use super::{
    operand::convert_operand,
    place::{
        emit_instructions_to_get_on_own, emit_instructions_to_set_value, get_place_type, make_jvm_safe,
        place_to_string,
    },
    types::{get_field_name_from_index, mir_int_to_oomir_const},
};
use crate::oomir;

use rustc_middle::{
    mir::{
        BasicBlock, BasicBlockData, Body, Local, Operand as MirOperand, Place, StatementKind,
        TerminatorKind,
    },
    ty::{Instance, TyCtxt},
};
use std::collections::HashMap;

mod checked_ops;
mod checked_intrinsic_registry;
pub mod checked_intrinsics;
mod rvalue;

pub use checked_intrinsic_registry::take_needed_intrinsics;

fn zero_constant_for_type(ty: &oomir::Type) -> Option<oomir::Constant> {
    match ty {
        oomir::Type::Boolean => Some(oomir::Constant::Boolean(false)),
        oomir::Type::Char => Some(oomir::Constant::Char('\0')),
        oomir::Type::I8 => Some(oomir::Constant::I8(0)),
        oomir::Type::I16 => Some(oomir::Constant::I16(0)),
        oomir::Type::I32 => Some(oomir::Constant::I32(0)),
        oomir::Type::I64 => Some(oomir::Constant::I64(0)),
        oomir::Type::F32 => Some(oomir::Constant::F32(0.0)),
        oomir::Type::F64 => Some(oomir::Constant::F64(0.0)),
        oomir::Type::Class(class_name) if class_name == crate::lower2::BIG_INTEGER_CLASS => {
            Some(oomir::Constant::Instance {
                class_name: class_name.clone(),
                fields: std::collections::HashMap::new(),
                params: vec![oomir::Constant::String("0".to_string())],
            })
        }
        _ => None,
    }
}

/// Convert a single MIR basic block into an OOMIR basic block.
pub fn convert_basic_block<'tcx>(
    bb: BasicBlock,
    bb_data: &BasicBlockData<'tcx>,
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    mir: &Body<'tcx>,
    return_oomir_type: &oomir::Type, // Pass function return type
    basic_blocks: &mut HashMap<String, oomir::BasicBlock>,
    data_types: &mut HashMap<String, oomir::DataType>,
) -> oomir::BasicBlock {
    // Use the basic block index as its label.
    let label = format!("bb{}", bb.index());
    let mut instructions = Vec::new();
    let mut mutable_borrow_arrays: HashMap<Local, (Place<'tcx>, String, oomir::Type)> =
        HashMap::new();

    // Convert each MIR statement in the block.
    for stmt in &bb_data.statements {
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                // 1. Evaluate the Rvalue to get the source operand and temp instructions
                let (rvalue_instructions, source_operand) = rvalue::convert_rvalue_to_operand(
                    // Call the refactored function
                    rvalue, place, // Pass original destination for temp naming hints
                    mir, tcx, instance, data_types,
                );

                // Add instructions needed to calculate the Rvalue
                instructions.extend(rvalue_instructions);

                if let rustc_middle::mir::Rvalue::Ref(
                    _,
                    rustc_middle::mir::BorrowKind::Mut { .. },
                    borrowed_place,
                ) = rvalue
                {
                    // Check if the destination is a simple local (most common case for &mut assignment)
                    if place.projection.is_empty() {
                        if let oomir::Operand::Variable {
                            name: array_var_name,
                            ty: array_ty,
                        } = &source_operand
                        {
                            // Extract element type from array type
                            if let oomir::Type::MutableReference(element_ty) = array_ty {
                                breadcrumbs::log!(
                                    breadcrumbs::LogLevel::Info,
                                    "mir-lowering",
                                    format!(
                                        "Info: Tracking mutable borrow array for place {:?} stored in local {:?}. Original: {:?}, ArrayVar: {}, ElementTy: {:?}",
                                        place,
                                        place.local,
                                        borrowed_place,
                                        array_var_name,
                                        element_ty
                                    )
                                );
                                mutable_borrow_arrays.insert(
                                    place.local, // The local holding the array reference (e.g., _3)
                                    (
                                        borrowed_place.clone(), // The original place borrowed (e.g., _1)
                                        array_var_name.clone(), // The OOMIR name of the array var (e.g., "3_tmp0")
                                        *element_ty.clone(), // The type of the element in the array
                                    ),
                                );
                            } else {
                                breadcrumbs::log!(
                                    breadcrumbs::LogLevel::Warn,
                                    "mir-lowering",
                                    format!(
                                        "Warning: Expected type for mutable borrow ref, found {:?}",
                                        array_ty
                                    )
                                );
                            }
                        } else {
                            breadcrumbs::log!(
                                breadcrumbs::LogLevel::Warn,
                                "mir-lowering",
                                format!(
                                    "Warning: Expected variable operand for mutable borrow ref assignment result, found {:?}",
                                    source_operand
                                )
                            );
                        }
                    } else {
                        breadcrumbs::log!(
                            breadcrumbs::LogLevel::Warn,
                            "mir-lowering",
                            format!(
                                "Warning: Mutable borrow assigned to complex place {:?}, write-back might not work correctly.",
                                place
                            )
                        );
                    }
                }

                // 2. Generate instructions to store the computed value into the destination place
                let assignment_instructions = emit_instructions_to_set_value(
                    place,          // The actual destination Place
                    source_operand, // The OOMIR operand holding the value from the Rvalue
                    tcx,
                    instance,
                    mir,
                    data_types,
                );

                // Add the final assignment instructions (Move, SetField, ArrayStore)
                instructions.extend(assignment_instructions);
            }
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Retag(_, _) => {
                // no-op, currently
            }
            StatementKind::Nop => {
                // Literally a no-op
            }
            StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => {
                breadcrumbs::log!(
                    breadcrumbs::LogLevel::Warn,
                    "mir-lowering",
                    format!(
                        "Warning: StatementKind::SetDiscriminant NYI. Place: {:?}, Index: {:?}",
                        place, variant_index
                    )
                );
                // TODO: Need logic similar to emit_instructions_to_set_value but for discriminants
            }
            // Handle other StatementKind variants if necessary
            _ => {
                breadcrumbs::log!(
                    breadcrumbs::LogLevel::Warn,
                    "mir-lowering",
                    format!("Warning: Unhandled StatementKind: {:?}", stmt.kind)
                );
            }
        }
    }

    // Convert the MIR terminator into corresponding OOMIR instructions.
    if let Some(terminator) = &bb_data.terminator {
        match &terminator.kind {
            TerminatorKind::Return => {
                // Handle Return without operand
                if *return_oomir_type == oomir::Type::Void {
                    instructions.push(oomir::Instruction::Return { operand: None });
                } else {
                    let return_operand = convert_operand(
                        &MirOperand::Move(Place::return_place()),
                        tcx,
                        instance,
                        mir,
                        data_types,
                        &mut instructions,
                    );
                    instructions.push(oomir::Instruction::Return {
                        operand: Some(return_operand),
                    });
                }
            }
            TerminatorKind::Goto { target } => {
                let target_label = format!("bb{}", target.index());
                instructions.push(oomir::Instruction::Jump {
                    target: target_label,
                });
            }
            TerminatorKind::SwitchInt { discr, targets, .. } => {
                // --- GENERAL SwitchInt Handling ---
                let discr_operand =
                    convert_operand(discr, tcx, instance, mir, data_types, &mut instructions);
                // Get the actual type of the discriminant from MIR local declarations
                let discr_ty = discr.ty(&mir.local_decls, tcx);

                // Convert the MIR targets into OOMIR (Constant, Label) pairs
                let oomir_targets: Vec<(oomir::Constant, String)> = targets
                    .iter()
                    .map(|(value, target_bb)| {
                        // Convert MIR value (u128) to appropriate OOMIR constant based on discr_ty
                        let oomir_const = mir_int_to_oomir_const(value, discr_ty, tcx); // Use helper
                        // Check if the constant type is suitable for a JVM switch
                    if !oomir_const.is_integer_like() {
                        breadcrumbs::log!(breadcrumbs::LogLevel::Warn, "mir-lowering", format!("Warning: SwitchInt target value {:?} for type {:?} cannot be directly used in JVM switch. Block: {}", oomir_const, discr_ty, label));
                             // Decide on fallback: error, skip target, default value?
                             // For now, let's potentially create an invalid switch target for lower2 to handle/error on.
                        }
                        let target_label = format!("bb{}", target_bb.index());
                        (oomir_const, target_label)
                    })
                    .collect();

                // Get the label for the 'otherwise' block
                let otherwise_label = format!("bb{}", targets.otherwise().index());

                // Add the single OOMIR Switch instruction
                instructions.push(oomir::Instruction::Switch {
                    discr: discr_operand,
                    targets: oomir_targets,
                    otherwise: otherwise_label,
                });
                // This Switch instruction terminates the current OOMIR basic block.
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                breadcrumbs::log!(
                    breadcrumbs::LogLevel::Info,
                    "mir-lowering",
                    format!("the function name is {:?}", func)
                );

                if let rustc_middle::mir::Operand::Constant(box c) = func {
                    let fn_ty = c.const_.ty();
                    if let rustc_middle::ty::TyKind::FnDef(def_id, _) = fn_ty.kind() {
                        let def_path = tcx.def_path_str(*def_id);
                        if def_path.ends_with("avxneconvert::cvtneeph2ps_256") {
                            breadcrumbs::log!(
                                breadcrumbs::LogLevel::Warn,
                                "mir-lowering",
                                format!(
                                    "Inlining placeholder lowering for foreign intrinsic {}",
                                    def_path
                                )
                            );

                            if args.len() != 1 {
                                panic!(
                                    "cvtneeph2ps_256 expected 1 arg, got {} for {}",
                                    args.len(),
                                    def_path
                                );
                            }

                            let source_operand = convert_operand(
                                &args[0].node,
                                tcx,
                                instance,
                                mir,
                                data_types,
                                &mut instructions,
                            );
                            let result_ty =
                                get_place_type(destination, mir, tcx, instance, data_types);
                            let temp_dest =
                                format!("{}_cvtneeph2ps_256_{}", place_to_string(destination, tcx), bb.index());

                            let lowered_operand =
                                if source_operand.get_type() == Some(result_ty.clone()) {
                                    source_operand
                                } else {
                                    instructions.push(oomir::Instruction::Cast {
                                        op: source_operand,
                                        ty: result_ty.clone(),
                                        dest: temp_dest.clone(),
                                    });
                                    oomir::Operand::Variable {
                                        name: temp_dest,
                                        ty: result_ty.clone(),
                                    }
                                };

                            let set_instrs = emit_instructions_to_set_value(
                                destination,
                                lowered_operand,
                                tcx,
                                instance,
                                mir,
                                data_types,
                            );
                            instructions.extend(set_instrs);

                            if let Some(target_bb) = target {
                                instructions.push(oomir::Instruction::Jump {
                                    target: format!("bb{}", target_bb.index()),
                                });
                            }

                            return oomir::BasicBlock {
                                label,
                                instructions,
                            };
                        }

                        if def_path.ends_with("avx512f::vcvttpd2udq256") {
                            breadcrumbs::log!(
                                breadcrumbs::LogLevel::Warn,
                                "mir-lowering",
                                format!(
                                    "Inlining placeholder lowering for foreign intrinsic {}",
                                    def_path
                                )
                            );

                            if args.len() != 3 {
                                panic!(
                                    "vcvttpd2udq256 expected 3 args, got {} for {}",
                                    args.len(),
                                    def_path
                                );
                            }

                            let source_operand = convert_operand(
                                &args[1].node,
                                tcx,
                                instance,
                                mir,
                                data_types,
                                &mut instructions,
                            );
                            let result_ty =
                                get_place_type(destination, mir, tcx, instance, data_types);
                            let temp_dest =
                                format!("{}_vcvttpd2udq256_{}", place_to_string(destination, tcx), bb.index());

                            let lowered_operand = if source_operand.get_type() == Some(result_ty.clone()) {
                                source_operand
                            } else {
                                instructions.push(oomir::Instruction::Cast {
                                    op: source_operand,
                                    ty: result_ty.clone(),
                                    dest: temp_dest.clone(),
                                });
                                oomir::Operand::Variable {
                                    name: temp_dest,
                                    ty: result_ty.clone(),
                                }
                            };

                            let set_instrs = emit_instructions_to_set_value(
                                destination,
                                lowered_operand,
                                tcx,
                                instance,
                                mir,
                                data_types,
                            );
                            instructions.extend(set_instrs);

                            if let Some(target_bb) = target {
                                instructions.push(oomir::Instruction::Jump {
                                    target: format!("bb{}", target_bb.index()),
                                });
                            }

                            return oomir::BasicBlock {
                                label,
                                instructions,
                            };
                        }

                        if def_path.ends_with("intrinsics::simd::simd_insert")
                            || def_path.ends_with("intrinsics::simd::simd_insert_dyn")
                        {
                            breadcrumbs::log!(
                                breadcrumbs::LogLevel::Info,
                                "mir-lowering",
                                format!("Inlining SIMD insert intrinsic {}", def_path)
                            );

                            if args.len() != 3 {
                                panic!(
                                    "SIMD insert intrinsic expected 3 args, got {} for {}",
                                    args.len(),
                                    def_path
                                );
                            }

                            let vector_operand = convert_operand(
                                &args[0].node,
                                tcx,
                                instance,
                                mir,
                                data_types,
                                &mut instructions,
                            );
                            let index_operand = convert_operand(
                                &args[1].node,
                                tcx,
                                instance,
                                mir,
                                data_types,
                                &mut instructions,
                            );
                            let value_operand = convert_operand(
                                &args[2].node,
                                tcx,
                                instance,
                                mir,
                                data_types,
                                &mut instructions,
                            );

                            let vector_class_name = match vector_operand.get_type() {
                                Some(oomir::Type::Class(name)) => name,
                                Some(oomir::Type::Reference(box oomir::Type::Class(name))) => name,
                                Some(oomir::Type::MutableReference(box oomir::Type::Class(name))) => {
                                    name
                                }
                                other => panic!(
                                    "SIMD insert expected class-like vector operand, got {:?}",
                                    other
                                ),
                            };

                            let (lane_field_name, lane_array_ty) = match data_types
                                .get(&vector_class_name)
                            {
                                Some(oomir::DataType::Class { fields, .. }) => {
                                    let field_name = get_field_name_from_index(
                                        &vector_class_name,
                                        0,
                                        data_types,
                                    )
                                    .unwrap_or_else(|e| {
                                        panic!(
                                            "SIMD insert could not resolve lane field for {}: {}",
                                            vector_class_name, e
                                        )
                                    });
                                    let field_ty = fields
                                        .first()
                                        .map(|(_, ty)| ty.clone())
                                        .unwrap_or_else(|| {
                                            panic!(
                                                "SIMD insert found no fields on vector class {}",
                                                vector_class_name
                                            )
                                        });
                                    (field_name, field_ty)
                                }
                                other => panic!(
                                    "SIMD insert expected registered class metadata for {}, got {:?}",
                                    vector_class_name, other
                                ),
                            };

                            let lane_array_var = format!(
                                "{}_simd_lanes_{}",
                                place_to_string(destination, tcx),
                                bb.index()
                            );
                            instructions.push(oomir::Instruction::GetField {
                                dest: lane_array_var.clone(),
                                object: vector_operand.clone(),
                                field_name: lane_field_name,
                                field_ty: lane_array_ty.clone(),
                                owner_class: vector_class_name,
                            });
                            instructions.push(oomir::Instruction::ArrayStore {
                                array: lane_array_var,
                                index: index_operand,
                                value: value_operand,
                            });

                            let set_instrs = emit_instructions_to_set_value(
                                destination,
                                vector_operand,
                                tcx,
                                instance,
                                mir,
                                data_types,
                            );
                            instructions.extend(set_instrs);

                            if let Some(target_bb) = target {
                                instructions.push(oomir::Instruction::Jump {
                                    target: format!("bb{}", target_bb.index()),
                                });
                            }

                            return oomir::BasicBlock {
                                label,
                                instructions,
                            };
                        }

                        if def_path.ends_with("intrinsics::simd::simd_select_bitmask") {
                            breadcrumbs::log!(
                                breadcrumbs::LogLevel::Warn,
                                "mir-lowering",
                                format!(
                                    "Inlining placeholder SIMD select bitmask intrinsic {}",
                                    def_path
                                )
                            );

                            if args.len() != 3 {
                                panic!(
                                    "SIMD select bitmask intrinsic expected 3 args, got {} for {}",
                                    args.len(),
                                    def_path
                                );
                            }

                            let mask_operand = convert_operand(
                                &args[0].node,
                                tcx,
                                instance,
                                mir,
                                data_types,
                                &mut instructions,
                            );
                            let on_operand = convert_operand(
                                &args[1].node,
                                tcx,
                                instance,
                                mir,
                                data_types,
                                &mut instructions,
                            );
                            let off_operand = convert_operand(
                                &args[2].node,
                                tcx,
                                instance,
                                mir,
                                data_types,
                                &mut instructions,
                            );

                            let result_ty =
                                get_place_type(destination, mir, tcx, instance, data_types);
                            let mask_ty = mask_operand.get_type().unwrap_or_else(|| {
                                panic!(
                                    "SIMD select bitmask mask operand had no type for {}",
                                    def_path
                                )
                            });
                            let zero_mask = zero_constant_for_type(&mask_ty).unwrap_or_else(|| {
                                panic!(
                                    "SIMD select bitmask does not support mask type {:?} for {}",
                                    mask_ty, def_path
                                )
                            });

                            let normalize_branch_operand =
                                |instructions: &mut Vec<oomir::Instruction>,
                                 operand: oomir::Operand,
                                 suffix: &str| {
                                    if operand.get_type() == Some(result_ty.clone()) {
                                        operand
                                    } else {
                                        let cast_dest = format!(
                                            "{}_simd_select_bitmask_{}_{}_{}",
                                            place_to_string(destination, tcx),
                                            bb.index(),
                                            suffix,
                                            make_jvm_safe(&def_path)
                                        );
                                        instructions.push(oomir::Instruction::Cast {
                                            op: operand,
                                            ty: result_ty.clone(),
                                            dest: cast_dest.clone(),
                                        });
                                        oomir::Operand::Variable {
                                            name: cast_dest,
                                            ty: result_ty.clone(),
                                        }
                                    }
                                };

                            let on_operand =
                                normalize_branch_operand(&mut instructions, on_operand, "on");
                            let off_operand =
                                normalize_branch_operand(&mut instructions, off_operand, "off");

                            let cond_var = format!(
                                "{}_simd_select_bitmask_nonzero_{}",
                                place_to_string(destination, tcx),
                                bb.index()
                            );
                            let true_label = format!(
                                "{}_simd_select_bitmask_true_{}",
                                place_to_string(destination, tcx),
                                bb.index()
                            );
                            let false_label = format!(
                                "{}_simd_select_bitmask_false_{}",
                                place_to_string(destination, tcx),
                                bb.index()
                            );
                            let end_label = format!(
                                "{}_simd_select_bitmask_end_{}",
                                place_to_string(destination, tcx),
                                bb.index()
                            );
                            let result_var = format!(
                                "{}_simd_select_bitmask_{}",
                                place_to_string(destination, tcx),
                                bb.index()
                            );

                            instructions.push(oomir::Instruction::Ne {
                                dest: cond_var.clone(),
                                op1: mask_operand,
                                op2: oomir::Operand::Constant(zero_mask),
                            });
                            instructions.push(oomir::Instruction::Branch {
                                condition: oomir::Operand::Variable {
                                    name: cond_var,
                                    ty: oomir::Type::Boolean,
                                },
                                true_block: true_label.clone(),
                                false_block: false_label.clone(),
                            });

                            instructions.push(oomir::Instruction::Label { name: true_label });
                            instructions.push(oomir::Instruction::Move {
                                dest: result_var.clone(),
                                src: on_operand,
                            });
                            instructions.push(oomir::Instruction::Jump {
                                target: end_label.clone(),
                            });

                            instructions.push(oomir::Instruction::Label { name: false_label });
                            instructions.push(oomir::Instruction::Move {
                                dest: result_var.clone(),
                                src: off_operand,
                            });
                            instructions.push(oomir::Instruction::Jump {
                                target: end_label.clone(),
                            });

                            instructions.push(oomir::Instruction::Label { name: end_label });
                            instructions.extend(emit_instructions_to_set_value(
                                destination,
                                oomir::Operand::Variable {
                                    name: result_var,
                                    ty: result_ty.clone(),
                                },
                                tcx,
                                instance,
                                mir,
                                data_types,
                            ));

                            if let Some(target_bb) = target {
                                instructions.push(oomir::Instruction::Jump {
                                    target: format!("bb{}", target_bb.index()),
                                });
                            }

                            return oomir::BasicBlock {
                                label,
                                instructions,
                            };
                        }

                        if def_path.ends_with("intrinsics::simd::simd_select") {
                            breadcrumbs::log!(
                                breadcrumbs::LogLevel::Warn,
                                "mir-lowering",
                                format!("Inlining placeholder SIMD select intrinsic {}", def_path)
                            );

                            if args.len() != 3 {
                                panic!(
                                    "SIMD select intrinsic expected 3 args, got {} for {}",
                                    args.len(),
                                    def_path
                                );
                            }

                            let selected_operand = convert_operand(
                                &args[1].node,
                                tcx,
                                instance,
                                mir,
                                data_types,
                                &mut instructions,
                            );
                            let result_ty =
                                get_place_type(destination, mir, tcx, instance, data_types);
                            let temp_dest = format!(
                                "{}_simd_select_{}",
                                place_to_string(destination, tcx),
                                bb.index()
                            );

                            let lowered_operand =
                                if selected_operand.get_type() == Some(result_ty.clone()) {
                                    selected_operand
                                } else {
                                    instructions.push(oomir::Instruction::Cast {
                                        op: selected_operand,
                                        ty: result_ty.clone(),
                                        dest: temp_dest.clone(),
                                    });
                                    oomir::Operand::Variable {
                                        name: temp_dest,
                                        ty: result_ty.clone(),
                                    }
                                };

                            instructions.extend(emit_instructions_to_set_value(
                                destination,
                                lowered_operand,
                                tcx,
                                instance,
                                mir,
                                data_types,
                            ));

                            if let Some(target_bb) = target {
                                instructions.push(oomir::Instruction::Jump {
                                    target: format!("bb{}", target_bb.index()),
                                });
                            }

                            return oomir::BasicBlock {
                                label,
                                instructions,
                            };
                        }

                        if def_path.ends_with("intrinsics::simd::simd_eq")
                            || def_path.ends_with("intrinsics::simd::simd_ne")
                            || def_path.ends_with("intrinsics::simd::simd_lt")
                            || def_path.ends_with("intrinsics::simd::simd_le")
                            || def_path.ends_with("intrinsics::simd::simd_gt")
                            || def_path.ends_with("intrinsics::simd::simd_ge")
                        {
                            breadcrumbs::log!(
                                breadcrumbs::LogLevel::Warn,
                                "mir-lowering",
                                format!(
                                    "Inlining placeholder SIMD comparison intrinsic {}",
                                    def_path
                                )
                            );

                            if args.len() != 2 {
                                panic!(
                                    "SIMD comparison intrinsic expected 2 args, got {} for {}",
                                    args.len(),
                                    def_path
                                );
                            }

                            let lhs_operand = convert_operand(
                                &args[0].node,
                                tcx,
                                instance,
                                mir,
                                data_types,
                                &mut instructions,
                            );
                            let result_ty =
                                get_place_type(destination, mir, tcx, instance, data_types);
                            let temp_dest = format!(
                                "{}_simd_cmp_{}",
                                place_to_string(destination, tcx),
                                bb.index()
                            );

                            let lowered_operand = if lhs_operand.get_type() == Some(result_ty.clone()) {
                                lhs_operand
                            } else {
                                instructions.push(oomir::Instruction::Cast {
                                    op: lhs_operand,
                                    ty: result_ty.clone(),
                                    dest: temp_dest.clone(),
                                });
                                oomir::Operand::Variable {
                                    name: temp_dest,
                                    ty: result_ty.clone(),
                                }
                            };

                            instructions.extend(emit_instructions_to_set_value(
                                destination,
                                lowered_operand,
                                tcx,
                                instance,
                                mir,
                                data_types,
                            ));

                            if let Some(target_bb) = target {
                                instructions.push(oomir::Instruction::Jump {
                                    target: format!("bb{}", target_bb.index()),
                                });
                            }

                            return oomir::BasicBlock {
                                label,
                                instructions,
                            };
                        }

                        if def_path.ends_with("intrinsics::simd::simd_extract")
                            || def_path.ends_with("intrinsics::simd::simd_extract_dyn")
                        {
                            breadcrumbs::log!(
                                breadcrumbs::LogLevel::Info,
                                "mir-lowering",
                                format!("Inlining SIMD extract intrinsic {}", def_path)
                            );

                            if args.len() != 2 {
                                panic!(
                                    "SIMD extract intrinsic expected 2 args, got {} for {}",
                                    args.len(),
                                    def_path
                                );
                            }

                            let vector_operand = convert_operand(
                                &args[0].node,
                                tcx,
                                instance,
                                mir,
                                data_types,
                                &mut instructions,
                            );
                            let index_operand = convert_operand(
                                &args[1].node,
                                tcx,
                                instance,
                                mir,
                                data_types,
                                &mut instructions,
                            );

                            let vector_class_name = match vector_operand.get_type() {
                                Some(oomir::Type::Class(name)) => name,
                                Some(oomir::Type::Reference(box oomir::Type::Class(name))) => name,
                                Some(oomir::Type::MutableReference(box oomir::Type::Class(name))) => {
                                    name
                                }
                                other => panic!(
                                    "SIMD extract expected class-like vector operand, got {:?}",
                                    other
                                ),
                            };

                            let (lane_field_name, lane_array_ty) = match data_types
                                .get(&vector_class_name)
                            {
                                Some(oomir::DataType::Class { fields, .. }) => {
                                    let field_name = get_field_name_from_index(
                                        &vector_class_name,
                                        0,
                                        data_types,
                                    )
                                    .unwrap_or_else(|e| {
                                        panic!(
                                            "SIMD extract could not resolve lane field for {}: {}",
                                            vector_class_name, e
                                        )
                                    });
                                    let field_ty = fields
                                        .first()
                                        .map(|(_, ty)| ty.clone())
                                        .unwrap_or_else(|| {
                                            panic!(
                                                "SIMD extract found no fields on vector class {}",
                                                vector_class_name
                                            )
                                        });
                                    (field_name, field_ty)
                                }
                                other => panic!(
                                    "SIMD extract expected registered class metadata for {}, got {:?}",
                                    vector_class_name, other
                                ),
                            };

                            let lane_array_var = format!(
                                "{}_simd_lanes_{}",
                                place_to_string(destination, tcx),
                                bb.index()
                            );
                            instructions.push(oomir::Instruction::GetField {
                                dest: lane_array_var.clone(),
                                object: vector_operand,
                                field_name: lane_field_name,
                                field_ty: lane_array_ty.clone(),
                                owner_class: vector_class_name,
                            });

                            let result_ty = get_place_type(destination, mir, tcx, instance, data_types);
                            let result_var = if destination.projection.is_empty() {
                                place_to_string(destination, tcx)
                            } else {
                                format!("{}_simd_extract_{}", place_to_string(destination, tcx), bb.index())
                            };

                            instructions.push(oomir::Instruction::ArrayGet {
                                dest: result_var.clone(),
                                array: oomir::Operand::Variable {
                                    name: lane_array_var,
                                    ty: lane_array_ty,
                                },
                                index: index_operand,
                            });

                            if !destination.projection.is_empty() {
                                let set_instrs = emit_instructions_to_set_value(
                                    destination,
                                    oomir::Operand::Variable {
                                        name: result_var,
                                        ty: result_ty.clone(),
                                    },
                                    tcx,
                                    instance,
                                    mir,
                                    data_types,
                                );
                                instructions.extend(set_instrs);
                            }

                            if let Some(target_bb) = target {
                                instructions.push(oomir::Instruction::Jump {
                                    target: format!("bb{}", target_bb.index()),
                                });
                            }

                            return oomir::BasicBlock {
                                label,
                                instructions,
                            };
                        }
                    }
                }

                let special_simd_function_name =
                    if let rustc_middle::mir::Operand::Constant(box c) = func {
                        let fn_ty = c.const_.ty();
                        if let rustc_middle::ty::TyKind::FnDef(def_id, _) = fn_ty.kind() {
                            let def_path = tcx.def_path_str(*def_id);
                            let method_name = if def_path.ends_with("intrinsics::simd::simd_and")
                            {
                                Some("bitand")
                            } else if def_path.ends_with("intrinsics::simd::simd_or") {
                                Some("bitor")
                            } else if def_path.ends_with("intrinsics::simd::simd_xor") {
                                Some("bitxor")
                            } else if def_path.ends_with("intrinsics::simd::simd_add") {
                                Some("add")
                            } else if def_path.ends_with("intrinsics::simd::simd_sub") {
                                Some("sub")
                            } else if def_path.ends_with("intrinsics::simd::simd_mul") {
                                Some("mul")
                            } else if def_path.ends_with("intrinsics::simd::simd_div") {
                                Some("div")
                            } else if def_path.ends_with("intrinsics::simd::simd_rem") {
                                Some("rem")
                            } else if def_path.ends_with("intrinsics::simd::simd_shl") {
                                Some("shl")
                            } else if def_path.ends_with("intrinsics::simd::simd_shr") {
                                Some("shr")
                            } else {
                                None
                            };

                            method_name.and_then(|method_name| {
                                let simd_ty = args.first()?.node.ty(&mir.local_decls, tcx);
                                let simd_oomir_ty = super::types::ty_to_oomir_type(
                                    simd_ty,
                                    tcx,
                                    &mut Default::default(),
                                    instance,
                                );
                                let class_name = match simd_oomir_ty {
                                    oomir::Type::Class(name) => name,
                                    oomir::Type::Reference(box oomir::Type::Class(name)) => name,
                                    oomir::Type::MutableReference(box oomir::Type::Class(name)) => {
                                        name
                                    }
                                    _ => return None,
                                };
                                Some(format!("{}_{}", class_name, method_name))
                            })
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                // Try to detect if this is a closure call
                let (function_name, is_closure_call) = if let Some(function_name) =
                    special_simd_function_name
                {
                    (function_name, false)
                } else if let Some(closure_info) =
                    super::closures::extract_closure_info(func, tcx)
                {
                    // This is a closure call - generate the proper closure function name
                    (
                        super::closures::generate_closure_function_name(
                            tcx,
                            closure_info.closure_def_id,
                        ),
                        true,
                    )
                } else {
                    // Regular function or generic instantiation
                    if let rustc_middle::mir::Operand::Constant(box c) = func {
                        let fn_ty = c.const_.ty();
                        if let rustc_middle::ty::TyKind::FnDef(def_id, args) = fn_ty.kind() {
                            breadcrumbs::log!(
                                breadcrumbs::LogLevel::Info,
                                "mir-lowering",
                                format!(
                                    "FnDef detected: def_id={:?}, is_local={}, args={:?}",
                                    def_id,
                                    def_id.is_local(),
                                    args
                                )
                            );
                            if def_id.is_local() {
                                // Check if this is a trait method call
                                if let Some(assoc_item) = tcx.opt_associated_item(*def_id) {
                                    breadcrumbs::log!(
                                        breadcrumbs::LogLevel::Info,
                                        "mir-lowering",
                                        format!(
                                            "Associated item found: {:?}, trait_item_def_id={:?}, container={:?}",
                                            assoc_item,
                                            assoc_item.trait_item_def_id(),
                                            assoc_item.container
                                        )
                                    );
                                    // Check if this is a trait method (check if parent is a trait)
                                    let is_trait_method = tcx.is_trait(tcx.parent(*def_id));

                                    if is_trait_method {
                                        // Trait method call: check if it's monomorphized to a concrete type
                                        if let Some(first_arg) = args.get(0) {
                                            if let Some(ty) = first_arg.as_type() {
                                                // Check if it's NOT a trait object (dyn Trait)
                                                if !matches!(
                                                    ty.kind(),
                                                    rustc_middle::ty::TyKind::Dynamic(..)
                                                ) {
                                                    // Concrete type - use Type_method naming
                                                    let type_name = super::types::ty_to_oomir_type(
                                                        ty,
                                                        tcx,
                                                        &mut Default::default(),
                                                        instance,
                                                    );
                                                    let method_name =
                                                        tcx.item_name(*def_id).to_string();
                                                    // Extract class name from Type
                                                    let class_name = match type_name {
                                                        oomir::Type::Class(name) => name,
                                                        oomir::Type::Reference(
                                                            box oomir::Type::Class(name),
                                                        ) => name,
                                                        oomir::Type::MutableReference(
                                                            box oomir::Type::Class(name),
                                                        ) => name,
                                                        _ => {
                                                            // Fallback for unexpected types
                                                            format!("{:?}", type_name)
                                                        }
                                                    };
                                                    let full_name =
                                                        format!("{}_{}", class_name, method_name);
                                                    breadcrumbs::log!(
                                                        breadcrumbs::LogLevel::Info,
                                                        "mir-lowering",
                                                        format!(
                                                            "Trait method call with concrete type: def_id={:?}, ty={:?}, using name: {}",
                                                            def_id, ty, full_name
                                                        )
                                                    );
                                                    (full_name, false)
                                                } else {
                                                    // Dynamic trait object - use dyn_Trait_method naming
                                                    let trait_name =
                                                        if let rustc_middle::ty::TyKind::Dynamic(
                                                            preds,
                                                            _,
                                                        ) = ty.kind()
                                                        {
                                                            // Extract trait name from trait object
                                                            if let Some(principal) =
                                                                preds.principal()
                                                            {
                                                                let trait_ref =
                                                                    principal.skip_binder();
                                                                tcx.item_name(trait_ref.def_id)
                                                                    .to_string()
                                                            } else {
                                                                "Unknown".to_string()
                                                            }
                                                        } else {
                                                            "Unknown".to_string()
                                                        };
                                                    let method_name =
                                                        tcx.item_name(*def_id).to_string();
                                                    let full_name = format!(
                                                        "dyn_{}_{}",
                                                        trait_name, method_name
                                                    );
                                                    breadcrumbs::log!(
                                                        breadcrumbs::LogLevel::Info,
                                                        "mir-lowering",
                                                        format!(
                                                            "Trait method call with dyn trait object, using name: {}",
                                                            full_name
                                                        )
                                                    );
                                                    (full_name, false)
                                                }
                                            } else {
                                                // No type in args, use monomorphized name
                                                (
                                                    super::naming::mono_fn_name_from_call_operand(
                                                        func, tcx, instance,
                                                    )
                                                    .unwrap(),
                                                    false,
                                                )
                                            }
                                        } else {
                                            // No args, use monomorphized name
                                            (
                                                super::naming::mono_fn_name_from_call_operand(
                                                    func, tcx, instance,
                                                )
                                                .unwrap(),
                                                false,
                                            )
                                        }
                                    } else {
                                        // Not a trait method, use monomorphized name
                                        (
                                            super::naming::mono_fn_name_from_call_operand(
                                                func, tcx, instance,
                                            )
                                            .unwrap(),
                                            false,
                                        )
                                    }
                                } else {
                                    // Not an associated item, use monomorphized name
                                    (
                                        super::naming::mono_fn_name_from_call_operand(
                                            func, tcx, instance,
                                        )
                                        .unwrap(),
                                        false,
                                    )
                                }
                            } else {
                                // External function: check for special cases, otherwise use path-based key for shims
                                let def_path = tcx.def_path_str(*def_id);

                                // Special case: core::str::<impl str>::len maps to our Kotlin shim's len method
                                if def_path.contains("::str::") && def_path.ends_with("::len") {
                                    ("len".to_string(), false)
                                } else {
                                    (make_jvm_safe(format!("{:?}", func).as_str()), false)
                                }
                            }
                        } else {
                            (make_jvm_safe(format!("{:?}", func).as_str()), false)
                        }
                    } else {
                        (make_jvm_safe(format!("{:?}", func).as_str()), false)
                    }
                };

                // --- Track Argument Origins ---
                // Store tuples: (Maybe Original MIR Place of Arg, OOMIR Operand for Arg)
                let mut processed_args: Vec<(Option<Place<'tcx>>, oomir::Operand)> = Vec::new();
                let mut pre_call_instructions = Vec::new(); // Instructions needed *before* the call for args

                // For closure calls, skip the first argument (the closure itself)
                // The MIR representation of closure.call((args)) is Fn::call(&closure, (args))
                // We only want to pass (args) to the lowered closure function
                let args_to_process = if is_closure_call && !args.is_empty() {
                    &args[1..] // Skip the first argument (the closure reference)
                } else {
                    args
                };

                for arg in args_to_process {
                    let mir_op = &arg.node;
                    // Important: Pass pre_call_instructions here to collect setup code for this arg
                    let oomir_op = convert_operand(
                        mir_op,
                        tcx,
                        instance,
                        mir,
                        data_types,
                        &mut pre_call_instructions,
                    );

                    // Identify if the MIR operand is a direct use of a local Place
                    let maybe_arg_place = match mir_op {
                        MirOperand::Move(p) | MirOperand::Copy(p) if p.projection.is_empty() => {
                            Some(p.clone())
                        }
                        _ => None,
                    };
                    processed_args.push((maybe_arg_place, oomir_op));
                }
                // Add instructions needed to prepare arguments *before* the call
                instructions.extend(pre_call_instructions);

                // Collect just the OOMIR operands for the call itself
                let oomir_args: Vec<oomir::Operand> =
                    processed_args.iter().map(|(_, op)| op.clone()).collect();

                // Determine destination OOMIR variable name (if any)
                let dest_var_name = destination.projection.is_empty()
                    .then(|| format!("_{}", destination.local.index()))
                    .or_else(|| {
                         breadcrumbs::log!(breadcrumbs::LogLevel::Warn, "mir-lowering", format!("Warning: Call destination {:?} is complex, return value might be lost.", destination));
                         None // Handle complex destinations if needed later
                    });

                // --- Emit the Call Instruction ---
                instructions.push(oomir::Instruction::Call {
                    dest: dest_var_name,
                    function: function_name,
                    args: oomir_args,
                });

                let mut write_back_instrs = Vec::new();
                for (maybe_arg_place, oomir_arg_operand) in &processed_args {
                    if let Some(arg_place) = maybe_arg_place {
                        // Check if the local used for this argument is one we tracked as a mutable borrow array
                        if let Some((original_place, array_var_name, element_ty)) =
                            mutable_borrow_arrays.get(&arg_place.local)
                        {
                            // Double-check if the operand passed was indeed the variable we expected
                            if let oomir::Operand::Variable { .. } = oomir_arg_operand {
                                breadcrumbs::log!(
                                    breadcrumbs::LogLevel::Info,
                                    "mir-lowering",
                                    format!(
                                        "Info: Emitting write-back for mutable borrow. Arg Place: {:?}, Original Place: {:?}, Array Var: {}",
                                        arg_place, original_place, array_var_name
                                    )
                                );

                                // Create a temporary variable for the value read from the array
                                let temp_writeback_var =
                                    format!("_writeback_{}", original_place.local.index());

                                // 1. Get value from array (using the tracked array_var_name)
                                let array_operand = oomir::Operand::Variable {
                                    name: array_var_name.clone(),
                                    // Reconstruct array type for clarity (though not strictly needed by ArrayGet)
                                    ty: oomir::Type::Array(Box::new(element_ty.clone())),
                                };
                                write_back_instrs.push(oomir::Instruction::ArrayGet {
                                    dest: temp_writeback_var.clone(),
                                    array: array_operand,
                                    index: oomir::Operand::Constant(oomir::Constant::I32(0)), // Always index 0
                                });

                                // 2. Set value back to original place
                                let value_to_set = oomir::Operand::Variable {
                                    name: temp_writeback_var,
                                    ty: element_ty.clone(), // Use the tracked element type
                                };
                                let set_instrs = emit_instructions_to_set_value(
                                    original_place, // The original Place (_1)
                                    value_to_set,   // The value read from the array
                                    tcx,
                                    instance,
                                    mir,
                                    data_types,
                                );
                                write_back_instrs.extend(set_instrs);
                            }
                        }
                    }
                }
                instructions.extend(write_back_instrs);

                // --- Add Jump to Target Block (if call returns) ---
                if let Some(target_bb) = target {
                    let target_label = format!("bb{}", target_bb.index());
                    breadcrumbs::log!(
                        breadcrumbs::LogLevel::Info,
                        "mir-lowering",
                        format!(
                            "Info: Adding Jump to {} after Call in bb{}",
                            target_label,
                            bb.index()
                        )
                    );
                    instructions.push(oomir::Instruction::Jump {
                        target: target_label,
                    });
                } else {
                    // Function diverges (e.g., panic!) - No jump needed.
                    breadcrumbs::log!(
                        breadcrumbs::LogLevel::Info,
                        "mir-lowering",
                        format!(
                            "Info: Call in bb{} has no return target (diverges).",
                            bb.index()
                        )
                    );
                }
            }
            TerminatorKind::Assert {
                target,
                cond,
                expected,
                msg,
                unwind: _,
            } => {
                let condition_operand: oomir::Operand;

                // Check if the condition operand is a direct use of a place (Copy or Move)
                let condition_place_opt = match cond {
                    MirOperand::Copy(place) | MirOperand::Move(place) => Some(place),
                    _ => None, // If it's a constant, handle directly
                };

                if let Some(place) = condition_place_opt {
                    // Now, check if this place has a field projection
                    let (temp_dest, instrs, field_oomir_type) =
                        emit_instructions_to_get_on_own(place, tcx, instance, mir, data_types);
                    instructions.extend(instrs);
                    // Use the temporary variable as the condition operand
                    condition_operand = oomir::Operand::Variable {
                        name: temp_dest.clone(),
                        ty: field_oomir_type,
                    };
                } else {
                    breadcrumbs::log!(
                        breadcrumbs::LogLevel::Info,
                        "mir-lowering",
                        format!("Info: Assert condition uses constant operand {:?}", cond)
                    );
                    // Condition is likely a constant itself
                    condition_operand =
                        convert_operand(cond, tcx, instance, mir, data_types, &mut instructions);
                }
                // --- End of condition operand handling ---

                // The MIR assert checks `!cond == expected`. Rust asserts check `cond == expected`.
                // Standard Rust `assert!(expr)` lowers to MIR `assert(expr, expected: true, ...)`
                // Standard Rust `assert_eq!(a,b)` might lower differently, but `assert!(a==b)` lowers like above.
                // The `checked_add` MIR uses `assert(!move (_7.1: bool), expected: true, ...)` effectively meaning "panic if _7.1 is true".
                // So, we need to check if `condition_operand == *expected`.

                // Generate a comparison instruction to check if the *actual condition value*
                // matches the expected boolean value.
                let comparison_dest = format!("assert_cmp_{}", bb.index()); // e.g., assert_cmp_3

                // Handle potential negation: MIR `assert(!cond)` means panic if `cond` is true.
                // MIR `assert(cond)` means panic if `cond` is false.
                // The `expected` field tells us what the non-panic value should be.
                // We want to branch to the failure block if `condition_operand != expected`.

                breadcrumbs::log!(
                    breadcrumbs::LogLevel::Info,
                    "mir-lowering",
                    format!(
                        "Info: Generating Assert comparison: '{}' = ({:?}) == {:?}",
                        comparison_dest, condition_operand, *expected
                    )
                );

                instructions.push(oomir::Instruction::Eq {
                    dest: comparison_dest.clone(),
                    op1: condition_operand, // Use the potentially GetField'd value
                    op2: oomir::Operand::Constant(oomir::Constant::Boolean(*expected)),
                });

                // Generate a branch based on the comparison result
                let success_block = format!("bb{}", target.index()); // Success path
                let failure_block = format!("assert_fail_{}", bb.index()); // Failure path label

                breadcrumbs::log!(
                    breadcrumbs::LogLevel::Info,
                    "mir-lowering",
                    format!(
                        "Info: Generating Assert branch: if '{}' == true goto {} else goto {}",
                        comparison_dest, success_block, failure_block
                    )
                );

                instructions.push(oomir::Instruction::Branch {
                    condition: oomir::Operand::Variable {
                        name: comparison_dest, // Use the result of the Eq comparison
                        ty: oomir::Type::Boolean,
                    },
                    true_block: success_block, // Jump here if condition == expected (assertion holds)
                    false_block: failure_block.clone(), // Jump here if assertion fails
                });

                // --- Add the failure block ---
                // Extract the message. msg is an AssertMessage.
                // We need to handle different kinds of AssertMessage.
                let panic_message = match &**msg {
                    rustc_middle::mir::AssertKind::BoundsCheck { len, index } => {
                        // TODO: More sophisticated message generation using len/index operands later
                        format!("BoundsCheck failed (len: {:?}, index: {:?})", len, index)
                    }
                    rustc_middle::mir::AssertKind::Overflow(op, l, r) => {
                        // TODO: Convert l and r operands to strings if possible later
                        format!("Overflow({:?}, {:?}, {:?})", op, l, r)
                    }
                    rustc_middle::mir::AssertKind::OverflowNeg(op) => {
                        format!("OverflowNeg({:?})", op)
                    }
                    rustc_middle::mir::AssertKind::DivisionByZero(op) => {
                        format!("DivisionByZero({:?})", op)
                    }
                    rustc_middle::mir::AssertKind::RemainderByZero(op) => {
                        format!("RemainderByZero({:?})", op)
                    }
                    rustc_middle::mir::AssertKind::ResumedAfterReturn(_) => {
                        "ResumedAfterReturn".to_string()
                    }
                    rustc_middle::mir::AssertKind::ResumedAfterPanic(_) => {
                        "ResumedAfterPanic".to_string()
                    }
                    rustc_middle::mir::AssertKind::MisalignedPointerDereference {
                        required,
                        found,
                    } => {
                        format!(
                            "MisalignedPointerDereference (required: {:?}, found: {:?})",
                            required, found
                        )
                    }
                    rustc_middle::mir::AssertKind::NullPointerDereference => {
                        "NullPointerDereference".to_string()
                    }
                    rustc_middle::mir::AssertKind::ResumedAfterDrop(_) => {
                        "ResumedAfterDrop".to_string()
                    }
                    rustc_middle::mir::AssertKind::InvalidEnumConstruction(_) => {
                        "InvalidEnumConstruction".to_string()
                    }
                };

                let fail_instructions = vec![oomir::Instruction::ThrowNewWithMessage {
                    exception_class: "java/lang/RuntimeException".to_string(), // Or ArithmeticException for overflows?
                    message: panic_message,
                }];
                breadcrumbs::log!(
                    breadcrumbs::LogLevel::Info,
                    "mir-lowering",
                    format!("Info: Creating failure block '{}'", failure_block)
                );
                basic_blocks.insert(
                    // Ensure 'basic_blocks' map is mutable and passed in
                    failure_block.clone(),
                    oomir::BasicBlock {
                        label: failure_block,
                        instructions: fail_instructions,
                    },
                );
            }
            TerminatorKind::Drop {
                place: dropped_place,
                target,
                unwind: _,
                replace: _,
                drop: _,
                async_fut: _,
            } => {
                // In simple cases (no custom Drop trait), a MIR drop often just signifies
                // the end of a scope before control flow continues.
                // We need to emit the jump to the target block.
                // We ignore unwind paths for now.
                // We also don't emit an explicit OOMIR 'drop' instruction yet,
                // as standard GC handles memory. If explicit resource cleanup (like file.close())
                // were needed, this would require much more complex handling (e.g., try-finally).

                breadcrumbs::log!(
                    breadcrumbs::LogLevel::Info,
                    "mir-lowering",
                    format!(
                        "Info: Handling Drop terminator for place {:?}. Jumping to target bb{}.",
                        place_to_string(dropped_place, tcx),
                        target.index()
                    )
                );

                let target_label = format!("bb{}", target.index());
                instructions.push(oomir::Instruction::Jump {
                    target: target_label,
                });
            }
            TerminatorKind::Unreachable => {
                instructions.push(oomir::Instruction::ThrowNewWithMessage {
                    exception_class: "java/lang/RuntimeException".to_string(),
                    message: "Unreachable code reached".to_string(),
                });
            }
            // Other terminator kinds (like Resume, etc.) will be added as needed.
            _ => {
                breadcrumbs::log!(
                    breadcrumbs::LogLevel::Warn,
                    "mir-lowering",
                    format!("Warning: Unhandled terminator {:?}", terminator.kind)
                );
            }
        }
    }

    oomir::BasicBlock {
        label,
        instructions,
    }
}
