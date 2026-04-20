# Core And Alloc Bringup Plan

## Current state

- `./build.py all` succeeds on `rustc 1.95.0-nightly (2026-01-30)`.
- The normal consumer flow is host-target Cargo using the generated [`config.toml`](../config.toml), with external calls routed through a Kotlin shim map embedded from [`shim-metadata-gen/core.json`](../shim-metadata-gen/core.json).
- Real upstream crate calls are not modeled yet. In [`src/lower1/control_flow.rs`](../src/lower1/control_flow.rs), calls outside the local crate are reduced to shim lookup keys; in [`src/lower2/translator.rs`](../src/lower2/translator.rs), non-shim fallback only emits `invokestatic` into `module.name`, which is the current crate's class set.

## Goal split

1. Compile real `core` for `jvm-unknown-unknown`.
2. Compile real `alloc` on top of that.
3. Only after those two are stable, start `std`.

This ordering matters because `std` will otherwise hide whether failures come from sysroot bringup, allocator ABI, or host/runtime assumptions.

## Probe crate

[`probes/core_alloc_probe`](../probes/core_alloc_probe) is an external consumer crate with its own `.cargo/config.toml`.

- `host_core` validates the existing host-target backend path still works for an external crate.
- `jvm_no_std` is the first real-`core` compile probe.
- `jvm_alloc` is the first real-`alloc` compile probe with an explicit local allocator surface.

## Progress so far

- Added the external probe crate and wired it to the generated backend configuration.
- Confirmed the old host-target path still has a real upstream-call gap: external `core` functions are not yet treated as first-class cross-crate calls.
- Moved the custom target past the frontend ABI-lowering ICE by reporting a supported 32-bit `arch` in the target template while keeping the JVM linker/backend flow.
- Fixed three backend issues that blocked early sysroot bringup:
  - direct MIR reads now use `instance_mir`
  - pointer-sized integer constants no longer assume 64-bit width
  - impl-item scanning now skips associated consts and other non-function impl items
- Fixed several newer sysroot-lowering crashes in the backend:
  - `f128` constants no longer panic on `INFINITY`, `NEG_INFINITY`, or `NAN`; they lower to bringup-only `BigDecimal` sentinels instead
  - trait-item scanning now skips associated types and consts instead of assuming every trait item is a function
  - trait wrapper generation no longer assumes a first argument exists for every method helper
  - scalar-backed transparent wrappers now unwrap recursively during constant lowering, including `NonZero*`-style nested wrappers
  - zero-field scalar wrapper constants now degrade to empty constant instances instead of aborting
  - type lowering now uses fallible normalization and preserves unresolved aliases instead of crashing immediately on projection types
- Removed the old `ScalarInt` width mismatch crash and a related class of premature sysroot lowering attempts:
  - raw pointers and function pointers now erase to bringup-only `null` constants instead of integer stand-ins
  - function-pointer-like Rust types map to `java/lang/Object` during JVM bringup
  - direct lowering now skips foreign items, generic/alias-bearing instances, generic traits, traits with associated items, and other discovered instances that still need special handling
- Fixed another group of real-`core` lowering failures in MIR and call lowering:
  - `Rvalue::Repeat` array lengths now use `try_to_target_usize` instead of assuming `ConstKind::Value`
  - nested helper functions such as `digit_unchecked::precondition_check` now get stable unique lowered names instead of colliding on leaf item names
  - `simd_extract` and `simd_insert` intrinsics now lower directly instead of surfacing later as missing normal functions
  - several common SIMD arithmetic/bitwise intrinsics are remapped onto the existing vector helper methods
  - the foreign AVX helper `vcvttpd2udq256` now has a bringup-only inline lowering so sysroot compilation can continue past that path
- Real `core` compilation now gets substantially farther and reaches backend lowering of sysroot crates.

## Execution plan

### Phase 1: establish failing baselines

1. `cargo build --bin host_core`
2. `cargo build --target ../../jvm-unknown-unknown.json -Z build-std=core,compiler_builtins -Z build-std-features=compiler-builtins-mem --bin jvm_no_std`
3. `cargo build --target ../../jvm-unknown-unknown.json -Z build-std=core,alloc,compiler_builtins -Z build-std-features=compiler-builtins-mem --bin jvm_alloc`

Capture the first failure in each stage before changing backend code.

### Phase 2: get real `core` compiling

1. Make cross-crate calls first-class instead of treating all upstream items as Kotlin shims.
2. Encode an owner/class naming scheme for upstream crates so method refs can target emitted classes from `core` and `compiler_builtins`.
3. Audit lang items and intrinsics hit during `core` build:
   `copy_nonoverlapping`, `write_bytes`, panic paths, slice/string helpers, integer overflow helpers, and compiler-builtins mem routines.
4. Decide which existing Kotlin helpers stay as runtime support versus which must disappear once `core` is native.
5. Add a regression command for `jvm_no_std` once the first `core` build passes.

## Immediate next steps

1. Keep extending direct lowering or shim coverage for the remaining foreign stdarch helpers hit by real `core`; the latest `jvm_no_std` run now fails on missing `cvtneeph2ps_256` while lowering `mm256_cvtneeph_ps`.
2. Audit the growing family of SIMD/stdarch helper calls and separate them into:
   - helpers that should lower directly in [`src/lower1/control_flow.rs`](../src/lower1/control_flow.rs)
   - helpers that should become reusable runtime/shim methods
3. Remove the remaining `compiler_builtins` normalization ICE around `float::traits::Float::Int` and similar projection types; the backend still hits unresolved projection aliases in generic float/int support code.
4. Decide how `f16` and `f128` should be represented on the JVM side during bringup:
   either lower them to runtime helper objects consistently, or gate unsupported constant cases cleanly instead of relying on bringup-only sentinel encodings.
5. Audit all remaining places that still assume full type normalization succeeds, especially in generic sysroot code paths that reference associated types or projection aliases.
6. Start the cross-crate call model work after the current sysroot-lowering crashes are removed:
   upstream functions from `core` and `compiler_builtins` need real owner/class resolution instead of shim-name fallback.

### Phase 3: get real `alloc` compiling

1. Define the allocator contract for the JVM target.
2. Plumb allocator symbols and `__rust_alloc` family support through lowering and linking, either by:
   - Emitting Rust allocator shims into generated bytecode, or
   - Providing a tiny JVM runtime crate/class that satisfies the Rust allocator ABI.
3. Validate static data, slice/vec growth paths, and string allocation paths emitted from `alloc`.
4. Add a regression command for `jvm_alloc`.

### Phase 4: prepare for `std`

1. Inventory remaining OS/runtime assumptions: threads, fs, env, io, time, process, and unwinding.
2. Split `std` work into "portable pure-Rust pieces" versus "JVM runtime bindings".
3. Only start here after `core` and `alloc` are compiling without the Kotlin shim standing in for them.

## Current blocker snapshot

- `jvm_no_std` now reaches backend lowering for real `core`.
- Earlier failures in the experimental constant path, nested UB-check helpers, `simd_extract`, `simd_insert`, and `vcvttpd2udq256` are gone.
- `core` now fails later on a different foreign stdarch helper, currently surfacing as missing lowered function `cvtneeph2ps_256` while lowering `mm256_cvtneeph_ps`.
- `compiler_builtins` still fails in generic float support code, currently surfacing as unresolved projection normalization around `float::traits::Float::Int`.
- `jvm_alloc` has not been usefully exercised yet because `core` is not compiling cleanly enough to move on.

## Expected first blockers

- Cargo sysroot build may fail before codegen because the target JSON is still minimal.
- `rustc_target` currently ICEs before backend codegen because `arch = "jvm"` has no ABI lowering in the frontend; the first experiment is to report a supported 32-bit arch in the target spec while keeping the JVM backend/linker pipeline.
- If sysroot build reaches codegen, upstream calls from `core` will likely fail because external non-shim items are not linked as method refs across crates.
- `alloc` will likely fail next on allocator ABI and memory intrinsic coverage.
