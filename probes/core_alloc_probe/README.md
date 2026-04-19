# core_alloc_probe

External probe crate for staged bringup of real Rust `core` and `alloc` on the JVM backend.

## Commands

Host-target backend smoke test:

```bash
cargo build --bin host_core
```

Custom target with real `core`:

```bash
cargo build \
  --target ../../jvm-unknown-unknown.json \
  -Z build-std=core,compiler_builtins \
  -Z build-std-features=compiler-builtins-mem \
  --bin jvm_no_std
```

Custom target with real `core` + `alloc`:

```bash
cargo build \
  --target ../../jvm-unknown-unknown.json \
  -Z build-std=core,alloc,compiler_builtins \
  -Z build-std-features=compiler-builtins-mem \
  --bin jvm_alloc
```

## Notes

- `.cargo/config.toml` is copied from the generated backend config so this crate behaves like an external consumer.
- `jvm_no_std` and `jvm_alloc` are compile probes first. They are expected to expose sysroot, lowering, or linker/runtime gaps before they become runnable applications.
