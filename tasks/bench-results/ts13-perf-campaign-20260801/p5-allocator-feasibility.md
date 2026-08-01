# P5 Android allocator feasibility

## Result

Reject the jemalloc candidate for the current campaign. The maintained Rust
bindings do not make a reproducible Android AAR with NDK 27.1.12297006. The
build needs an upstream patch or a local linker shim. The product keeps the
Android system allocator.

No jemalloc AAR or APK exists. Therefore, there is no candidate artifact hash
and no valid device comparison.

## Checkpoint

- Worktree: `/Users/lucas/eu-id/.codex/worktrees/ts13-p5-jemalloc-candidate`
- Branch: `codex/ts13-p5-jemalloc-candidate`
- Base commit: `5562c33c44bc1d2cbd119f9ebab0e40e94512b93`
- Rust: `rustc 1.94.0-nightly (86a49fd71 2026-01-14)`
- cargo-ndk: `4.1.2`
- Android NDK: `27.1.12297006`
- Android targets: `aarch64-linux-android` and `x86_64-linux-android`

## Allocator audit

The canonical SDK has no `#[global_allocator]` item. It has no allocator
dependency. Android uses the allocator that Bionic supplies. The campaign
calls this system path Scudo.

Commit `730e9294` added mimalloc to the old SDK and FFI link units. It did not
limit the change to Android. Commit `4759ad19` removed this code when the
repository moved to one canonical TS13 identity path. No repository commit has
an Android jemalloc candidate.

## Candidate shape

The rejected candidate had one Android-only dependency and one private static:

```toml
[target.'cfg(target_os = "android")'.dependencies]
tikv-jemallocator = { version = "0.6.1", default-features = false, features = ["disable_initial_exec_tls"] }
```

```rust
#[cfg(target_os = "android")]
#[global_allocator]
static ANDROID_ALLOCATOR: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;
```

The `disable_initial_exec_tls` feature is necessary because the SDK shared
library loads after the application starts. The candidate did not change the
UniFFI surface, `proveIdentity`, `verifyIdentity`, the proof statement, or the
proof serialization.

## Build evidence

| Attempt | Result |
| --- | --- |
| `tikv-jemallocator` 0.6.1, host `cargo check -p sdk` | Pass. The Android-only dependency does not build on the host. |
| 0.6.1, release AAR with NDK 27 | Fail at the AArch64 link. `ld.lld` reports `unable to find library -lgcc`. |
| `tikv-jemallocator` 0.7.0 with `tikv-jemalloc-sys` 0.7.1 | Fail in the Android C build because the make phase cannot find NDK target headers. |
| 0.7 with explicit NDK sysroot and target headers | Fail because `prof_sys.c` selects `mach-o/dyld.h` for an Android object. |

Both tested `tikv-jemalloc-sys` build scripts add `-lgcc` for Android. NDK 27
does not contain `libgcc.a`. It contains the LLVM compiler runtime instead:

`toolchains/llvm/prebuilt/darwin-x86_64/lib/clang/18/lib/linux/libclang_rt.builtins-aarch64-android.a`

The 0.6.1 crate checksum is
`0359b4327f954e0567e69fb191cf1436617748813819c94b8cd4a431422d053a`.
Its system-crate checksum is
`cd8aa5b2ab86a2cefa406d889139c162cbb230092f7d1d7cbc1716405d852a3b`.
The 0.7.0 crate checksum is
`249f09e49ab1609436f34c776e84231bead18d6a955f119f939bdc1d847561bd`.
Its selected 0.7.1 system-crate checksum is
`1a2825c78386b4ae0314074867860ba9577875de945f05992c38815cbec327f0`.

## Rejection rule

A local fix would need at least one of these changes:

- vendor and patch `tikv-jemalloc-sys`;
- generate a `libgcc.a` compatibility archive for each Android ABI; or
- build and maintain a separate jemalloc archive outside Cargo.

These changes add build code that is not part of the allocator experiment.
They also make the result depend on a local toolchain shim. Do not use such a
result for the P5 device comparison.

The candidate source and lockfile changes were removed. The branch contains
only this feasibility record and the related task result. The source still
matches base commit `5562c33c`.

## Soundness and API status

The rejected allocator did not change an AIR, a transcript, a public input, or
an artifact input. It did not need a source-bound circuit artifact. No
allocator code remains, so proof soundness and unlinkability are unchanged.

The post-removal checks passed:

- `cargo check --locked -p sdk --all-targets`
- `cargo test --locked --release -p sdk --lib -j12 -- --test-threads=1`
  (`13 passed; 0 failed`)
- `git diff --check`

The SDK source, manifest, and lockfile have no difference from base commit
`5562c33c`.

No Firebase upload or device run occurred in this work.

The P5 allocator comparison is closed as not feasible on the pinned toolchain.
Keep the Android system allocator for this campaign. Reopen the comparison only
after the maintained jemalloc binding supports NDK 27 without a local patch.
