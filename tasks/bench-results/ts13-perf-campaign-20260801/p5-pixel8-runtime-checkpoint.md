# P5 Pixel 8 runtime-control checkpoint

Status: preliminary. P2 will change the circuit. Run the final device sweep after P2.

## Input

- Source commit: `5a6087767726a5fffe5c67d3781aa8429318d21f`
- Circuit hash: `cc4c00d4fa753641afb2a9a3b08635f8a7ee35bd1bccb708e0d0dd8a8619b729`
- Host APK SHA-256: `c1705cfff49a4912662dbfedc558d27bee0d9d237fd72545d74abe0d084e70cf`
- Test APK SHA-256: `bdb2f1c304c6d26d0abacc8d1d5cbf0769048f0c05297df9079e2a95f494ca28`
- Firebase matrix: `matrix-qhoy3e1ja82ma`
- Device: Google Pixel 8, Android API 34
- Requested and effective Rayon workers: 8
- Allowed CPUs: 0 through 7
- Proof thread and worker stack: 64 MiB each
- Sample: one cold `proveIdentity` call and one `verifyIdentity` call

## Result

| Prove | Verify | Envelope | Process HWM | Witness | AIR core |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 5,588 ms | 222 ms | 1,572,910 bytes | 1,862,644 KiB | 329.306 ms | 5,213.082 ms |

The AIR core is the binding phase. Witness generation is 5.9% of the complete prove time. The
process approached the device memory limit and caused Android to kill background processes. P2 must
reduce the shared Keccak service before the final worker, affinity, and allocator sweep.
