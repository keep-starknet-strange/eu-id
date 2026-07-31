# P0 Firebase baseline

Date: 2026-08-01

This run measures the canonical `proveIdentity` and `verifyIdentity` APIs before
the P1 through P6 campaign changes. The privacy claim is `public-input
unlinkable; transcript zero knowledge pending`.

## Provenance

- Source commit: `f9b9f8328c70743213ce579d6d6e0a3199b16f17`
- Circuit hash: `9772642c038b0b34c2bbbe2d6a72d11f3d4a954c696a5bacccd5d15ed4974ad9`
- Android AAR SHA-256: `7cf3fd02f2d943e3eebeb0a50e4f3afc8e7b92f610943e8edb6c9e47ad270328`
- Host APK SHA-256: `db83d29372f2dfe0548a45bd4078455c72ac375d5af6322a72965973e408f6a7`
- Test APK SHA-256: `03b174b8178962a89f17a0fabaf6ef44d33d2b7d0935480729f898a27a424e3b`
- Fixture SHA-256: `7f2ac1729642d894ee7ac62783a327e475ad5d5ade9d2000333fe7a051d56766`
- Proof envelope: 1,638,446 bytes
- Firebase matrix: `matrix-248wvpvwz502z`
- [Firebase result](https://console.firebase.google.com/project/exploration-dev-417917/testlab/histories/bh.a21b73b77a063202/matrices/5731670339527455917)

The fixture uses the canonical ISO MSO 1.0 document. All three tests passed.
Each device ran one cold instrumentation test with the release AAR.

## Results

| Firebase model | Device | CPUs | Prove | Verify | Peak RSS | AIR core | Witness |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `shiba` | Pixel 8 | 9 | 9,578 ms | 254 ms | 1,989,380 KiB | 8,324.672 ms | 1,190.715 ms |
| `e3q` | Galaxy S24 Ultra | 8 | 6,385 ms | 226 ms | 2,040,544 KiB | 5,301.233 ms | 1,035.074 ms |
| `a54x` | Galaxy A54 | 8 | 10,276 ms | 578 ms | 1,978,908 KiB | 9,150.748 ms | 989.818 ms |

The baseline misses the 2,000 ms primary prove gate on Pixel 8 and Galaxy S24
Ultra. The A54 also misses the 350 ms verify gate. These are cold, single-run
values, so the final campaign must repeat the same fixed-device method after
the accepted circuit and runtime changes.
