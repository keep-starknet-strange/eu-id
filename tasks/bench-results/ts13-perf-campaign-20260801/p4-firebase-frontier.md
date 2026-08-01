# P4 Firebase frontier

Date: 2026-08-01

Status: in progress. One of ten eligible points is complete.

The privacy claim is `public-input unlinkable; transcript zero knowledge pending`.
This run used the canonical `proveIdentity` and `verifyIdentity` APIs.

## Provenance

- Point: blowup 3, 36 queries, 20 proof-of-work bits, lift 19
- Source commit: `4e14f09df39f2820f3c2eaffe433a16ad62b9b2a`
- Artifact commit: `95e5f9a820904e32abb39a3eedfcf04f52cf88be`
- Benchmark harness commit: `5562c33c44bc1d2cbd119f9ebab0e40e94512b93`
- Fixture binding commit: `6920c7a60db71fb4a5408b2b66b553d21ae6b765`
- Circuit SHA-256: `4d55b4e5cb6d4fab102395d3647d267d3f3116e6cabae9e33f3c957f7e07c2b2`
- AAR SHA-256: `8e53ecfddb047e0be8a958a71eee2472b8a1f3d5d367238d3c83922b9dd318bd`
- Fixture SHA-256: `ad775e87c9369b85e707025bf8f909715e2fc4de97e3db8005e10317bdbf8863`
- Host APK SHA-256: `372ccb129256e479a61f53bae3305c424c11c0c905f4fdda2320f5f7de86d1be`
- Test APK SHA-256: `287be0265632bec74bd450edc53fdc96475329316e54d936016e9b07ef115ca0`
- Envelope: 1,572,910 bytes
- Firebase project: `exploration-dev-503108`
- Firebase matrix: `matrix-t75o13p0yobva`
- Result directory: `ts13-unlinkable-v1-p4-q36-p20-l19-parallel-20260801-2`
- Result bucket: `test-lab-67wdfy26qh61w-j1q1w8tsupf6x`
- [Firebase result](https://console.firebase.google.com/project/exploration-dev-503108/testlab/histories/bh.f2a4643da48d3d54/matrices/7186493250225133801)

Firebase created the three executions in one matrix. Each execution used the
same APK pair and `rayon_threads=6`. All three tests passed.

The matrix specification used these two objects for all three executions:

- `gs://test-lab-67wdfy26qh61w-j1q1w8tsupf6x/ts13-unlinkable-v1-p4-q36-p20-l19-parallel-20260801-2/EuIdBenchAndroid-release.apk`
- `gs://test-lab-67wdfy26qh61w-j1q1w8tsupf6x/ts13-unlinkable-v1-p4-q36-p20-l19-parallel-20260801-2/EuIdBenchAndroid-release-androidTest.apk`

The downloaded objects matched the two local APKs byte for byte. Their sizes
were 18,361,258 bytes and 711,119 bytes.

## Results

| Firebase model | Device | Prove | Verify | Peak RSS | AIR core | Witness |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `shiba` | Pixel 8 | 5,664 ms | 218 ms | 1,646,140 KiB | 5,069.804 ms | 558.731 ms |
| `e3q` | Galaxy S24 Ultra | 3,884 ms | 126 ms | 1,744,896 KiB | 3,528.066 ms | 315.884 ms |
| `a54x` | Galaxy A54 | 6,062 ms | 202 ms | 1,643,952 KiB | 5,351.765 ms | 632.486 ms |

Each device used six effective Rayon workers. The proof thread and each proof
worker had a 67,108,864-byte stack. The run did not request or apply an
affinity policy.

| Phase | Pixel 8 | Galaxy S24 Ultra | Galaxy A54 |
| --- | ---: | ---: | ---: |
| Public input | 0.179 ms | 0.369 ms | 3.701 ms |
| Credential extract | 2.280 ms | 14.190 ms | 16.622 ms |
| Witness generation | 558.731 ms | 315.884 ms | 632.486 ms |
| Twiddles | 1.855 ms | 1.324 ms | 4.148 ms |
| Tree 0 write | 43.125 ms | 27.150 ms | 48.290 ms |
| Tree 0 commit | 82.631 ms | 58.728 ms | 88.139 ms |
| Tree 1 write | 61.917 ms | 43.531 ms | 68.540 ms |
| Tree 1 commit | 661.406 ms | 435.375 ms | 623.251 ms |
| Tree 2 write | 1,535.002 ms | 1,089.727 ms | 1,594.689 ms |
| Tree 2 commit | 224.341 ms | 165.969 ms | 220.940 ms |
| Round GKR | 1,028.826 ms | 849.261 ms | 1,210.001 ms |
| Interaction commit | 27.947 ms | 20.186 ms | 33.700 ms |
| Build components | 17.787 ms | 12.043 ms | 21.610 ms |
| STARK prove | 1,382.461 ms | 814.846 ms | 1,434.062 ms |
| Composition | 943.918 ms | 483.466 ms | 940.252 ms |
| Composition polynomial | 874.859 ms | 427.839 ms | 858.580 ms |
| OODS evaluation | 31.617 ms | 30.513 ms | 36.599 ms |
| FRI quotients | 112.951 ms | 111.398 ms | 122.287 ms |
| Proof of work | 108.043 ms | 101.751 ms | 152.256 ms |
| FRI opening | 185.931 ms | 87.717 ms | 182.668 ms |
| AIR core total | 5,069.804 ms | 3,528.066 ms | 5,351.765 ms |
| SDK core prove | 5,637.194 ms | 3,862.552 ms | 6,007.994 ms |

| Memory point | Pixel 8 RSS / HWM | S24 Ultra RSS / HWM | A54 RSS / HWM |
| --- | ---: | ---: | ---: |
| Runtime start | 107,144 / 107,144 KiB | 114,064 / 114,064 KiB | 93,488 / 93,488 KiB |
| Witness complete | 257,468 / 298,284 KiB | 345,792 / 345,792 KiB | 310,164 / 310,164 KiB |
| Tree 2 write | 970,016 / 1,108,268 KiB | 1,081,724 / 1,215,444 KiB | 976,376 / 1,149,028 KiB |
| Tree 2 commit | 1,122,024 / 1,138,604 KiB | 1,254,040 / 1,254,040 KiB | 1,153,508 / 1,153,508 KiB |
| Round GKR | 895,996 / 1,646,140 KiB | 1,054,248 / 1,744,896 KiB | 952,180 / 1,643,952 KiB |
| AIR core total | 167,780 / 1,646,140 KiB | 468,644 / 1,744,896 KiB | 298,760 / 1,643,952 KiB |

The Pixel 8 process could use CPU identifiers 0 through 7. The S24 Ultra
process could use identifiers 0 through 6. The A54 process could use
identifiers 0 through 2 and 4 through 7. These values came from
`/proc/thread-self/status`. The run recorded the online topology from
`/sys/devices/system/cpu/online`.

## Checkpoint comparison

The P0 run used an older circuit. This comparison shows campaign progress. It
does not select a P4 point.

| Device | P0 prove | Current prove | Change | P0 peak RSS | Current peak RSS |
| --- | ---: | ---: | ---: | ---: | ---: |
| Pixel 8 | 9,578 ms | 5,664 ms | -40.9% | 1,989,380 KiB | 1,646,140 KiB |
| Galaxy S24 Ultra | 6,385 ms | 3,884 ms | -39.2% | 2,040,544 KiB | 1,744,896 KiB |
| Galaxy A54 | 10,276 ms | 6,062 ms | -41.0% | 1,978,908 KiB | 1,643,952 KiB |

The P3 Pixel 8 checkpoint proved in 8,101 ms and used 1,860,328 KiB. The
current point reduces these values by 30.1% and 11.5%, respectively.

## Log limit

The uploaded harness wrote one JSON value with the complete phase array. Each
device log contains exactly 4,100 bytes for this value. Android cut the value
during the phase array. The top-level latency, size, memory, runtime, stack,
affinity, and topology fields are complete. The product branch now writes one
bounded summary record and one bounded record for each phase. The selected P4
package must use this new format for the P5 and final gate runs.

## Remaining work

Nine eligible source-bound APK pairs still need a cold Pixel 8 measurement.
The product point is the fastest eligible Pixel 8 result below the approved
2,500,000-byte envelope ceiling. This checkpoint does not meet the 2,000 ms
final prove gate on any binding phone.
