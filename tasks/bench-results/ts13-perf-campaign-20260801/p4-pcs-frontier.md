# P4 PCS and FRI frontier

Date: 2026-08-01

Status: in progress.

The privacy claim is `public-input unlinkable; transcript zero knowledge pending`.
All points use ML-DSA-65 for the issuer, device, and revocation roles. All points
use the sound 25-row Keccak carrier and its 9,102,656-cell service.

## Method

Each row satisfies this PCS label:

```text
query count * log blowup + proof-of-work bits = 128
```

The sweep removes a point if a lower proof-of-work value has the same query
count. It tests each remaining point with no explicit lift and with the minimum
valid explicit lift. The minimum lift is log size 18 for blowup 1 and 2. It is
log size 19 for blowup 3.

The current proof has these fixed values:

- 7,008 opened columns;
- 9,193 sampled secure fields;
- 3,872 bytes of outer claims;
- 20 AIRs;
- a maximum 20,128-byte GKR payload;
- base tree log sizes 16, 16, 16, 13, and 16;
- composition evaluation log size 18.

The artifact rounds the worst proof body to the next 65,536-byte boundary. It
adds the fixed 46-byte identity-proof header.

## Exact envelope frontier

| Blowup | Queries | PoW | Lift | Worst body | Capacity | Envelope | Status |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | :---: |
| 3 | 36 | 20 | none | 1,506,440 | 1,507,328 | 1,507,374 | eligible |
| 3 | 35 | 23 | none | 1,472,488 | 1,507,328 | 1,507,374 | eligible |
| 3 | 36 | 20 | 19 | 1,509,900 | 1,572,864 | 1,572,910 | eligible |
| 3 | 35 | 23 | 19 | 1,475,852 | 1,507,328 | 1,507,374 | eligible |
| 2 | 54 | 20 | none | 2,095,112 | 2,097,152 | 2,097,198 | eligible |
| 2 | 53 | 22 | none | 2,061,576 | 2,097,152 | 2,097,198 | eligible |
| 2 | 52 | 24 | none | 2,028,040 | 2,031,616 | 2,031,662 | eligible |
| 2 | 54 | 20 | 18 | 2,100,300 | 2,162,688 | 2,162,734 | eligible |
| 2 | 53 | 22 | 18 | 2,066,668 | 2,097,152 | 2,097,198 | eligible |
| 2 | 52 | 24 | 18 | 2,033,036 | 2,097,152 | 2,097,198 | eligible |
| 1 | 108 | 20 | none | 3,861,128 | 3,866,624 | 3,866,670 | STWO rejection |
| 1 | 107 | 21 | none | 3,828,008 | 3,866,624 | 3,866,670 | STWO rejection |
| 1 | 106 | 22 | none | 3,794,888 | 3,801,088 | 3,801,134 | STWO rejection |
| 1 | 105 | 23 | none | 3,761,768 | 3,801,088 | 3,801,134 | STWO rejection |
| 1 | 104 | 24 | none | 3,728,648 | 3,735,552 | 3,735,598 | STWO rejection |
| 1 | 108 | 20 | 18 | 3,912,972 | 3,932,160 | 3,932,206 | STWO rejection |
| 1 | 107 | 21 | 18 | 3,879,372 | 3,932,160 | 3,932,206 | STWO rejection |
| 1 | 106 | 22 | 18 | 3,845,772 | 3,866,624 | 3,866,670 | STWO rejection |
| 1 | 105 | 23 | 18 | 3,812,172 | 3,866,624 | 3,866,670 | STWO rejection |
| 1 | 104 | 24 | 18 | 3,778,572 | 3,801,088 | 3,801,134 | STWO rejection |

The selection ceiling is 2,500,000 bytes. The pinned STWO MLE prover also
rejects blowup 1 before query and proof-of-work processing. Its inferred
`ExtendToEvalDomain` mode is not implemented. The table records the exact
analytic sizes, but no sound proof artifact exists for those rows.

## Valid source and artifact ledger

Each source commit has a separate generated-artifact commit. Each listed probe
passed artifact drift and one live `proveIdentity` and `verifyIdentity` run
before the final timing campaign.

| Blowup | Queries | PoW | Lift | Source commit | Artifact commit | Generation input SHA-256 | Circuit SHA-256 | Probe SHA-256 |
| ---: | ---: | ---: | ---: | --- | --- | --- | --- | --- |
| 2 | 54 | 20 | none | `cd4567370d0967a45cf1886e75c88443bc3f866f` | `e56bd8a7fde21417fc63335452e49732fe167c54` | `0b1a32399ce8f8b9871df5c70c1786d869be87c3ddc2e9eaf8398f00e279ec51` | `6ffaf7fa2274b5d486c79c5504c340f3bcd9004f7f4aa7523a731e8c27e62368` | `c2ddab5c36742737c0ddd5c63f9d14cf058ed68a8978faf5755e10c7dcadcb99` |
| 2 | 53 | 22 | none | `18b8fc73218156ccb37c49b3c176c0a4a54789f1` | `895b3833c16eee87a549467ee576cb8136803a03` | `849e3057c8dc10432612a7eecf3c0f3d0d8b1a6506d112d56b81a1eb96d4d854` | `fd77e8d34592bc6b06cfb690dd25a98dbed61c1c0ea561a231eaf7b3781cd724` | `ede465e6bbbf98d428b63f8e103e9dd6d9aaa15a7ceb16a92a5cb3c510af982b` |
| 2 | 52 | 24 | none | `d3da76c13d2c99a552e93905704070b9a1b501a7` | `103b289464df151f53b51ba7602d2004c9e64773` | `c9a88cccf576c3bd0060b5c6a25bd2018f6eccc42ecb54a0112c8da0d77dfea1` | `e4931cbdc3499a614aafdf1c140561736629895c1369836bce521703ecd36d3f` | `b74c291196c69e0219327a2e54ee2aa33e3127d1a98c62532b5dc0541240cf44` |
| 2 | 54 | 20 | 18 | `681d0bb76745a34add73f4a711c7da0cf93c07e9` | `0b2c0de6dd9480d86b9327571df9028b08032cbd` | `cbde428631ab86c80c126766c099f1a4702b705f54ef281ace5aab2232e0599c` | `7a1ffb8f0e38dc5a97d1ca49d19c4e1f7cea32a4ff612cbe4299a226f9fd3303` | `5d6040c031d3ac929bc190e3f68cc6b840804b233ea5b6e58e946e3ada28c5a1` |
| 2 | 53 | 22 | 18 | `2222ca175bfbdbb7dc82eb02a2c6922f22590a0c` | `9ece1fabb3e3d907842b4b4f61dd21890d731ec4` | `3c2d92686af595c72368e1030f526e8f20ae9f5d436cabcfc97c56aede41ea62` | `3da0d201333316da2bb8243812d7980e21f18b45b9283bf284da686c7f1dd800` | `21457168526a31d0e53adfa2dede20f876acef775ea4f87b7cafd45ba26abb3a` |
| 2 | 52 | 24 | 18 | `ce2a42e71210de9ca37da32eb9609ecb162390b0` | `0ebc4a5e0a1f6d028ae7958dbe343bb621449b8e` | `5b2e10b4ec4e1d9a61dec38f47d115ea29599826f8b1b06369236f0cf4ea15eb` | `e7150917a9144f67d9036505fa0a0b1004db8c64f2fe81b86fc0c337b18942b2` | `8eeff34ab76f312ccbfbefa267bbeb35aa612fd55fea979bb3f22686833188c3` |
| 3 | 36 | 20 | none | `edde21bbe0fff0a42666e278940a933631e03925` | `269d5854a7aa9c3532f2bb1c9dc8540122d15615` | `b7e4fd6cfd1c610b5c61ca588acfdf7f46bd013802d7b96ebbc24c23d3b0bbed` | `f5b6e13df0405190b5715b4bb8c4d5313dd4c22149167e5b23bceba03289717c` | `b89e57813581abc01afb793452e8f6e84aa11bf7ee88ab185c8a0c7b5c54b741` |
| 3 | 35 | 23 | none | `c9f45da8ac65066d8b6e9d19b88dfe3f9be32a5d` | `382eadec1046751c575e6754148c8d4316c31815` | `9d38f038cdec98acf5392c90f0f0fcd8562f290df3532786c2eb1efb4963e4e9` | `23463f054d71ba16f908b6aa61eba48eca1b6795b48ec324ed1bd160a8950222` | `3fa09eceb91579a6992e776644d4410881064cadc4be999f372c4f77577bfc78` |
| 3 | 35 | 23 | 19 | `1777c39b402646bd50e4510b1e507b36e7979dfe` | `9f976ad59d1da0d9097ce65a247ff4eaf12d2476` | `4c345eef8c32665822fe080c853e1c907e11ca5ec33f35ce8b07d713e5284379` | `e6fd40594e446dd70c45598bd8e82d58d8dfb86722aa81714460c748d4e59668` | `bba0d8c70f49959c3ae298ba763a31e74dd1c5b20a3ceea476bc8fd508a8278e` |
| 3 | 36 | 20 | 19 | `4e14f09df39f2820f3c2eaffe433a16ad62b9b2a` | `95e5f9a820904e32abb39a3eedfcf04f52cf88be` | `60f05b9e596a48e03f6895f36f962775f3f6d1f2dfd50ca3fbb94640153863f0` | `4d55b4e5cb6d4fab102395d3647d267d3f3116e6cabae9e33f3c957f7e07c2b2` | `593a2a7370cefc25a5b221727ec7b41d462606982a3a548a78616b470cc8fff9` |

## Cold desktop measurements

The host is an Apple M2 Max with 12 CPU cores and 32 GB of memory. The campaign
ran seven fresh processes for each point. It ran one process at a time. Each
process used 12 Rayon workers and a 512 MiB minimum Rayon stack. The order
rotated after each round and reversed on alternate rounds.

| Blowup | Queries | PoW | Lift | Prove median (range) | Verify median | Peak RSS median | Envelope |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 54 | 20 | none | 1,163 ms (1,144–1,182) | 32 ms | 1,414.3 MiB | 2,097,198 B |
| 2 | 53 | 22 | none | 1,160 ms (1,151–1,207) | 32 ms | 1,416.8 MiB | 2,097,198 B |
| 2 | 52 | 24 | none | 1,162 ms (1,141–1,332) | 32 ms | 1,412.6 MiB | 2,031,662 B |
| 2 | 54 | 20 | 18 | 1,158 ms (1,148–1,244) | 32 ms | 1,421.7 MiB | 2,162,734 B |
| 2 | 53 | 22 | 18 | **1,157 ms (1,148–1,240)** | 32 ms | 1,419.2 MiB | 2,097,198 B |
| 2 | 52 | 24 | 18 | 1,167 ms (1,161–1,652) | 32 ms | 1,427.2 MiB | 2,097,198 B |
| 3 | 36 | 20 | none | 1,243 ms (1,239–1,263) | 36 ms | 1,744.0 MiB | 1,507,374 B |
| 3 | 35 | 23 | none | 1,246 ms (1,234–1,316) | 36 ms | 1,751.2 MiB | 1,507,374 B |
| 3 | 36 | 20 | 19 | 1,236 ms (1,230–1,242) | 35 ms | 1,782.0 MiB | 1,572,910 B |
| 3 | 35 | 23 | 19 | 1,273 ms (1,250–1,348) | 38 ms | 1,743.3 MiB | 1,507,374 B |

The fastest desktop median is the blowup-two, q53, PoW22, lift-18 point. The
desktop result does not select the product point. The approved rule selects the
fastest eligible cold Pixel 8 point.

## Raw desktop samples

Each line gives prove milliseconds, verify milliseconds, and peak-RSS bytes in
round order.

```text
b2-q54-p20-none prove=[1182,1169,1163,1144,1165,1160,1163] verify=[31,32,32,33,32,32,31] rss=[1484734464,1482981376,1454587904,1501659136,1491943424,1460420608,1456422912]
b2-q53-p22-none prove=[1207,1155,1170,1159,1178,1151,1160] verify=[32,32,33,32,32,32,32] rss=[1480769536,1488912384,1476673536,1499676672,1485586432,1492582400,1484128256]
b2-q52-p24-none prove=[1148,1184,1162,1332,1142,1141,1251] verify=[32,32,32,32,32,32,32] rss=[1490255872,1447002112,1481244672,1499365376,1460125696,1461846016,1499414528]
b2-q54-p20-l18 prove=[1175,1152,1158,1244,1154,1148,1158] verify=[31,32,32,33,32,32,32] rss=[1490747392,1502085120,1489108992,1487601664,1510375424,1491828736,1487601664]
b2-q53-p22-l18 prove=[1158,1158,1151,1154,1240,1157,1148] verify=[32,31,32,32,32,32,31] rss=[1493843968,1489125376,1472708608,1473036288,1465614336,1534984192,1488109568]
b2-q52-p24-l18 prove=[1337,1161,1233,1652,1162,1162,1167] verify=[32,32,31,32,31,32,31] rss=[1494286336,1493712896,1496481792,1494089728,1523105792,1536245760,1501675520]
b3-q36-p20-none prove=[1263,1245,1243,1239,1247,1243,1242] verify=[36,36,36,35,35,36,36] rss=[1822572544,1830764544,1805860864,1828683776,1860485120,1836630016,1821982720]
b3-q35-p23-none prove=[1302,1234,1246,1263,1237,1237,1316] verify=[36,36,35,36,36,35,36] rss=[1836220416,1893122048,1831698432,1833271296,1866301440,1840087040,1834647552]
b3-q36-p20-l19 prove=[1230,1236,1238,1240,1236,1242,1231] verify=[35,35,35,36,35,34,35] rss=[1868513280,1852981248,1862238208,1869643776,1867644928,1927151616,1918484480]
b3-q35-p23-l19 prove=[1273,1266,1274,1348,1331,1250,1254] verify=[37,35,38,38,38,38,35] rss=[1853440000,1831174144,1827291136,1821245440,1827930112,1821327360,1830633472]
```

One reused-target product executable failed after core proof. Its SHA-256 was
`59c41cc11929316f84c72de5cfaca937f6bd5adade2c0825a27881fa1f55afa2`.
It is not evidence. A fresh empty-target build produced the product probe hash
in the ledger and passed all seven scheduled runs. A separate 22-proof audit
measured fixed-int proof bodies from 1,413,257 to 1,426,137 bytes. The exact
bound is 1,509,900 bytes and the aligned body capacity is 1,572,864 bytes. The
envelope bound is valid, and no source change is needed.

## Phone measurements

No all-ML-DSA-65 frontier phone row is complete yet.

The current blowup-3, q36, PoW20, lift-19 checkpoint has a verified Android
build:

- circuit hash: `4d55b4e5cb6d4fab102395d3647d267d3f3116e6cabae9e33f3c957f7e07c2b2`;
- fixture SHA-256: `ad775e87c9369b85e707025bf8f909715e2fc4de97e3db8005e10317bdbf8863`;
- AAR SHA-256: `8e53ecfddb047e0be8a958a71eee2472b8a1f3d5d367238d3c83922b9dd318bd`;
- benchmark-harness commit: `5562c33c`;
- host APK SHA-256: `748cc8af40b057ebff0831ba3629cfb4dd1957bfc673b47894aac6756374a013`;
- test APK SHA-256: `287be0265632bec74bd450edc53fdc96475329316e54d936016e9b07ef115ca0`.

All 16 release host unit tests and both APK builds passed. The test APK contains
the current circuit-bound fixture. The Firebase upload waits for explicit
approval to send these proprietary APKs to project `exploration-dev-503108`.
