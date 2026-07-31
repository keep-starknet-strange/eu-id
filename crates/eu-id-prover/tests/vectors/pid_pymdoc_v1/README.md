# pyMDOC PID parser fixture

`issuer_signed.cbor` contains an `eu.europa.ec.eudi.pid.1` `IssuerSigned`
value. The source is
[pyMDOC-CBOR](https://github.com/eu-digital-identity-wallet/pyMDOC-CBOR) at
commit `aecbd8e929879a882c9c45e435211561c7f2d1bb`. The upstream license is
Apache-2.0.

The Rust tests load only `issuer_signed.cbor`. They check the MSO version,
namespace shape, exact tagged item bytes, and item-key order.

SHA-256:

```text
4774c2192afd3382365ac73ab8d85f2886812fbc53ac05268f05479df2ba7c04  issuer_signed.cbor
```

`issuer_chain.der` and `device_key.pem` record the source values. The upstream
generator uses random item salts, so it cannot reproduce the checked-in CBOR
bytes.
