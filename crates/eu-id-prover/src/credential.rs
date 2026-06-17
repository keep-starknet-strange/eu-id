//! The simplified POC credential `C` — a fixed signed byte-layout that stands
//! in for an ISO/IEC 18013-5 mdoc for the proof-of-concept.
//!
//! **This is the frozen interface contract.** Every cross-component binding
//! relation added later (the SHA preimage field-exposure provider and the
//! age / nationality credential bindings) keys off the field offsets defined
//! here, so the layout must not change once consumers exist. The same contract
//! is documented prose-side in `docs/credential-format.md`.
//!
//! Layout — binary-packed, multi-byte integer fields big-endian. Total
//! [`CREDENTIAL_LEN`] = 11 bytes, which fits in a single 64-byte SHA-256 block
//! (so both credential fields live in block 0, keeping the field-exposure
//! relation single-block):
//!
//! ```text
//! off len field         encoding
//!  0   4  magic         ASCII "EUID"  (0x45 0x55 0x49 0x44)
//!  4   1  version       0x01
//!  5   2  birth year    u16 big-endian
//!  7   1  birth month   u8  (1..=12)
//!  8   1  birth day     u8  (1..=31)
//!  9   2  nationality   u16 big-endian (ISO-3166-1 numeric)
//! ```
//!
//! The byte windows the predicate bindings consume are [`DOB_WINDOW`] (the
//! `year/month/day` bytes) and [`NATIONALITY_WINDOW`]. The byte ↔ value
//! reconciliation a binding proves is just big-endian recomposition:
//!
//! ```text
//! year  = C[5] * 256 + C[6]      month = C[7]      day = C[8]
//! code  = C[9] * 256 + C[10]
//! ```
//!
//! The format is deliberately minimal — the POC's honesty disclaimer already
//! covers "not a real mdoc". It carries no issuer id, no validity window, no
//! signature-suite bytes; those return with the deferred full-mdoc work.

use core::fmt;
use core::ops::Range;

/// Magic / header bytes identifying the credential format (ASCII "EUID").
pub const MAGIC: [u8; 4] = *b"EUID";

/// Credential format version. Bumped if the layout ever changes (it should not,
/// once consumers exist — see the module docs).
pub const VERSION: u8 = 1;

/// Offset of the 4-byte magic.
pub const OFF_MAGIC: usize = 0;
/// Offset of the 1-byte version.
pub const OFF_VERSION: usize = 4;
/// Offset of the 2-byte big-endian birth year.
pub const OFF_BIRTH_YEAR: usize = 5;
/// Offset of the 1-byte birth month.
pub const OFF_BIRTH_MONTH: usize = 7;
/// Offset of the 1-byte birth day.
pub const OFF_BIRTH_DAY: usize = 8;
/// Offset of the 2-byte big-endian nationality code.
pub const OFF_NATIONALITY: usize = 9;

/// Total encoded length of a credential, in bytes.
pub const CREDENTIAL_LEN: usize = 11;

// The single-block field-exposure relation depends on the whole credential
// fitting in one 64-byte SHA-256 block. Enforced at compile time.
const _: () = assert!(
    CREDENTIAL_LEN <= 64,
    "credential must fit one SHA-256 block"
);

/// Byte window covering the date-of-birth field (`year_hi, year_lo, month, day`)
/// — the 4 bytes the age ↔ credential binding requires.
pub const DOB_WINDOW: Range<usize> = OFF_BIRTH_YEAR..OFF_NATIONALITY; // 5..9

/// Byte window covering the nationality field (`code_hi, code_lo`) — the 2 bytes
/// the nationality ↔ credential binding requires.
pub const NATIONALITY_WINDOW: Range<usize> = OFF_NATIONALITY..CREDENTIAL_LEN; // 9..11

/// The semantic content of a [`CREDENTIAL_LEN`]-byte credential.
///
/// Field validity (a real calendar date, an assigned ISO code) is intentionally
/// **not** enforced here — that is the predicates' job. This type only owns the
/// byte layout (the frozen contract); [`decode`](Credential::decode) checks
/// only the structural invariants (length, magic, version).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Credential {
    pub birth_year: u16,
    pub birth_month: u8,
    pub birth_day: u8,
    /// ISO-3166-1 numeric country code (e.g. 276 = Germany).
    pub nationality: u16,
}

impl Credential {
    /// Construct a credential from its semantic fields.
    pub fn new(birth_year: u16, birth_month: u8, birth_day: u8, nationality: u16) -> Self {
        Self {
            birth_year,
            birth_month,
            birth_day,
            nationality,
        }
    }

    /// Serialize to the frozen [`CREDENTIAL_LEN`]-byte layout. This is the
    /// preimage `C` the issuer hashes (SHA-256) and signs (ECDSA-P256).
    pub fn encode(&self) -> [u8; CREDENTIAL_LEN] {
        let mut c = [0u8; CREDENTIAL_LEN];
        c[OFF_MAGIC..OFF_MAGIC + MAGIC.len()].copy_from_slice(&MAGIC);
        c[OFF_VERSION] = VERSION;
        c[OFF_BIRTH_YEAR..OFF_BIRTH_MONTH].copy_from_slice(&self.birth_year.to_be_bytes());
        c[OFF_BIRTH_MONTH] = self.birth_month;
        c[OFF_BIRTH_DAY] = self.birth_day;
        c[OFF_NATIONALITY..CREDENTIAL_LEN].copy_from_slice(&self.nationality.to_be_bytes());
        c
    }

    /// Parse a credential from bytes, checking the structural invariants
    /// (length, magic, version). Semantic field validity is left to the
    /// predicates.
    pub fn decode(bytes: &[u8]) -> Result<Self, CredentialError> {
        if bytes.len() != CREDENTIAL_LEN {
            return Err(CredentialError::BadLength {
                expected: CREDENTIAL_LEN,
                got: bytes.len(),
            });
        }
        if bytes[OFF_MAGIC..OFF_MAGIC + MAGIC.len()] != MAGIC {
            return Err(CredentialError::BadMagic);
        }
        if bytes[OFF_VERSION] != VERSION {
            return Err(CredentialError::UnsupportedVersion(bytes[OFF_VERSION]));
        }
        Ok(Self {
            birth_year: u16::from_be_bytes([bytes[OFF_BIRTH_YEAR], bytes[OFF_BIRTH_YEAR + 1]]),
            birth_month: bytes[OFF_BIRTH_MONTH],
            birth_day: bytes[OFF_BIRTH_DAY],
            nationality: u16::from_be_bytes([bytes[OFF_NATIONALITY], bytes[OFF_NATIONALITY + 1]]),
        })
    }

    /// The 4 date-of-birth bytes (`year_hi, year_lo, month, day`) — the exact
    /// bytes [`DOB_WINDOW`] selects from [`encode`](Credential::encode).
    pub fn dob_bytes(&self) -> [u8; 4] {
        let c = self.encode();
        c[DOB_WINDOW].try_into().expect("DOB_WINDOW is 4 bytes")
    }

    /// The 2 nationality bytes (`code_hi, code_lo`) — the exact bytes
    /// [`NATIONALITY_WINDOW`] selects from [`encode`](Credential::encode).
    pub fn nationality_bytes(&self) -> [u8; 2] {
        let c = self.encode();
        c[NATIONALITY_WINDOW]
            .try_into()
            .expect("NATIONALITY_WINDOW is 2 bytes")
    }
}

/// Errors from [`Credential::decode`]. Only structural failures; semantic field
/// validity (a real date, an assigned ISO code) is the predicates' concern.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CredentialError {
    /// The byte slice was not exactly [`CREDENTIAL_LEN`] long.
    BadLength { expected: usize, got: usize },
    /// The magic header did not match [`MAGIC`].
    BadMagic,
    /// The version byte is not a supported [`VERSION`].
    UnsupportedVersion(u8),
}

impl fmt::Display for CredentialError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BadLength { expected, got } => {
                write!(f, "credential must be {expected} bytes, got {got}")
            }
            Self::BadMagic => write!(f, "credential magic header does not match \"EUID\""),
            Self::UnsupportedVersion(v) => write!(f, "unsupported credential version {v}"),
        }
    }
}

impl std::error::Error for CredentialError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_has_frozen_layout() {
        // 2007-03-15, Germany (276 = 0x0114).
        let c = Credential::new(2007, 3, 15, 276);
        let bytes = c.encode();
        assert_eq!(bytes.len(), CREDENTIAL_LEN);
        assert_eq!(&bytes[OFF_MAGIC..OFF_MAGIC + 4], b"EUID");
        assert_eq!(bytes[OFF_VERSION], 1);
        assert_eq!(
            &bytes[OFF_BIRTH_YEAR..OFF_BIRTH_MONTH],
            &2007u16.to_be_bytes()
        );
        assert_eq!(bytes[OFF_BIRTH_MONTH], 3);
        assert_eq!(bytes[OFF_BIRTH_DAY], 15);
        assert_eq!(&bytes[OFF_NATIONALITY..CREDENTIAL_LEN], &[0x01, 0x14]);
    }

    #[test]
    fn roundtrips_through_decode() {
        for c in [
            Credential::new(2000, 1, 1, 276),
            Credential::new(2008, 6, 17, 250),
            Credential::new(1906, 12, 31, 840),
        ] {
            assert_eq!(Credential::decode(&c.encode()), Ok(c));
        }
    }

    #[test]
    fn windows_select_the_documented_bytes() {
        let c = Credential::new(2007, 3, 15, 276);
        let bytes = c.encode();
        assert_eq!(&bytes[DOB_WINDOW], &c.dob_bytes());
        assert_eq!(&bytes[NATIONALITY_WINDOW], &c.nationality_bytes());
        // The reconciliation formulas the bindings prove.
        let d = c.dob_bytes();
        assert_eq!(u16::from(d[0]) * 256 + u16::from(d[1]), 2007);
        assert_eq!(d[2], 3);
        assert_eq!(d[3], 15);
        let n = c.nationality_bytes();
        assert_eq!(u16::from(n[0]) * 256 + u16::from(n[1]), 276);
    }

    #[test]
    fn decode_rejects_bad_length() {
        assert_eq!(
            Credential::decode(&[0u8; 10]),
            Err(CredentialError::BadLength {
                expected: CREDENTIAL_LEN,
                got: 10
            })
        );
    }

    #[test]
    fn decode_rejects_bad_magic() {
        let mut bytes = Credential::new(2000, 1, 1, 276).encode();
        bytes[0] = b'X';
        assert_eq!(Credential::decode(&bytes), Err(CredentialError::BadMagic));
    }

    #[test]
    fn decode_rejects_unsupported_version() {
        let mut bytes = Credential::new(2000, 1, 1, 276).encode();
        bytes[OFF_VERSION] = 2;
        assert_eq!(
            Credential::decode(&bytes),
            Err(CredentialError::UnsupportedVersion(2))
        );
    }
}
