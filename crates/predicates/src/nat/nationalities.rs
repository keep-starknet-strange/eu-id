/// ISO 3166-1 alpha-2 codes assigned by the current product profile.
///
/// This is the sole country-code source used by statement validation, witness
/// construction, and the fixed signed-nationality lookup table.
pub const ASSIGNED_ISO_ALPHA2: [[u8; 2]; 249] = [
    *b"AD", *b"AE", *b"AF", *b"AG", *b"AI", *b"AL", *b"AM", *b"AO", *b"AQ", *b"AR", *b"AS", *b"AT",
    *b"AU", *b"AW", *b"AX", *b"AZ", *b"BA", *b"BB", *b"BD", *b"BE", *b"BF", *b"BG", *b"BH", *b"BI",
    *b"BJ", *b"BL", *b"BM", *b"BN", *b"BO", *b"BQ", *b"BR", *b"BS", *b"BT", *b"BV", *b"BW", *b"BY",
    *b"BZ", *b"CA", *b"CC", *b"CD", *b"CF", *b"CG", *b"CH", *b"CI", *b"CK", *b"CL", *b"CM", *b"CN",
    *b"CO", *b"CR", *b"CU", *b"CV", *b"CW", *b"CX", *b"CY", *b"CZ", *b"DE", *b"DJ", *b"DK", *b"DM",
    *b"DO", *b"DZ", *b"EC", *b"EE", *b"EG", *b"EH", *b"ER", *b"ES", *b"ET", *b"FI", *b"FJ", *b"FK",
    *b"FM", *b"FO", *b"FR", *b"GA", *b"GB", *b"GD", *b"GE", *b"GF", *b"GG", *b"GH", *b"GI", *b"GL",
    *b"GM", *b"GN", *b"GP", *b"GQ", *b"GR", *b"GS", *b"GT", *b"GU", *b"GW", *b"GY", *b"HK", *b"HM",
    *b"HN", *b"HR", *b"HT", *b"HU", *b"ID", *b"IE", *b"IL", *b"IM", *b"IN", *b"IO", *b"IQ", *b"IR",
    *b"IS", *b"IT", *b"JE", *b"JM", *b"JO", *b"JP", *b"KE", *b"KG", *b"KH", *b"KI", *b"KM", *b"KN",
    *b"KP", *b"KR", *b"KW", *b"KY", *b"KZ", *b"LA", *b"LB", *b"LC", *b"LI", *b"LK", *b"LR", *b"LS",
    *b"LT", *b"LU", *b"LV", *b"LY", *b"MA", *b"MC", *b"MD", *b"ME", *b"MF", *b"MG", *b"MH", *b"MK",
    *b"ML", *b"MM", *b"MN", *b"MO", *b"MP", *b"MQ", *b"MR", *b"MS", *b"MT", *b"MU", *b"MV", *b"MW",
    *b"MX", *b"MY", *b"MZ", *b"NA", *b"NC", *b"NE", *b"NF", *b"NG", *b"NI", *b"NL", *b"NO", *b"NP",
    *b"NR", *b"NU", *b"NZ", *b"OM", *b"PA", *b"PE", *b"PF", *b"PG", *b"PH", *b"PK", *b"PL", *b"PM",
    *b"PN", *b"PR", *b"PS", *b"PT", *b"PW", *b"PY", *b"QA", *b"RE", *b"RO", *b"RS", *b"RU", *b"RW",
    *b"SA", *b"SB", *b"SC", *b"SD", *b"SE", *b"SG", *b"SH", *b"SI", *b"SJ", *b"SK", *b"SL", *b"SM",
    *b"SN", *b"SO", *b"SR", *b"SS", *b"ST", *b"SV", *b"SX", *b"SY", *b"SZ", *b"TC", *b"TD", *b"TF",
    *b"TG", *b"TH", *b"TJ", *b"TK", *b"TL", *b"TM", *b"TN", *b"TO", *b"TR", *b"TT", *b"TV", *b"TW",
    *b"TZ", *b"UA", *b"UG", *b"UM", *b"US", *b"UY", *b"UZ", *b"VA", *b"VC", *b"VE", *b"VG", *b"VI",
    *b"VN", *b"VU", *b"WF", *b"WS", *b"YE", *b"YT", *b"ZA", *b"ZM", *b"ZW",
];

/// User-assigned nationality codes accepted in signed mdoc arrays.
///
/// They are valid private signed values, but never public policy members.
pub const SIGNED_USER_ASSIGNED_ALPHA2: [[u8; 2]; 2] = [*b"QU", *b"QS"];

pub const fn pack_alpha2(code: [u8; 2]) -> u32 {
    u16::from_be_bytes(code) as u32
}

pub fn assigned_iso_alpha2_codes() -> &'static [[u8; 2]] {
    &ASSIGNED_ISO_ALPHA2
}

pub fn is_assigned_iso_alpha2(code: u32) -> bool {
    ASSIGNED_ISO_ALPHA2
        .iter()
        .any(|&assigned| pack_alpha2(assigned) == code)
}

pub fn is_valid_signed_alpha2(code: u32) -> bool {
    is_assigned_iso_alpha2(code)
        || SIGNED_USER_ASSIGNED_ALPHA2
            .iter()
            .any(|&assigned| pack_alpha2(assigned) == code)
}

pub fn signed_alpha2_codes() -> impl Iterator<Item = u32> {
    let mut codes = ASSIGNED_ISO_ALPHA2
        .iter()
        .chain(&SIGNED_USER_ASSIGNED_ALPHA2)
        .copied()
        .map(pack_alpha2)
        .collect::<Vec<_>>();
    codes.sort_unstable();
    codes.into_iter()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn assigned_set_is_exact_and_has_no_duplicates() {
        let assigned = ASSIGNED_ISO_ALPHA2.iter().copied().collect::<HashSet<_>>();
        assert_eq!(assigned.len(), 249);
        assert!(ASSIGNED_ISO_ALPHA2.windows(2).all(|pair| pair[0] < pair[1]));

        let exhaustive_count = (b'A'..=b'Z')
            .flat_map(|first| (b'A'..=b'Z').map(move |second| [first, second]))
            .filter(|&code| is_assigned_iso_alpha2(pack_alpha2(code)))
            .count();
        assert_eq!(exhaustive_count, 249);

        for excluded in [*b"QU", *b"QS", *b"XK", *b"ZZ"] {
            assert!(!is_assigned_iso_alpha2(pack_alpha2(excluded)));
        }
        for user_assigned in SIGNED_USER_ASSIGNED_ALPHA2 {
            assert!(is_valid_signed_alpha2(pack_alpha2(user_assigned)));
        }
        for invalid in [*b"XK", *b"ZZ", *b"zz"] {
            assert!(!is_valid_signed_alpha2(pack_alpha2(invalid)));
        }
    }
}
