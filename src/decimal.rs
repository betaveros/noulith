use num::Zero;
use num::bigint::BigInt;
use num::rational::Ratio;

fn apply_exp10(base: BigInt, exponent: i32) -> Ratio<BigInt> {
    if exponent >= 0 {
        Ratio::from(base * BigInt::from(10).pow(exponent as u32))
    } else {
        Ratio::new(base, BigInt::from(10).pow((-exponent) as u32))
    }
}

fn parse_decimal_exactly(s: &str) -> Option<Ratio<BigInt>> {
    // scientific notation
    let (base_str, exponent) = if let Some(e_pos) = s.find(['e', 'E']) {
        let base_part = &s[..e_pos];
        let exp_part = &s[e_pos + 1..];

        let exp: i32 = exp_part.parse().ok()?;
        (base_part, exp)
    } else {
        (s, 0)
    };

    // decimal point
    if let Some(dot_pos) = base_str.find('.') {
        let integer_part = &base_str[..dot_pos];
        let fractional_part = &base_str[dot_pos + 1..];
        // reject "." (but "1." and ".1" are both fine)
        if integer_part.is_empty() && fractional_part.is_empty() {
            return None;
        }
        // reject e.g. "1.-1"
        if !fractional_part.chars().all(|c| c.is_ascii_digit()) {
            return None;
        }

        let integer_digits: BigInt = if integer_part.is_empty() {
            BigInt::from(0)
        } else {
            integer_part.parse().ok()?
        };
        let fractional_digits: BigInt = if fractional_part.is_empty() {
            BigInt::from(0)
        } else {
            fractional_part.parse().ok()?
        };

        let decimal_places = fractional_part.len();
        let base_value =
            integer_digits * BigInt::from(10).pow(decimal_places as u32) + fractional_digits;

        Some(apply_exp10(base_value, exponent - (decimal_places as i32)))
    } else {
        Some(apply_exp10(base_str.parse().ok()?, exponent))
    }
}

pub fn parse_rational_exactly(s: &str) -> Option<Ratio<BigInt>> {
    let s = s.trim();
    if let Some(slash_pos) = s.find('/') {
        let numerator_str = s[..slash_pos].trim();
        let denominator_str = s[slash_pos + 1..].trim();

        let numerator = parse_decimal_exactly(numerator_str)?;
        let denominator = parse_decimal_exactly(denominator_str)?;

        if denominator.is_zero() {
            None
        } else {
            Some(numerator / denominator)
        }
    } else {
        parse_decimal_exactly(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_as_rational() {
        assert_eq!(
            parse_rational_exactly("42"),
            Some(Ratio::from(BigInt::from(42)))
        );
        assert_eq!(
            parse_rational_exactly("-42"),
            Some(Ratio::from(BigInt::from(-42)))
        );
        assert_eq!(
            parse_rational_exactly("+42"),
            Some(Ratio::from(BigInt::from(42)))
        );

        assert_eq!(
            parse_rational_exactly("1/2"),
            Some(Ratio::new(BigInt::from(1), BigInt::from(2)))
        );
        assert_eq!(
            parse_rational_exactly("-3/4"),
            Some(Ratio::new(BigInt::from(-3), BigInt::from(4)))
        );

        assert_eq!(
            parse_rational_exactly("0.5"),
            Some(Ratio::new(BigInt::from(1), BigInt::from(2)))
        );
        assert_eq!(
            parse_rational_exactly("3.14"),
            Some(Ratio::new(BigInt::from(314), BigInt::from(100)))
        );
        assert_eq!(
            parse_rational_exactly(".25"),
            Some(Ratio::new(BigInt::from(1), BigInt::from(4)))
        );

        assert_eq!(
            parse_rational_exactly("1e3"),
            Some(Ratio::from(BigInt::from(1000)))
        );
        assert_eq!(
            parse_rational_exactly("1.5e2"),
            Some(Ratio::from(BigInt::from(150)))
        );
        assert_eq!(
            parse_rational_exactly("2e-1"),
            Some(Ratio::new(BigInt::from(1), BigInt::from(5)))
        );

        assert_eq!(
            parse_rational_exactly("1.23e-2"),
            Some(Ratio::new(BigInt::from(123), BigInt::from(10000)))
        );

        assert_eq!(parse_rational_exactly(""), None);
        assert_eq!(parse_rational_exactly("abc"), None);
        assert_eq!(parse_rational_exactly("1/0"), None);
    }
}
