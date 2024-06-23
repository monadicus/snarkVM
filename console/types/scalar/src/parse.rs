// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl Parser for Scalar {
    /// Parses a string into a scalar circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the optional negative sign '-' from the string.
        let (string, negation) = map(opt(tag("-")), |neg: Option<&str>| neg.is_some())(string)?;
        // Parse the digits from the string.
        let (string, primitive) = recognize(many1(terminated(one_of("0123456789"), many0(char('_')))))(string)?;
        // Parse the value from the string.
        let (string, value): (&str, ConsoleScalar) =
            map_res(tag(Self::type_name()), |_| primitive.replace('_', "").parse())(string)?;
        // Negate the value if the negative sign was present.
        let value = match negation {
            true => -value,
            false => value,
        };

        Ok((string, Scalar::new(value)))
    }
}

impl FromStr for Scalar {
    type Err = Error;

    /// Parses a string into a scalar.
    #[inline]
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl Debug for Scalar {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for Scalar {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}{}", self.scalar, Self::type_name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ITERATIONS: u64 = 10_000;

    #[test]
    fn test_parse() -> Result<()> {
        let rng = &mut TestRng::default();

        // Ensure empty value fails.
        assert!(Scalar::parse(Scalar::type_name()).is_err());
        assert!(Scalar::parse("").is_err());

        for _ in 0..ITERATIONS {
            // Sample a random value.
            let scalar: ConsoleScalar = Uniform::rand(rng);

            let expected = format!("{}{}", scalar, Scalar::type_name());
            let (remainder, candidate) = Scalar::parse(&expected).unwrap();
            assert_eq!(format!("{expected}"), candidate.to_string());
            assert_eq!("", remainder);
        }
        Ok(())
    }

    #[test]
    fn test_display() {
        /// Attempts to construct a scalar from the given element,
        /// format it in display mode, and recover a scalar from it.
        fn check_display(element: ConsoleScalar) {
            let candidate = Scalar::new(element);
            assert_eq!(format!("{element}{}", Scalar::type_name()), format!("{candidate}"));

            let candidate_recovered = Scalar::from_str(&format!("{candidate}")).unwrap();
            assert_eq!(candidate, candidate_recovered);
        }

        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            let element = Uniform::rand(&mut rng);

            check_display(element);
        }
    }

    #[test]
    fn test_display_zero() {
        let zero = ConsoleScalar::zero();

        let candidate = Scalar::new(zero);
        assert_eq!("0scalar", &format!("{candidate}"));
    }

    #[test]
    fn test_display_one() {
        let one = ConsoleScalar::one();

        let candidate = Scalar::new(one);
        assert_eq!("1scalar", &format!("{candidate}"));
    }

    #[test]
    fn test_display_two() {
        let one = ConsoleScalar::one();
        let two = one + one;

        let candidate = Scalar::new(two);
        assert_eq!("2scalar", &format!("{candidate}"));
    }
}
