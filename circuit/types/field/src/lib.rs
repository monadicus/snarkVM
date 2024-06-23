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

#![forbid(unsafe_code)]
#![allow(clippy::too_many_arguments)]
#![cfg_attr(test, allow(clippy::assertions_on_result_states))]

mod helpers;

pub mod add;
pub mod compare;
pub mod div;
pub mod div_unchecked;
pub mod double;
pub mod equal;
pub mod inverse;
pub mod mul;
pub mod neg;
pub mod pow;
pub mod square;
pub mod square_root;
pub mod sub;
pub mod ternary;

use console::ConsoleField;
#[cfg(test)]
use console::{TestRng, Uniform};
#[cfg(test)]
use snarkvm_circuit_environment::{assert_count, assert_output_mode, assert_scope, count, output_mode};

use snarkvm_circuit_environment::{prelude::*, Circuit};
use snarkvm_circuit_types_boolean::Boolean;

#[derive(Clone)]
pub struct Field {
    /// The linear combination contains the primary representation of the field.
    linear_combination: LinearCombination<ConsoleField>,
    /// An optional secondary representation in little-endian bits is provided,
    /// so that calls to `ToBits` only incur constraint costs once.
    bits_le: OnceCell<Vec<Boolean>>,
}

impl FieldTrait for Field {}

impl Default for Field {
    /// Returns the default field element.
    fn default() -> Self {
        Self::zero()
    }
}

#[cfg(console)]
impl Inject for Field {
    type Primitive = console::Field;

    /// Initializes a field circuit from a console field.
    fn new(mode: Mode, field: Self::Primitive) -> Self {
        Self { linear_combination: Circuit::new_variable(mode, *field).into(), bits_le: Default::default() }
    }
}

#[cfg(console)]
impl Eject for Field {
    type Primitive = console::Field;

    /// Ejects the mode of the field circuit.
    fn eject_mode(&self) -> Mode {
        self.linear_combination.mode()
    }

    /// Ejects the field circuit as a console field.
    fn eject_value(&self) -> Self::Primitive {
        console::Field::new(self.linear_combination.value())
    }
}

#[cfg(console)]
impl Parser for Field {
    /// Parses a string into a field circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the field from the string.
        let (string, field) = console::Field::parse(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;

        match mode {
            Some((_, mode)) => Ok((string, Field::new(mode, field))),
            None => Ok((string, Field::new(Mode::Constant, field))),
        }
    }
}

#[cfg(console)]
impl FromStr for Field {
    type Err = Error;

    /// Parses a string into a field circuit.
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

#[cfg(console)]
impl TypeName for Field {
    /// Returns the type name of the circuit as a string.
    #[inline]
    fn type_name() -> &'static str {
        console::Field::type_name()
    }
}

#[cfg(console)]
impl Debug for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[cfg(console)]
impl Display for Field {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.eject_value(), self.eject_mode())
    }
}

impl From<LinearCombination<ConsoleField>> for Field {
    fn from(linear_combination: LinearCombination<ConsoleField>) -> Self {
        Self { linear_combination, bits_le: Default::default() }
    }
}

impl From<&LinearCombination<ConsoleField>> for Field {
    fn from(linear_combination: &LinearCombination<ConsoleField>) -> Self {
        From::from(linear_combination.clone())
    }
}

impl From<Field> for LinearCombination<ConsoleField> {
    fn from(field: Field) -> Self {
        From::from(&field)
    }
}

impl From<&Field> for LinearCombination<ConsoleField> {
    fn from(field: &Field) -> Self {
        field.linear_combination.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ITERATIONS: u64 = 10_000;

    /// Attempts to construct a field from the given element and mode,
    /// format it in display mode, and recover a field from it.
    fn check_display(mode: Mode, element: console::Field) -> Result<()> {
        let candidate = Field::new(mode, element);
        assert_eq!(format!("{element}.{mode}"), format!("{candidate}"));

        let candidate_recovered = Field::from_str(&format!("{candidate}"))?;
        assert_eq!(candidate.eject_value(), candidate_recovered.eject_value());
        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            let element = Uniform::rand(&mut rng);

            // Constant
            check_display(Mode::Constant, element)?;
            // Public
            check_display(Mode::Public, element)?;
            // Private
            check_display(Mode::Private, element)?;
        }
        Ok(())
    }

    #[test]
    fn test_display_zero() {
        let zero = console::Field::zero();

        // Constant
        let candidate = Field::new(Mode::Constant, zero);
        assert_eq!("0field.constant", &format!("{candidate}"));

        // Public
        let candidate = Field::new(Mode::Public, zero);
        assert_eq!("0field.public", &format!("{candidate}"));

        // Private
        let candidate = Field::new(Mode::Private, zero);
        assert_eq!("0field.private", &format!("{candidate}"));
    }

    #[test]
    fn test_display_one() {
        let one = console::Field::one();

        // Constant
        let candidate = Field::new(Mode::Constant, one);
        assert_eq!("1field.constant", &format!("{candidate}"));

        // Public
        let candidate = Field::new(Mode::Public, one);
        assert_eq!("1field.public", &format!("{candidate}"));

        // Private
        let candidate = Field::new(Mode::Private, one);
        assert_eq!("1field.private", &format!("{candidate}"));
    }

    #[test]
    fn test_display_two() {
        let one = console::Field::one();
        let two = one + one;

        // Constant
        let candidate = Field::new(Mode::Constant, two);
        assert_eq!("2field.constant", &format!("{candidate}"));

        // Public
        let candidate = Field::new(Mode::Public, two);
        assert_eq!("2field.public", &format!("{candidate}"));

        // Private
        let candidate = Field::new(Mode::Private, two);
        assert_eq!("2field.private", &format!("{candidate}"));
    }

    #[test]
    fn test_parser() {
        type Primitive = ConsoleField;

        // Constant

        let (_, candidate) = Field::parse("5field").unwrap();
        assert_eq!(Primitive::from_str("5field").unwrap(), *candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Field::parse("5_field").unwrap();
        assert_eq!(Primitive::from_str("5field").unwrap(), *candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Field::parse("1_5_field").unwrap();
        assert_eq!(Primitive::from_str("15field").unwrap(), *candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Field::parse("5field.constant").unwrap();
        assert_eq!(Primitive::from_str("5field").unwrap(), *candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Field::parse("5_field.constant").unwrap();
        assert_eq!(Primitive::from_str("5field").unwrap(), *candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Field::parse("1_5_field.constant").unwrap();
        assert_eq!(Primitive::from_str("15field").unwrap(), *candidate.eject_value());
        assert!(candidate.is_constant());

        // Public

        let (_, candidate) = Field::parse("5field.public").unwrap();
        assert_eq!(Primitive::from_str("5field").unwrap(), *candidate.eject_value());
        assert!(candidate.is_public());

        let (_, candidate) = Field::parse("5_field.public").unwrap();
        assert_eq!(Primitive::from_str("5field").unwrap(), *candidate.eject_value());
        assert!(candidate.is_public());

        let (_, candidate) = Field::parse("1_5_field.public").unwrap();
        assert_eq!(Primitive::from_str("15field").unwrap(), *candidate.eject_value());
        assert!(candidate.is_public());

        // Private

        let (_, candidate) = Field::parse("5field.private").unwrap();
        assert_eq!(Primitive::from_str("5field").unwrap(), *candidate.eject_value());
        assert!(candidate.is_private());

        let (_, candidate) = Field::parse("5_field.private").unwrap();
        assert_eq!(Primitive::from_str("5field").unwrap(), *candidate.eject_value());
        assert!(candidate.is_private());

        let (_, candidate) = Field::parse("1_5_field.private").unwrap();
        assert_eq!(Primitive::from_str("15field").unwrap(), *candidate.eject_value());
        assert!(candidate.is_private());

        // Random

        let mut rng = TestRng::default();

        for mode in [Mode::Constant, Mode::Public, Mode::Private] {
            for _ in 0..ITERATIONS {
                let value = Uniform::rand(&mut rng);
                let expected = Field::new(mode, value);

                let (_, candidate) = Field::parse(&format!("{expected}")).unwrap();
                assert_eq!(expected.eject_value(), candidate.eject_value());
                assert_eq!(mode, candidate.eject_mode());
            }
        }
    }
}
