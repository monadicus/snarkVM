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

pub mod and;
pub mod equal;
pub mod nand;
pub mod nor;
pub mod not;
pub mod or;
pub mod ternary;
pub mod xor;

use console::ConsoleField;
#[cfg(test)]
use snarkvm_circuit_environment::{assert_count, assert_output_mode, assert_scope, count, output_mode};

use snarkvm_circuit_environment::{prelude::*, Circuit};

use core::ops::Deref;

#[derive(Clone)]
pub struct Boolean(LinearCombination<ConsoleField>);

impl BooleanTrait for Boolean {}

impl Boolean {
    /// Initializes a boolean from a variable.
    ///
    /// Note: This method does **not** check the booleanity of the variable.
    pub fn from_variable(var: Variable<ConsoleField>) -> Self {
        // In debug-mode only, sanity check the booleanity of the variable.
        debug_assert!(var.value().is_zero() || var.value().is_one(), "Boolean variable is not well-formed");
        // Return the boolean.
        Boolean(var.into())
    }
}

#[cfg(console)]
impl Inject for Boolean {
    type Primitive = bool;

    /// Initializes a new instance of a boolean from a primitive boolean value.
    fn new(mode: Mode, value: Self::Primitive) -> Self {
        let variable = Circuit::new_variable(mode, match value {
            true => ConsoleField::one(),
            false => ConsoleField::zero(),
        });

        // Ensure (1 - a) * a = 0
        // `a` must be either 0 or 1.
        Circuit::enforce(|| (Circuit::one() - &variable, &variable, Circuit::zero()));

        Self(variable.into())
    }

    /// Initializes a constant boolean circuit from a primitive boolean value.
    fn constant(value: Self::Primitive) -> Self {
        match value {
            true => Self(Circuit::one()),
            false => Self(Circuit::zero()),
        }
    }
}

#[cfg(console)]
impl Eject for Boolean {
    type Primitive = bool;

    /// Ejects the mode of the boolean.
    fn eject_mode(&self) -> Mode {
        // Perform a software-level safety check that the boolean is well-formed.
        match self.0.is_boolean_type() {
            true => self.0.mode(),
            false => Circuit::halt("Boolean variable is not well-formed"),
        }
    }

    /// Ejects the boolean as a constant boolean value.
    fn eject_value(&self) -> Self::Primitive {
        let value = self.0.value();
        debug_assert!(value.is_zero() || value.is_one());
        value.is_one()
    }
}

#[cfg(console)]
impl Parser for Boolean {
    /// Parses a string into a boolean circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the boolean from the string.
        let (string, boolean) = console::Boolean::parse(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;

        match mode {
            Some((_, mode)) => Ok((string, Boolean::new(mode, *boolean))),
            None => Ok((string, Boolean::new(Mode::Constant, *boolean))),
        }
    }
}

#[cfg(console)]
impl FromStr for Boolean {
    type Err = Error;

    /// Parses a string into a boolean.
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
impl TypeName for Boolean {
    /// Returns the type name of the circuit as a string.
    #[inline]
    fn type_name() -> &'static str {
        console::Boolean::type_name()
    }
}

#[cfg(console)]
impl Debug for Boolean {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[cfg(console)]
impl Display for Boolean {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.eject_value(), self.eject_mode())
    }
}

impl Deref for Boolean {
    type Target = LinearCombination<ConsoleField>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<Boolean> for LinearCombination<ConsoleField> {
    fn from(boolean: Boolean) -> Self {
        boolean.0
    }
}

impl From<&Boolean> for LinearCombination<ConsoleField> {
    fn from(boolean: &Boolean) -> Self {
        boolean.0.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    #[test]
    fn test_new_constant() {
        Circuit::scope("test_new_constant", || {
            let candidate = Boolean::new(Mode::Constant, false);
            assert!(!candidate.eject_value()); // false
            assert_scope!(1, 0, 0, 0);

            let candidate = Boolean::new(Mode::Constant, true);
            assert!(candidate.eject_value()); // true
            assert_scope!(2, 0, 0, 0);
        });
    }

    #[test]
    fn test_new_public() {
        Circuit::scope("test_new_public", || {
            let candidate = Boolean::new(Mode::Public, false);
            assert!(!candidate.eject_value()); // false
            assert_scope!(0, 1, 0, 1);

            let candidate = Boolean::new(Mode::Public, true);
            assert!(candidate.eject_value()); // true
            assert_scope!(0, 2, 0, 2);
        });
    }

    #[test]
    fn test_new_private() {
        Circuit::scope("test_new_private", || {
            let candidate = Boolean::new(Mode::Private, false);
            assert!(!candidate.eject_value()); // false
            assert_scope!(0, 0, 1, 1);

            let candidate = Boolean::new(Mode::Private, true);
            assert!(candidate.eject_value()); // true
            assert_scope!(0, 0, 2, 2);
        });
    }

    #[test]
    fn test_new_fail() {
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;
        {
            let candidate = Circuit::new_variable(Mode::Constant, two);

            // Ensure `a` is either 0 or 1:
            // (1 - a) * a = 0
            assert!(
                std::panic::catch_unwind(|| Circuit::enforce(|| (
                    Circuit::one() - &candidate,
                    candidate,
                    Circuit::zero()
                )))
                .is_err()
            );
            assert_eq!(0, Circuit::num_constraints());

            Circuit::reset();
        }
        {
            let candidate = Circuit::new_variable(Mode::Public, two);

            // Ensure `a` is either 0 or 1:
            // (1 - a) * a = 0
            Circuit::enforce(|| (Circuit::one() - &candidate, candidate, Circuit::zero()));
            assert!(!Circuit::is_satisfied());

            Circuit::reset();
        }
        {
            let candidate = Circuit::new_variable(Mode::Private, two);

            // Ensure `a` is either 0 or 1:
            // (1 - a) * a = 0
            Circuit::enforce(|| (Circuit::one() - &candidate, candidate, Circuit::zero()));
            assert!(!Circuit::is_satisfied());

            Circuit::reset();
        }
    }

    #[test]
    fn test_parser() {
        let (_, candidate) = Boolean::parse("true").unwrap();
        assert!(candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Boolean::parse("false").unwrap();
        assert!(!candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Boolean::parse("true.constant").unwrap();
        assert!(candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Boolean::parse("false.constant").unwrap();
        assert!(!candidate.eject_value());
        assert!(candidate.is_constant());

        let (_, candidate) = Boolean::parse("true.public").unwrap();
        assert!(candidate.eject_value());
        assert!(candidate.is_public());

        let (_, candidate) = Boolean::parse("false.public").unwrap();
        assert!(!candidate.eject_value());
        assert!(candidate.is_public());

        let (_, candidate) = Boolean::parse("true.private").unwrap();
        assert!(candidate.eject_value());
        assert!(candidate.is_private());

        let (_, candidate) = Boolean::parse("false.private").unwrap();
        assert!(!candidate.eject_value());
        assert!(candidate.is_private());

        for mode in [Mode::Constant, Mode::Public, Mode::Private] {
            for value in [true, false] {
                let expected = Boolean::new(mode, value);

                let (_, candidate) = Boolean::parse(&format!("{expected}")).unwrap();
                assert_eq!(expected.eject_value(), candidate.eject_value());
                assert_eq!(mode, candidate.eject_mode());
            }
        }
    }

    #[test]
    fn test_display() {
        let candidate = Boolean::new(Mode::Constant, false);
        assert_eq!("false.constant", format!("{candidate}"));

        let candidate = Boolean::new(Mode::Constant, true);
        assert_eq!("true.constant", format!("{candidate}"));

        let candidate = Boolean::new(Mode::Public, false);
        assert_eq!("false.public", format!("{candidate}"));

        let candidate = Boolean::new(Mode::Public, true);
        assert_eq!("true.public", format!("{candidate}"));

        let candidate = Boolean::new(Mode::Private, false);
        assert_eq!("false.private", format!("{candidate}"));

        let candidate = Boolean::new(Mode::Private, true);
        assert_eq!("true.private", format!("{candidate}"));
    }
}
