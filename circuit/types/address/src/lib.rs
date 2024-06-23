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
#![cfg_attr(test, allow(clippy::assertions_on_result_states))]

mod helpers;

mod compare;
mod equal;
mod ternary;

use console::ConsoleField;
#[cfg(test)]
use console::{TestRng, Uniform};
#[cfg(test)]
use snarkvm_circuit_environment::{assert_count, assert_output_mode, assert_scope, count, output_mode};

use snarkvm_circuit_environment::prelude::*;
use snarkvm_circuit_types_boolean::Boolean;
use snarkvm_circuit_types_field::Field;
use snarkvm_circuit_types_group::Group;
use snarkvm_circuit_types_scalar::Scalar;

use core::str::FromStr;

#[derive(Clone)]
pub struct Address(Group);

impl AddressTrait for Address {}

impl Address {
    /// Initializes the zero address.
    #[inline]
    pub fn zero() -> Self {
        Self(Group::zero())
    }
}

#[cfg(console)]
impl Inject for Address {
    type Primitive = console::Address;

    /// Initializes a new instance of an address.
    fn new(mode: Mode, address: Self::Primitive) -> Self {
        Self(Group::new(mode, *address))
    }
}

#[cfg(console)]
impl Eject for Address {
    type Primitive = console::Address;

    /// Ejects the mode of the address.
    fn eject_mode(&self) -> Mode {
        self.0.eject_mode()
    }

    /// Ejects the address.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::new(self.0.eject_value())
    }
}

#[cfg(console)]
impl Parser for Address {
    /// Parses a string into an address circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the address from the string.
        let (string, address) = console::Address::parse(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;

        match mode {
            Some((_, mode)) => Ok((string, Address::new(mode, address))),
            None => Ok((string, Address::new(Mode::Constant, address))),
        }
    }
}

#[cfg(console)]
impl FromStr for Address {
    type Err = Error;

    /// Parses a string into a address.
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
impl TypeName for Address {
    /// Returns the type name of the circuit as a string.
    #[inline]
    fn type_name() -> &'static str {
        console::Address::type_name()
    }
}

#[cfg(console)]
impl Debug for Address {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[cfg(console)]
impl Display for Address {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.eject_value(), self.eject_mode())
    }
}

impl From<Address> for LinearCombination<ConsoleField> {
    fn from(address: Address) -> Self {
        From::from(&address)
    }
}

impl From<&Address> for LinearCombination<ConsoleField> {
    fn from(address: &Address) -> Self {
        From::from(address.to_field())
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;

    #[test]
    fn test_address_parse() {
        let expected = "aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.public";
        let address = Address::parse(expected).unwrap().1;
        assert_eq!(expected, &format!("{address}"));
    }
}
