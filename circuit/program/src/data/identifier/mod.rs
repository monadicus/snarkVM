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

use console::ConsoleField;
#[cfg(test)]
use snarkvm_circuit_types::environment::assert_scope;

mod equal;
mod from_bits;
mod from_field;
mod size_in_bits;
mod to_bits;
mod to_field;

use snarkvm_circuit_types::{
    environment::{prelude::*, Circuit},
    Boolean,
    Field,
    U8,
};
use snarkvm_utilities::ToBits as TB;

/// An identifier is an **immutable** UTF-8 string,
/// represented as a **constant** field element in the circuit.
///
/// # Requirements
/// The identifier must not be an empty string.
/// The identifier must not start with a number.
/// The identifier must be alphanumeric, and may include underscores.
/// The identifier must not consist solely of underscores.
/// The identifier must fit within the data capacity of a base field element.
#[derive(Clone)]
pub struct Identifier(Field, u8); // Number of bytes in the identifier.

#[cfg(console)]
impl Inject for Identifier {
    type Primitive = console::Identifier;

    /// Initializes a new identifier from a string.
    /// Note: Identifiers are always `Mode::Constant`.
    fn new(_: Mode, identifier: Self::Primitive) -> Self {
        // Convert the identifier to a string to check its validity.
        let identifier = identifier.to_string();

        // Note: The string bytes themselves are **not** little-endian. Rather, they are order-preserving
        // for reconstructing the string when recovering the field element back into bytes.
        let field = Field::from_bits_le(&Vec::<Boolean>::constant(identifier.to_bits_le()));

        // Return the identifier.
        Self(field, identifier.len() as u8)
    }
}

#[cfg(console)]
impl Eject for Identifier {
    type Primitive = console::Identifier;

    /// Ejects the mode of the identifier.
    fn eject_mode(&self) -> Mode {
        debug_assert!(self.0.eject_mode() == Mode::Constant, "Identifier::eject_mode - Mode must be 'Constant'");
        Mode::Constant
    }

    /// Ejects the identifier as a string.
    fn eject_value(&self) -> Self::Primitive {
        match console::FromField::from_field(&self.0.eject_value()) {
            Ok(identifier) => identifier,
            Err(error) => Circuit::halt(format!("Failed to convert an identifier to a string: {error}")),
        }
    }
}

#[cfg(console)]
impl Parser for Identifier {
    /// Parses a UTF-8 string into an identifier.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the identifier from the string.
        let (string, identifier) = console::Identifier::parse(string)?;

        Ok((string, Identifier::constant(identifier)))
    }
}

#[cfg(console)]
impl FromStr for Identifier {
    type Err = Error;

    /// Parses a UTF-8 string into an identifier.
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
impl Debug for Identifier {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[cfg(console)]
impl Display for Identifier {
    /// Prints the identifier as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.eject_value())
    }
}

impl Eq for Identifier {}

impl PartialEq for Identifier {
    /// Implements the `Eq` trait for the identifier.
    fn eq(&self, other: &Self) -> bool {
        self.0.eject_value() == other.0.eject_value()
    }
}

impl core::hash::Hash for Identifier {
    /// Implements the `Hash` trait for the identifier.
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.0.eject_value().hash(state);
    }
}

impl From<Identifier> for LinearCombination<ConsoleField> {
    /// Note: Identifier is always `Mode::Constant`.
    fn from(identifier: Identifier) -> Self {
        From::from(&identifier)
    }
}

impl From<&Identifier> for LinearCombination<ConsoleField> {
    /// Note: Identifier is always `Mode::Constant`.
    fn from(identifier: &Identifier) -> Self {
        LinearCombination::from(&identifier.0)
    }
}

#[cfg(all(test, console))]
pub(crate) mod tests {
    use super::*;
    use console::{ConsoleField, Rng, TestRng};

    use anyhow::{bail, Result};
    use core::str::FromStr;
    use rand::distributions::Alphanumeric;

    /// Samples a random identifier.
    pub(crate) fn sample_console_identifier() -> Result<console::Identifier> {
        // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
        let string = sample_console_identifier_as_string()?;
        // Return the identifier.
        console::Identifier::from_str(&string)
    }

    /// Samples a random identifier as a string.
    pub(crate) fn sample_console_identifier_as_string() -> Result<String> {
        // Initialize a test RNG.
        let rng = &mut TestRng::default();
        // Sample a random fixed-length alphanumeric string, that always starts with an alphabetic character.
        let string = "a".to_string()
            + &rng
                .sample_iter(&Alphanumeric)
                .take(ConsoleField::size_in_data_bits() / (8 * 2))
                .map(char::from)
                .collect::<String>();
        // Ensure identifier fits within the data capacity of the base field.
        let max_bytes = ConsoleField::size_in_data_bits() / 8; // Note: This intentionally rounds down.
        match string.len() <= max_bytes {
            // Return the identifier.
            true => Ok(string),
            false => bail!("Identifier exceeds the maximum capacity allowed"),
        }
    }

    /// Samples a random identifier as a string.
    pub(crate) fn sample_lowercase_console_identifier_as_string() -> Result<String> {
        // Sample a random identifier.
        let string = sample_console_identifier_as_string()?;
        // Return the identifier as lowercase.
        Ok(string.to_lowercase())
    }

    #[test]
    fn test_identifier_parse() -> Result<()> {
        let candidate = Identifier::parse("foo_bar").unwrap();
        assert_eq!("", candidate.0);
        assert_eq!(Identifier::constant("foo_bar".try_into()?).eject(), candidate.1.eject());
        Ok(())
    }

    #[test]
    fn test_identifier_parse_fails() -> Result<()> {
        // Must be alphanumeric or underscore.
        let identifier = Identifier::parse("foo_bar~baz").unwrap();
        assert_eq!(("~baz", Identifier::from_str("foo_bar")?.eject()), (identifier.0, identifier.1.eject()));
        let identifier = Identifier::parse("foo_bar-baz").unwrap();
        assert_eq!(("-baz", Identifier::from_str("foo_bar")?.eject()), (identifier.0, identifier.1.eject()));

        // Must not be solely underscores.
        assert!(Identifier::parse("_").is_err());
        assert!(Identifier::parse("__").is_err());
        assert!(Identifier::parse("___").is_err());
        assert!(Identifier::parse("____").is_err());

        // Must not start with a number.
        assert!(Identifier::parse("1").is_err());
        assert!(Identifier::parse("2").is_err());
        assert!(Identifier::parse("3").is_err());
        assert!(Identifier::parse("1foo").is_err());
        assert!(Identifier::parse("12").is_err());
        assert!(Identifier::parse("111").is_err());

        // Must fit within the data capacity of a base field element.
        let identifier = Identifier::parse("foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy");
        assert!(identifier.is_err());
        Ok(())
    }

    #[test]
    fn test_identifier_display() -> Result<()> {
        let identifier = Identifier::from_str("foo_bar")?;
        assert_eq!("foo_bar", format!("{identifier}"));
        Ok(())
    }

    #[test]
    fn test_identifier_bits() -> Result<()> {
        let identifier = Identifier::from_str("foo_bar")?;
        assert_eq!(
            identifier.to_bits_le().eject(),
            Identifier::from_bits_le(&identifier.to_bits_le()).to_bits_le().eject()
        );
        assert_eq!(
            identifier.to_bits_be().eject(),
            Identifier::from_bits_be(&identifier.to_bits_be()).to_bits_be().eject()
        );
        Ok(())
    }
}
