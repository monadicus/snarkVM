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

mod equal;
mod helpers;

#[cfg(test)]
use console::TestRng;
use console::{Console, Environment as ConsoleEnvironment};
#[cfg(test)]
use snarkvm_circuit_environment::assert_scope;

use snarkvm_circuit_environment::{prelude::*, Circuit, Environment};
use snarkvm_circuit_types_boolean::Boolean;
use snarkvm_circuit_types_field::Field;
use snarkvm_circuit_types_integers::U8;

#[derive(Clone)]
pub struct StringType {
    mode: Mode,
    bytes: Vec<U8>,
    size_in_bytes: Field,
}

impl StringTrait for StringType {}

#[cfg(console)]
impl Inject for StringType {
    type Primitive = console::StringType;

    /// Initializes a new instance of a string.
    fn new(mode: Mode, string: Self::Primitive) -> Self {
        // Cast the number of bytes in the 'string' as a field element.
        let num_bytes = console::Field::from_u32(
            u32::try_from(string.len()).unwrap_or_else(|error| Circuit::halt(error.to_string())),
        );

        // "Load-bearing witness allocation - Please do not optimize me." - Pratyush :)

        // Inject the number of bytes as a constant.
        let expected_size_in_bytes = Field::constant(num_bytes);
        // Inject the number of bytes as a witness.
        let size_in_bytes = match mode.is_constant() {
            true => expected_size_in_bytes.clone(),
            false => Field::new(Mode::Private, num_bytes),
        };
        // Ensure the witness matches the constant.
        Circuit::assert_eq(&expected_size_in_bytes, &size_in_bytes);

        Self {
            mode,
            bytes: string.as_bytes().iter().map(|byte| U8::new(mode, console::Integer::new(*byte))).collect(),
            size_in_bytes,
        }
    }
}

#[cfg(console)]
impl Eject for StringType {
    type Primitive = console::StringType;

    /// Ejects the mode of the string.
    fn eject_mode(&self) -> Mode {
        match self.bytes.is_empty() {
            true => self.mode,
            false => self.bytes.eject_mode(),
        }
    }

    /// Ejects the string as a string literal.
    fn eject_value(&self) -> Self::Primitive {
        // Ensure the string is within the allowed capacity.
        let num_bytes = self.bytes.len();
        match num_bytes <= Console::MAX_STRING_BYTES as usize {
            true => console::StringType::new(
                &String::from_utf8(self.bytes.eject_value().into_iter().map(|byte| *byte).collect())
                    .unwrap_or_else(|error| Circuit::halt(format!("Failed to eject a string value: {error}"))),
            ),
            false => Circuit::halt(format!("Attempted to eject a string of size {num_bytes}")),
        }
    }
}

#[cfg(console)]
impl Parser for StringType {
    /// Parses a string into a string circuit.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the content from the string.
        let (string, content) = console::StringType::parse(string)?;
        // Parse the mode from the string.
        let (string, mode) = opt(pair(tag("."), Mode::parse))(string)?;

        match mode {
            Some((_, mode)) => Ok((string, StringType::new(mode, content))),
            None => Ok((string, StringType::new(Mode::Constant, content))),
        }
    }
}

#[cfg(console)]
impl FromStr for StringType {
    type Err = Error;

    /// Parses a string into a string circuit.
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
impl TypeName for StringType {
    /// Returns the type name of the circuit as a string.
    #[inline]
    fn type_name() -> &'static str {
        console::StringType::type_name()
    }
}

#[cfg(console)]
impl Debug for StringType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[cfg(console)]
impl Display for StringType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}", self.eject_value(), self.eject_mode())
    }
}
