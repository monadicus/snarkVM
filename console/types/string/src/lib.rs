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

#![cfg_attr(test, allow(clippy::assertions_on_result_states))]
#![warn(clippy::cast_possible_truncation)]

mod bitwise;
mod bytes;
mod parse;
mod random;
mod serialize;

pub use snarkvm_console_network_environment::prelude::*;
pub use snarkvm_console_types_boolean::Boolean;
pub use snarkvm_console_types_field::Field;
pub use snarkvm_console_types_integers::Integer;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct StringType {
    /// The underlying string.
    string: String,
}

impl StringTrait for StringType {}

impl StringType {
    /// Initializes a new string.
    pub fn new(string: &str) -> Self {
        // Ensure the string is within the allowed capacity.
        let num_bytes = string.len();
        match num_bytes <= Console::MAX_STRING_BYTES as usize {
            true => Self { string: string.to_string() },
            false => Console::halt(format!("Attempted to allocate a string of size {num_bytes}")),
        }
    }
}

impl TypeName for StringType {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "string"
    }
}

impl Deref for StringType {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.string.as_str()
    }
}
