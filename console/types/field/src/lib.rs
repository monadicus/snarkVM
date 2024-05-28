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

mod arithmetic;
mod bitwise;
mod bytes;
mod compare;
mod from_bits;
mod one;
mod parse;
mod random;
mod serialize;
mod size_in_bits;
mod size_in_bytes;
mod to_bits;
mod zero;

pub use snarkvm_console_network_environment::prelude::*;
pub use snarkvm_console_types_boolean::Boolean;

use zeroize::Zeroize;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Zeroize)]
pub struct Field {
    /// The underlying field element.
    field: ConsoleField,
}

impl FieldTrait for Field {}

impl Field {
    /// The field size in bits.
    pub const SIZE_IN_BITS: usize = ConsoleField::SIZE_IN_BITS;
    /// The field size in bytes.
    pub const SIZE_IN_BYTES: usize = (ConsoleField::SIZE_IN_BITS + 7) / 8;
    /// The field capacity for data bits.
    pub const SIZE_IN_DATA_BITS: usize = ConsoleField::SIZE_IN_DATA_BITS;

    /// Initializes a new field.
    pub const fn new(field: ConsoleField) -> Self {
        Self { field }
    }

    /// Initializes a new field as a domain separator.
    pub fn new_domain_separator(domain: &str) -> Self {
        Self::new(ConsoleField::from_bytes_le_mod_order(domain.as_bytes()))
    }

    /// Initializes a new field from a `u8`.
    pub fn from_u8(value: u8) -> Self {
        Self { field: ConsoleField::from(value as u128) }
    }

    /// Initializes a new field from a `u16`.
    pub fn from_u16(value: u16) -> Self {
        Self { field: ConsoleField::from(value as u128) }
    }

    /// Initializes a new field from a `u32`.
    pub fn from_u32(value: u32) -> Self {
        Self { field: ConsoleField::from(value as u128) }
    }

    /// Initializes a new field from a `u64`.
    pub fn from_u64(value: u64) -> Self {
        Self { field: ConsoleField::from(value as u128) }
    }

    /// Initializes a new field from a `u128`.
    pub fn from_u128(value: u128) -> Self {
        Self { field: ConsoleField::from(value) }
    }

    /// Returns `1 * 2^{-1}`.
    pub fn half() -> Self {
        Self { field: ConsoleField::half() }
    }
}

impl Default for Field {
    /// Returns the default field element.
    fn default() -> Self {
        Self::zero()
    }
}

impl TypeName for Field {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "field"
    }
}

impl Deref for Field {
    type Target = ConsoleField;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.field
    }
}

impl DerefMut for Field {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.field
    }
}
