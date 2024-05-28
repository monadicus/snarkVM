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
mod from_field;
mod from_field_lossy;
mod from_fields;
mod one;
mod parse;
mod random;
mod serialize;
mod size_in_bits;
mod size_in_bytes;
mod to_bits;
mod to_field;
mod to_fields;
mod to_scalar;
mod zero;

pub use snarkvm_console_network_environment::prelude::*;
pub use snarkvm_console_types_boolean::Boolean;
pub use snarkvm_console_types_field::Field;
pub use snarkvm_console_types_scalar::Scalar;

pub type I8 = Integer<i8>;
pub type I16 = Integer<i16>;
pub type I32 = Integer<i32>;
pub type I64 = Integer<i64>;
pub type I128 = Integer<i128>;

pub type U8 = Integer<u8>;
pub type U16 = Integer<u16>;
pub type U32 = Integer<u32>;
pub type U64 = Integer<u64>;
pub type U128 = Integer<u128>;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Integer<I: IntegerType> {
    /// The underlying integer value.
    integer: I,
}

impl<I: IntegerType> IntegerTrait<I, U8, U16, U32> for Integer<I> {}

impl<I: IntegerType> IntegerCore<I> for Integer<I> {}

impl<I: IntegerType> Visibility for Integer<I> {
    type Boolean = Boolean;

    /// Returns the number of field elements to encode `self`.
    fn size_in_fields(&self) -> Result<u16> {
        Ok(1)
    }
}

impl<I: IntegerType> Integer<I> {
    pub const MAX: Self = Self::new(I::MAX);
    pub const MIN: Self = Self::new(I::MIN);

    /// Initializes a new integer.
    pub const fn new(integer: I) -> Self {
        Self { integer }
    }
}

impl<I: IntegerType> TypeName for Integer<I> {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        I::type_name()
    }
}

impl<I: IntegerType> Deref for Integer<I> {
    type Target = I;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.integer
    }
}
