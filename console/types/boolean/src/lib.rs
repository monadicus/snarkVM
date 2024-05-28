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
mod from_bits;
mod parse;
mod random;
mod serialize;
mod size_in_bits;
mod size_in_bytes;
mod to_bits;

pub use snarkvm_console_network_environment::prelude::*;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Boolean {
    /// The underlying boolean.
    boolean: bool,
}

impl BooleanTrait for Boolean {}

impl Boolean {
    /// Initializes a new boolean.
    pub const fn new(boolean: bool) -> Self {
        Self { boolean }
    }

    /// Initializes a `false` boolean.
    #[deprecated(since = "0.1.0", note = "This is used for **testing** purposes")]
    pub const fn zero() -> Self {
        Self::new(false)
    }
}

impl TypeName for Boolean {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "boolean"
    }
}

impl Deref for Boolean {
    type Target = bool;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.boolean
    }
}

impl PartialEq<Boolean> for bool {
    fn eq(&self, other: &Boolean) -> bool {
        *self == **other
    }
}
