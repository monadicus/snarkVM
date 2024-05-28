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

mod bytes;
mod parse;
mod serialize;

use crate::{Identifier, U32};
use snarkvm_console_network::prelude::*;

/// A helper type for accessing an entry in a register, struct, array, or record.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Access {
    /// Access a member of a register, struct, or record.
    Member(Identifier),
    /// Access an element of an array.
    Index(U32),
}

impl From<Identifier> for Access {
    /// Initializes a new member access from an identifier.
    #[inline]
    fn from(identifier: Identifier) -> Self {
        Self::Member(identifier)
    }
}

impl From<U32> for Access {
    /// Initializes a new index access from a u32.
    #[inline]
    fn from(index: U32) -> Self {
        Self::Index(index)
    }
}
