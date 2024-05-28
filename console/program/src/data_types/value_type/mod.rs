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

use crate::{EntryType, Identifier, Locator, PlaintextType};
use snarkvm_console_network::prelude::*;

use enum_index::EnumIndex;

#[derive(Clone, PartialEq, Eq, Hash, EnumIndex)]
pub enum ValueType {
    /// A constant type.
    Constant(PlaintextType),
    /// A publicly-visible type.
    Public(PlaintextType),
    /// A private type decrypted with the account owner's address.
    Private(PlaintextType),
    /// A record type inherits its visibility from the record definition.
    Record(Identifier),
    /// An external record type inherits its visibility from its record definition.
    ExternalRecord(Locator),
    /// A publicly-visible future.
    Future(Locator),
}

impl From<EntryType> for ValueType {
    fn from(entry: EntryType) -> Self {
        match entry {
            EntryType::Constant(plaintext) => ValueType::Constant(plaintext),
            EntryType::Public(plaintext) => ValueType::Public(plaintext),
            EntryType::Private(private) => ValueType::Private(private),
        }
    }
}
