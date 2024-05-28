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
mod serialize;
mod string;

use snarkvm_console_types::prelude::*;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum InputID {
    /// The hash of the constant input.
    Constant(Field),
    /// The hash of the public input.
    Public(Field),
    /// The ciphertext hash of the private input.
    Private(Field),
    /// The commitment, gamma, serial number, and tag of the record input.
    Record(Field, Group, Field, Field),
    /// The hash of the external record input.
    ExternalRecord(Field),
}

impl InputID {
    /// Returns the (primary) input ID.
    pub const fn id(&self) -> &Field {
        match self {
            InputID::Constant(id) => id,
            InputID::Public(id) => id,
            InputID::Private(id) => id,
            InputID::Record(id, ..) => id,
            InputID::ExternalRecord(id) => id,
        }
    }
}
