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

use crate::{Identifier, PlaintextType};
use snarkvm_console_network::prelude::*;

use indexmap::IndexMap;

#[derive(Clone, PartialEq, Eq)]
pub struct StructType {
    /// The name of the struct.
    name: Identifier,
    /// The name and type for the members of the struct.
    members: IndexMap<Identifier, PlaintextType>,
}

impl StructType {
    /// Returns the name of the struct type.
    #[inline]
    pub const fn name(&self) -> &Identifier {
        &self.name
    }

    /// Returns the members of the struct type.
    #[inline]
    pub const fn members(&self) -> &IndexMap<Identifier, PlaintextType> {
        &self.members
    }
}

impl TypeName for StructType {
    /// Returns the type name.
    fn type_name() -> &'static str {
        "struct"
    }
}
