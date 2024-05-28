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

use crate::{ArrayType, Identifier, LiteralType};
use snarkvm_console_network::prelude::*;

/// A `PlaintextType` defines the type parameter for a literal, struct, or array.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum PlaintextType {
    /// A literal type contains its type name.
    /// The format of the type is `<type_name>`.
    Literal(LiteralType),
    /// An struct type contains its identifier.
    /// The format of the type is `<identifier>`.
    Struct(Identifier),
    /// An array type contains its element type and length.
    /// The format of the type is `[<element_type>; <length>]`.
    Array(ArrayType),
}

impl From<LiteralType> for PlaintextType {
    /// Initializes a plaintext type from a literal type.
    fn from(literal: LiteralType) -> Self {
        PlaintextType::Literal(literal)
    }
}

impl From<Identifier> for PlaintextType {
    /// Initializes a plaintext type from a struct type.
    fn from(struct_: Identifier) -> Self {
        PlaintextType::Struct(struct_)
    }
}

impl From<ArrayType> for PlaintextType {
    /// Initializes a plaintext type from an array type.
    fn from(array: ArrayType) -> Self {
        PlaintextType::Array(array)
    }
}
