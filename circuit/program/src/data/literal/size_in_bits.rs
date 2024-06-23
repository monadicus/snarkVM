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

use super::*;

impl Literal {
    /// Returns the number of bits of this literal.
    pub fn size_in_bits(&self) -> U16 {
        U16::constant(console::U16::new(match self {
            Self::Address(..) => console::Address::size_in_bits() as u16,
            Self::Boolean(..) => console::Boolean::size_in_bits() as u16,
            Self::Field(..) => console::Field::size_in_bits() as u16,
            Self::Group(..) => console::Group::size_in_bits() as u16,
            Self::I8(..) => console::I8::size_in_bits() as u16,
            Self::I16(..) => console::I16::size_in_bits() as u16,
            Self::I32(..) => console::I32::size_in_bits() as u16,
            Self::I64(..) => console::I64::size_in_bits() as u16,
            Self::I128(..) => console::I128::size_in_bits() as u16,
            Self::U8(..) => console::U8::size_in_bits() as u16,
            Self::U16(..) => console::U16::size_in_bits() as u16,
            Self::U32(..) => console::U32::size_in_bits() as u16,
            Self::U64(..) => console::U64::size_in_bits() as u16,
            Self::U128(..) => console::U128::size_in_bits() as u16,
            Self::Scalar(..) => console::Scalar::size_in_bits() as u16,
            Self::Signature(..) => console::Signature::size_in_bits() as u16,
            Self::String(string) => string.to_bits_le().len() as u16,
        }))
    }
}
