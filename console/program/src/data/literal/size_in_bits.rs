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
    pub fn size_in_bits(&self) -> u16 {
        let size = match self {
            Self::Address(..) => Address::size_in_bits(),
            Self::Boolean(..) => Boolean::size_in_bits(),
            Self::Field(..) => Field::size_in_bits(),
            Self::Group(..) => Group::size_in_bits(),
            Self::I8(..) => I8::size_in_bits(),
            Self::I16(..) => I16::size_in_bits(),
            Self::I32(..) => I32::size_in_bits(),
            Self::I64(..) => I64::size_in_bits(),
            Self::I128(..) => I128::size_in_bits(),
            Self::U8(..) => U8::size_in_bits(),
            Self::U16(..) => U16::size_in_bits(),
            Self::U32(..) => U32::size_in_bits(),
            Self::U64(..) => U64::size_in_bits(),
            Self::U128(..) => U128::size_in_bits(),
            Self::Scalar(..) => Scalar::size_in_bits(),
            Self::Signature(..) => Signature::size_in_bits(),
            Self::String(string) => match string.len().checked_mul(8) {
                Some(size) => size,
                None => Console::halt("String exceeds usize::MAX bits."),
            },
        };
        u16::try_from(size).or_halt_with("Literal exceeds u16::MAX bits.")
    }
}
