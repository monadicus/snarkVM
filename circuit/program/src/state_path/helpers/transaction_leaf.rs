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

use snarkvm_circuit_types::{environment::prelude::*, Boolean, Field, U16, U8};

#[derive(Clone)]
pub struct TransactionLeaf {
    /// The variant of the Merkle leaf.
    variant: U8,
    /// The index of the Merkle leaf.
    index: U16,
    /// The ID.
    id: Field,
}

impl TransactionLeaf {
    /// Returns the variant of the Merkle leaf.
    pub const fn variant(&self) -> &U8 {
        &self.variant
    }

    /// Returns the index of the Merkle leaf.
    pub const fn index(&self) -> &U16 {
        &self.index
    }

    /// Returns the ID in the Merkle leaf.
    pub const fn id(&self) -> &Field {
        &self.id
    }
}

impl Inject for TransactionLeaf {
    type Primitive = console::TransactionLeaf;

    /// Initializes a new transaction leaf circuit from a primitive.
    fn new(mode: Mode, transaction_leaf: Self::Primitive) -> Self {
        Self {
            variant: U8::new(mode, console::U8::new(transaction_leaf.variant())),
            index: U16::new(mode, console::U16::new(transaction_leaf.index())),
            id: Field::new(mode, transaction_leaf.id()),
        }
    }
}

impl Eject for TransactionLeaf {
    type Primitive = console::TransactionLeaf;

    /// Ejects the mode of the transaction leaf.
    fn eject_mode(&self) -> Mode {
        (&self.variant, &self.index, &self.id).eject_mode()
    }

    /// Ejects the transaction leaf.
    fn eject_value(&self) -> Self::Primitive {
        Self::Primitive::from(*self.variant.eject_value(), *self.index.eject_value(), self.id.eject_value())
    }
}

impl ToBits for TransactionLeaf {
    type Boolean = Boolean;

    /// Outputs the little-endian bit representation of `self` *without* trailing zeros.
    fn write_bits_le(&self, vec: &mut Vec<Self::Boolean>) {
        self.variant.write_bits_le(vec);
        self.index.write_bits_le(vec);
        self.id.write_bits_le(vec);
    }

    /// Outputs the big-endian bit representation of `self` *without* leading zeros.
    fn write_bits_be(&self, vec: &mut Vec<Self::Boolean>) {
        self.variant.write_bits_be(vec);
        self.index.write_bits_be(vec);
        self.id.write_bits_be(vec);
    }
}
