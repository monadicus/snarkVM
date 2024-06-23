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

use console::ConsoleField;
use snarkvm_circuit_network::AleoV0;
use snarkvm_circuit_types::environment::Circuit;

use super::*;

impl From<Vec<Field>> for Plaintext {
    /// Initializes a plaintext from a list of base field elements.
    fn from(fields: Vec<Field>) -> Self {
        Self::from_fields(&fields)
    }
}

impl From<&[Field]> for Plaintext {
    /// Initializes a plaintext from a list of base field elements.
    fn from(fields: &[Field]) -> Self {
        Self::from_fields(fields)
    }
}

impl FromFields for Plaintext {
    type Field = Field;

    /// Initializes a plaintext from a list of base field elements.
    fn from_fields(fields: &[Self::Field]) -> Self {
        // Ensure the number of field elements does not exceed the maximum allowed size.
        if fields.len() > AleoV0::MAX_DATA_SIZE_IN_FIELDS as usize {
            Circuit::halt("Plaintext exceeds maximum allowed size")
        }

        // Unpack the field elements into little-endian bits, and reverse the list for popping the terminus bit off.
        let mut bits_le = fields
            .iter()
            .flat_map(|field| field.to_bits_le().into_iter().take(ConsoleField::size_in_data_bits()))
            .rev();
        // Remove the terminus bit that was added during encoding.
        for boolean in bits_le.by_ref() {
            // Drop all extraneous `0` bits, in addition to the final `1` bit.
            if boolean.eject_value() {
                // This case will always be reached, since the terminus bit is always `1`.
                break;
            }
        }
        // Reverse the bits back and recover the data from the bits.
        Self::from_bits_le(&bits_le.rev().collect::<Vec<_>>())
    }
}
