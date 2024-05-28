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

use snarkvm_console_network::AleoNetwork;

use super::*;

impl TryFrom<Vec<Field>> for Plaintext {
    type Error = Error;

    /// Initializes a plaintext from a list of base field elements.
    fn try_from(fields: Vec<Field>) -> Result<Self, Self::Error> {
        Self::from_fields(&fields)
    }
}

impl TryFrom<&[Field]> for Plaintext {
    type Error = Error;

    /// Initializes a plaintext from a list of base field elements.
    fn try_from(fields: &[Field]) -> Result<Self, Self::Error> {
        Self::from_fields(fields)
    }
}

impl FromFields for Plaintext {
    type Field = Field;

    /// Initializes a plaintext from a list of base field elements.
    fn from_fields(fields: &[Self::Field]) -> Result<Self> {
        // Ensure the number of field elements does not exceed the maximum allowed size.
        if fields.len() > AleoNetwork::MAX_DATA_SIZE_IN_FIELDS as usize {
            bail!("Plaintext exceeds maximum allowed size")
        }

        // Unpack the field elements into little-endian bits, and reverse the list for popping the terminus bit off.
        let mut bits_le =
            fields.iter().flat_map(|field| field.to_bits_le().into_iter().take(Field::size_in_data_bits())).rev();
        // Remove the terminus bit that was added during encoding.
        for boolean in bits_le.by_ref() {
            // Drop all extraneous `0` bits, in addition to the final `1` bit.
            if boolean {
                // This case will always be reached, since the terminus bit is always `1`.
                break;
            }
        }
        // Reverse the bits back and recover the data from the bits.
        Self::from_bits_le(&bits_le.rev().collect::<Vec<_>>())
    }
}
