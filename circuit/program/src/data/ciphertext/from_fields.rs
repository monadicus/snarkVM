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

use snarkvm_circuit_network::AleoV0;

use super::*;

impl From<Vec<Field>> for Ciphertext {
    /// Initializes a ciphertext from a list of base field elements.
    fn from(fields: Vec<Field>) -> Self {
        // Ensure the number of field elements does not exceed the maximum allowed size.
        match fields.len() <= AleoV0::MAX_DATA_SIZE_IN_FIELDS as usize {
            true => Self(fields),
            false => Circuit::halt("Ciphertext exceeds maximum allowed size"),
        }
    }
}

impl From<&[Field]> for Ciphertext {
    /// Initializes a ciphertext from a list of base field elements.
    fn from(fields: &[Field]) -> Self {
        Self::from_fields(fields)
    }
}

impl FromFields for Ciphertext {
    type Field = Field;

    /// Initializes a ciphertext from a list of base field elements.
    fn from_fields(fields: &[Self::Field]) -> Self {
        Self::from(fields.to_vec())
    }
}
