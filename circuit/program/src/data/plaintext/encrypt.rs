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

impl Plaintext {
    /// Encrypts `self` to the given address under the given randomizer.
    pub fn encrypt(&self, address: &Address, randomizer: Scalar) -> Ciphertext {
        // Compute the plaintext view key.
        let plaintext_view_key = (address.to_group() * randomizer).to_x_coordinate();
        // Encrypt the plaintext.
        self.encrypt_symmetric(plaintext_view_key)
    }

    /// Encrypts `self` under the given plaintext view key.
    pub fn encrypt_symmetric(&self, plaintext_view_key: Field) -> Ciphertext {
        // Determine the number of randomizers needed to encrypt the plaintext.
        let num_randomizers = self.num_randomizers();
        // Prepare a randomizer for each field element.
        let randomizers = AleoV0::hash_many_psd8(&[AleoV0::encryption_domain(), plaintext_view_key], num_randomizers);
        // Encrypt the plaintext.
        self.encrypt_with_randomizers(&randomizers)
    }

    /// Encrypts `self` under the given randomizers.
    pub(crate) fn encrypt_with_randomizers(&self, randomizers: &[Field]) -> Ciphertext {
        // Encrypt the plaintext.
        Ciphertext::from_fields(
            &self
                .to_fields()
                .into_iter()
                .zip_eq(randomizers)
                .map(|(plaintext, randomizer)| plaintext + randomizer)
                .collect::<Vec<_>>(),
        )
    }
}
