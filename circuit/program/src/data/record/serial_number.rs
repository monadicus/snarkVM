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

impl<Private: Visibility> Record<Private> {
    /// A helper method to derive the serial number from the private key and commitment.
    pub fn serial_number(private_key: PrivateKey, commitment: Field) -> Field {
        // Compute the generator `H` as `HashToGroup(commitment)`.
        let h = AleoV0::hash_to_group_psd2(&[AleoV0::serial_number_domain(), commitment.clone()]);
        // Compute `gamma` as `sk_sig * H`.
        let gamma = h * private_key.sk_sig();
        // Compute the serial number from `gamma`.
        Self::serial_number_from_gamma(&gamma, commitment)
    }

    /// A helper method to derive the serial number from the gamma and commitment.
    pub fn serial_number_from_gamma(gamma: &Group, commitment: Field) -> Field {
        // Compute `sn_nonce` as `Hash(COFACTOR * gamma)`.
        let sn_nonce =
            AleoV0::hash_to_scalar_psd2(&[AleoV0::serial_number_domain(), gamma.mul_by_cofactor().to_x_coordinate()]);
        // Compute `serial_number` as `Commit(commitment, sn_nonce)`.
        AleoV0::commit_bhp512(&(AleoV0::serial_number_domain(), commitment).to_bits_le(), &sn_nonce)
    }
}
