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
mod serialize;
mod string;

use snarkvm_console_account::{Address, PrivateKey, Signature};
use snarkvm_console_types::prelude::*;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct ProgramOwner {
    /// The address of the program owner.
    address: Address,
    /// The signature of the program owner, over the deployment transaction ID.
    signature: Signature,
}

impl ProgramOwner {
    /// Initializes a new program owner.
    pub fn new<R: Rng + CryptoRng>(private_key: &PrivateKey, deployment_id: Field, rng: &mut R) -> Result<Self> {
        // Derive the address.
        let address = Address::try_from(private_key)?;
        // Sign the transaction ID.
        let signature = private_key.sign(&[deployment_id], rng)?;
        // Return the program owner.
        Ok(Self { signature, address })
    }

    /// Initializes a new program owner from an address and signature.
    pub fn from(address: Address, signature: Signature) -> Self {
        Self { address, signature }
    }

    /// Returns the address of the program owner.
    pub const fn address(&self) -> Address {
        self.address
    }

    /// Returns the signature of the program owner.
    pub const fn signature(&self) -> &Signature {
        &self.signature
    }

    /// Verify that the signature is valid for the given deployment ID.
    pub fn verify(&self, deployment_id: Field) -> bool {
        self.signature.verify(&self.address, &[deployment_id])
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;

    use once_cell::sync::OnceCell;

    pub(crate) fn sample_program_owner() -> ProgramOwner {
        static INSTANCE: OnceCell<ProgramOwner> = OnceCell::new();
        *INSTANCE.get_or_init(|| {
            // Initialize the RNG.
            let rng = &mut TestRng::default();

            // Initialize a private key.
            let private_key = PrivateKey::new(rng).unwrap();

            // Initialize a deployment ID.
            let deployment_id: Field = rng.gen();

            // Return the program owner.
            ProgramOwner::new(&private_key, deployment_id, rng).unwrap()
        })
    }

    #[test]
    fn test_verify_program_owner() {
        // Initialize the RNG.
        let rng = &mut TestRng::default();

        // Initialize a private key.
        let private_key = PrivateKey::new(rng).unwrap();

        // Initialize a deployment ID.
        let deployment_id: Field = rng.gen();

        // Construct the program owner.
        let owner = ProgramOwner::new(&private_key, deployment_id, rng).unwrap();
        // Ensure that the program owner is verified for the given deployment ID.
        assert!(owner.verify(deployment_id));

        // Ensure that the program owner is not verified for a different deployment ID.
        let incorrect_deployment_id: Field = rng.gen();
        assert!(!owner.verify(incorrect_deployment_id));
    }
}
