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

mod bitwise;
mod bytes;
mod from_bits;
mod parse;
mod serialize;
mod size_in_bits;
mod size_in_bytes;
mod to_bits;
mod to_fields;
mod verify;

#[cfg(feature = "private_key")]
mod sign;

#[cfg(feature = "compute_key")]
use crate::ComputeKey;
#[cfg(feature = "private_key")]
use crate::PrivateKey;

use crate::address::Address;
use snarkvm_console_network::prelude::*;
use snarkvm_console_types::{Boolean, Field, Scalar};

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Signature {
    /// The verifier challenge to check against.
    challenge: Scalar,
    /// The prover response to the challenge.
    response: Scalar,
    /// The compute key of the prover.
    compute_key: ComputeKey,
}

impl From<(Scalar, Scalar, ComputeKey)> for Signature {
    /// Derives the account signature from a tuple `(challenge, response, compute_key)`.
    fn from((challenge, response, compute_key): (Scalar, Scalar, ComputeKey)) -> Self {
        Self { challenge, response, compute_key }
    }
}

impl From<&(Scalar, Scalar, ComputeKey)> for Signature {
    /// Derives the account signature from a tuple `(challenge, response, compute_key)`.
    fn from((challenge, response, compute_key): &(Scalar, Scalar, ComputeKey)) -> Self {
        Self { challenge: *challenge, response: *response, compute_key: *compute_key }
    }
}

impl Signature {
    /// Returns the verifier challenge.
    pub const fn challenge(&self) -> Scalar {
        self.challenge
    }

    /// Returns the prover response.
    pub const fn response(&self) -> Scalar {
        self.response
    }

    /// Returns the signer compute key.
    pub const fn compute_key(&self) -> ComputeKey {
        self.compute_key
    }

    /// Returns the signer address.
    pub fn to_address(&self) -> Address {
        self.compute_key.to_address()
    }
}

impl TypeName for Signature {
    /// Returns the type name as a string.
    #[inline]
    fn type_name() -> &'static str {
        "signature"
    }
}

impl Signature {
    /// Initializes a `zero` signature.
    #[cfg(any(test, feature = "test"))]
    pub fn zero() -> Self {
        Self::from((
            Scalar::zero(),
            Scalar::zero(),
            ComputeKey::try_from((crate::Group::zero(), crate::Group::zero())).unwrap(),
        ))
    }

    /// Initializes a "random" signature.
    #[cfg(any(test, feature = "test"))]
    pub fn rand<R: Rng>(rng: &mut R) -> Self {
        Self::from((
            Scalar::rand(rng),
            Scalar::rand(rng),
            ComputeKey::try_from((crate::Group::rand(rng), crate::Group::rand(rng))).unwrap(),
        ))
    }
}

#[cfg(test)]
mod test_helpers {
    use super::*;
    use snarkvm_console_network::MainnetV0;

    type CurrentNetwork = MainnetV0;

    /// Samples a random signature.
    pub(super) fn sample_signature(num_fields: u64, rng: &mut TestRng) -> Signature<CurrentNetwork> {
        // Sample an address and a private key.
        let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let address = Address::try_from(&private_key).unwrap();

        // Generate a signature.
        let message: Vec<_> = (0..num_fields).map(|_| Uniform::rand(rng)).collect();
        let signature = Signature::sign(&private_key, &message, rng).unwrap();
        assert!(signature.verify(&address, &message));
        signature
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ITERATIONS: u64 = 100;

    #[test]
    fn test_from() -> Result<()> {
        let mut rng = TestRng::default();

        for i in 0..ITERATIONS {
            // Sample a new signature.
            let signature = test_helpers::sample_signature(i, &mut rng);

            // Check that the signature can be reconstructed from its parts.
            let candidate = Signature::from((signature.challenge(), signature.response(), signature.compute_key()));
            assert_eq!(signature, candidate);
        }
        Ok(())
    }
}
