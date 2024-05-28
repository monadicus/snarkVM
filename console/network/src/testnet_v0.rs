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

lazy_static! {
    pub static ref TESTNET_CREDITS_PROVING_KEYS: IndexMap<String, Arc<VarunaProvingKey>> = {
        let mut map = IndexMap::new();
        snarkvm_parameters::insert_testnet_credit_keys!(map, VarunaProvingKey, Prover);
        map
    };
    pub static ref TESTNET_CREDITS_VERIFYING_KEYS: IndexMap<String, Arc<VarunaVerifyingKey>> = {
        let mut map = IndexMap::new();
        snarkvm_parameters::insert_testnet_credit_keys!(map, VarunaVerifyingKey, Verifier);
        map
    };
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TestnetV0;

impl Environment for TestnetV0 {
    type Affine = <Console as Environment>::Affine;
    type BigInteger = <Console as Environment>::BigInteger;
    type Field = <Console as Environment>::Field;
    type PairingCurve = <Console as Environment>::PairingCurve;
    type Projective = <Console as Environment>::Projective;
    type Scalar = <Console as Environment>::Scalar;

    /// The coefficient `A` of the twisted Edwards curve.
    const EDWARDS_A: Self::Field = Console::EDWARDS_A;
    /// The coefficient `D` of the twisted Edwards curve.
    const EDWARDS_D: Self::Field = Console::EDWARDS_D;
    /// The coefficient `A` of the Montgomery curve.
    const MONTGOMERY_A: Self::Field = Console::MONTGOMERY_A;
    /// The coefficient `B` of the Montgomery curve.
    const MONTGOMERY_B: Self::Field = Console::MONTGOMERY_B;
}

impl Network for TestnetV0 {
    /// The network edition.
    const EDITION: u16 = 0;
    /// The genesis block coinbase target.
    const GENESIS_COINBASE_TARGET: u64 = (1u64 << 10).saturating_sub(1);
    /// The genesis block proof target.
    const GENESIS_PROOF_TARGET: u64 = 1u64 << 8;
    /// The fixed timestamp of the genesis block.
    const GENESIS_TIMESTAMP: i64 = 1715776496 /* 2024-05-15 12:34:56 UTC */;
    /// The network ID.
    const ID: u16 = 1;
    /// The function name for the inclusion circuit.
    const INCLUSION_FUNCTION_NAME: &'static str = MainnetV0::INCLUSION_FUNCTION_NAME;
    /// The maximum number of certificates in a batch.
    const MAX_CERTIFICATES: u16 = 100;
    /// The network name.
    const NAME: &'static str = "Aleo Testnet (v0)";

    /// Returns the genesis block bytes.
    fn genesis_bytes() -> &'static [u8] {
        snarkvm_parameters::testnet::GenesisBytes::load_bytes()
    }

    /// Returns the proving key for the given function name in `credits.aleo`.
    fn get_credits_proving_key(function_name: String) -> Result<&'static Arc<VarunaProvingKey>> {
        TESTNET_CREDITS_PROVING_KEYS
            .get(&function_name)
            .ok_or_else(|| anyhow!("Proving key for credits.aleo/{function_name}' not found"))
    }

    /// Returns the verifying key for the given function name in `credits.aleo`.
    fn get_credits_verifying_key(function_name: String) -> Result<&'static Arc<VarunaVerifyingKey>> {
        TESTNET_CREDITS_VERIFYING_KEYS
            .get(&function_name)
            .ok_or_else(|| anyhow!("Verifying key for credits.aleo/{function_name}' not found"))
    }

    /// Returns the `proving key` for the inclusion circuit.
    fn inclusion_proving_key() -> &'static Arc<VarunaProvingKey> {
        static INSTANCE: OnceCell<Arc<VarunaProvingKey>> = OnceCell::new();
        INSTANCE.get_or_init(|| {
            // Skipping the first byte, which is the encoded version.
            Arc::new(
                CircuitProvingKey::from_bytes_le(&snarkvm_parameters::testnet::INCLUSION_PROVING_KEY[1..])
                    .expect("Failed to load inclusion proving key."),
            )
        })
    }

    /// Returns the `verifying key` for the inclusion circuit.
    fn inclusion_verifying_key() -> &'static Arc<VarunaVerifyingKey> {
        static INSTANCE: OnceCell<Arc<VarunaVerifyingKey>> = OnceCell::new();
        INSTANCE.get_or_init(|| {
            // Skipping the first byte, which is the encoded version.
            Arc::new(
                CircuitVerifyingKey::from_bytes_le(&snarkvm_parameters::testnet::INCLUSION_VERIFYING_KEY[1..])
                    .expect("Failed to load inclusion verifying key."),
            )
        })
    }
}
