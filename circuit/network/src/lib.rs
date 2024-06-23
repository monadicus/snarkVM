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

#![forbid(unsafe_code)]
#![allow(clippy::too_many_arguments)]

pub mod canary_v0;
pub use canary_v0::*;

pub mod testnet_v0;
use console::AleoNetwork;
pub use testnet_v0::*;

pub mod v0;
pub use v0::*;

use snarkvm_circuit_algorithms::{
    Commit,
    CommitUncompressed,
    Hash,
    HashMany,
    HashToGroup,
    HashToScalar,
    HashUncompressed,
    Keccak256,
    Keccak384,
    Keccak512,
    Pedersen128,
    Pedersen64,
    Poseidon2,
    Poseidon4,
    Poseidon8,
    Sha3_256,
    Sha3_384,
    Sha3_512,
    BHP1024,
    BHP256,
    BHP512,
    BHP768,
};
use snarkvm_circuit_collections::merkle_tree::MerklePath;
use snarkvm_circuit_types::{
    environment::{prelude::*, Environment},
    Boolean,
    Field,
    Group,
    Scalar,
};

thread_local! {
    /// The group bases for the Aleo signature and encryption schemes.
    static GENERATOR_G: Vec<Group> = Vec::constant(AleoNetwork::g_powers().to_vec());

    /// The encryption domain as a constant field element.
    static ENCRYPTION_DOMAIN: Field = Field::constant(AleoNetwork::encryption_domain());
    /// The graph key domain as a constant field element.
    static GRAPH_KEY_DOMAIN: Field = Field::constant(AleoNetwork::graph_key_domain());
    /// The serial number domain as a constant field element.
    static SERIAL_NUMBER_DOMAIN: Field = Field::constant(AleoNetwork::serial_number_domain());

    /// The BHP hash function, which can take an input of up to 256 bits.
    static BHP_256: BHP256 = BHP256::constant(console::BHP_256.clone());
    /// The BHP hash function, which can take an input of up to 512 bits.
    static BHP_512: BHP512 = BHP512::constant(console::BHP_512.clone());
    /// The BHP hash function, which can take an input of up to 768 bits.
    static BHP_768: BHP768 = BHP768::constant(console::BHP_768.clone());
    /// The BHP hash function, which can take an input of up to 1024 bits.
    static BHP_1024: BHP1024 = BHP1024::constant(console::BHP_1024.clone());

    /// The Keccak hash function, which outputs 256 bits.
    static KECCAK_256: Keccak256 = Keccak256::new();
    /// The Keccak hash function, which outputs 384 bits.
    static KECCAK_384: Keccak384 = Keccak384::new();
    /// The Keccak hash function, which outputs 512 bits.
    static KECCAK_512: Keccak512 = Keccak512::new();

    /// The Pedersen hash function, which can take an input of up to 64 bits.
    static PEDERSEN_64: Pedersen64 = Pedersen64::constant(console::PEDERSEN_64.clone());
    /// The Pedersen hash function, which can take an input of up to 128 bits.
    static PEDERSEN_128: Pedersen128 = Pedersen128::constant(console::PEDERSEN_128.clone());

    /// The Poseidon hash function, using a rate of 2.
    static POSEIDON_2: Poseidon2 = Poseidon2::constant(console::POSEIDON_2.clone());
    /// The Poseidon hash function, using a rate of 4.
    static POSEIDON_4: Poseidon4 = Poseidon4::constant(console::POSEIDON_4.clone());
    /// The Poseidon hash function, using a rate of 8.
    static POSEIDON_8: Poseidon8 = Poseidon8::constant(console::POSEIDON_8.clone());

    /// The SHA-3 hash function, which outputs 256 bits.
    static SHA3_256: Sha3_256 = Sha3_256::new();
    /// The SHA-3 hash function, which outputs 384 bits.
    static SHA3_384: Sha3_384 = Sha3_384::new();
    /// The SHA-3 hash function, which outputs 512 bits.
    static SHA3_512: Sha3_512 = Sha3_512::new();
}

/// Attention: Do not use `Send + Sync` on this trait, as it is not thread-safe.
pub trait Aleo: Environment {
    /// The maximum number of field elements in data (must not exceed u16::MAX).
    const MAX_DATA_SIZE_IN_FIELDS: u32 = AleoNetwork::MAX_DATA_SIZE_IN_FIELDS;
    /// Initializes the global constants for the Aleo environment.
    fn initialize_global_constants() {
        GENERATOR_G.with(|_| ());
        ENCRYPTION_DOMAIN.with(|_| ());
        GRAPH_KEY_DOMAIN.with(|_| ());
        SERIAL_NUMBER_DOMAIN.with(|_| ());
        BHP_256.with(|_| ());
        BHP_512.with(|_| ());
        BHP_768.with(|_| ());
        BHP_1024.with(|_| ());
        KECCAK_256.with(|_| ());
        KECCAK_384.with(|_| ());
        KECCAK_512.with(|_| ());
        PEDERSEN_64.with(|_| ());
        PEDERSEN_128.with(|_| ());
        POSEIDON_2.with(|_| ());
        POSEIDON_4.with(|_| ());
        POSEIDON_8.with(|_| ());
        SHA3_256.with(|_| ());
        SHA3_384.with(|_| ());
        SHA3_512.with(|_| ());
    }

    /// Returns the encryption domain as a constant field element.
    fn encryption_domain() -> Field {
        ENCRYPTION_DOMAIN.with(|domain| domain.clone())
    }

    /// Returns the graph key domain as a constant field element.
    fn graph_key_domain() -> Field {
        GRAPH_KEY_DOMAIN.with(|domain| domain.clone())
    }

    /// Returns the serial number domain as a constant field element.
    fn serial_number_domain() -> Field {
        SERIAL_NUMBER_DOMAIN.with(|domain| domain.clone())
    }

    /// Returns the scalar multiplication on the generator `G`.
    #[inline]
    fn g_scalar_multiply(scalar: &Scalar) -> Group {
        GENERATOR_G.with(|bases| {
            bases
                .iter()
                .zip_eq(&scalar.to_bits_le())
                .fold(Group::zero(), |output, (base, bit)| Group::ternary(bit, &(&output + base), &output))
        })
    }

    /// Returns a BHP commitment with an input hasher of 256-bits.
    fn commit_bhp256(input: &[Boolean], randomizer: &Scalar) -> Field {
        BHP_256.with(|bhp| bhp.commit(input, randomizer))
    }

    /// Returns a BHP commitment with an input hasher of 512-bits.
    fn commit_bhp512(input: &[Boolean], randomizer: &Scalar) -> Field {
        BHP_512.with(|bhp| bhp.commit(input, randomizer))
    }

    /// Returns a BHP commitment with an input hasher of 768-bits.
    fn commit_bhp768(input: &[Boolean], randomizer: &Scalar) -> Field {
        BHP_768.with(|bhp| bhp.commit(input, randomizer))
    }

    /// Returns a BHP commitment with an input hasher of 1024-bits.
    fn commit_bhp1024(input: &[Boolean], randomizer: &Scalar) -> Field {
        BHP_1024.with(|bhp| bhp.commit(input, randomizer))
    }

    /// Returns a Pedersen commitment for the given (up to) 64-bit input and randomizer.
    fn commit_ped64(input: &[Boolean], randomizer: &Scalar) -> Field {
        PEDERSEN_64.with(|pedersen| pedersen.commit(input, randomizer))
    }

    /// Returns a Pedersen commitment for the given (up to) 128-bit input and randomizer.
    fn commit_ped128(input: &[Boolean], randomizer: &Scalar) -> Field {
        PEDERSEN_128.with(|pedersen| pedersen.commit(input, randomizer))
    }

    /// Returns a BHP commitment with an input hasher of 256-bits.
    fn commit_to_group_bhp256(input: &[Boolean], randomizer: &Scalar) -> Group {
        BHP_256.with(|bhp| bhp.commit_uncompressed(input, randomizer))
    }

    /// Returns a BHP commitment with an input hasher of 512-bits.
    fn commit_to_group_bhp512(input: &[Boolean], randomizer: &Scalar) -> Group {
        BHP_512.with(|bhp| bhp.commit_uncompressed(input, randomizer))
    }

    /// Returns a BHP commitment with an input hasher of 768-bits.
    fn commit_to_group_bhp768(input: &[Boolean], randomizer: &Scalar) -> Group {
        BHP_768.with(|bhp| bhp.commit_uncompressed(input, randomizer))
    }

    /// Returns a BHP commitment with an input hasher of 1024-bits.
    fn commit_to_group_bhp1024(input: &[Boolean], randomizer: &Scalar) -> Group {
        BHP_1024.with(|bhp| bhp.commit_uncompressed(input, randomizer))
    }

    /// Returns a Pedersen commitment for the given (up to) 64-bit input and randomizer.
    fn commit_to_group_ped64(input: &[Boolean], randomizer: &Scalar) -> Group {
        PEDERSEN_64.with(|pedersen| pedersen.commit_uncompressed(input, randomizer))
    }

    /// Returns a Pedersen commitment for the given (up to) 128-bit input and randomizer.
    fn commit_to_group_ped128(input: &[Boolean], randomizer: &Scalar) -> Group {
        PEDERSEN_128.with(|pedersen| pedersen.commit_uncompressed(input, randomizer))
    }

    /// Returns the BHP hash with an input hasher of 256-bits.
    fn hash_bhp256(input: &[Boolean]) -> Field {
        BHP_256.with(|bhp| bhp.hash(input))
    }

    /// Returns the BHP hash with an input hasher of 512-bits.
    fn hash_bhp512(input: &[Boolean]) -> Field {
        BHP_512.with(|bhp| bhp.hash(input))
    }

    /// Returns the BHP hash with an input hasher of 768-bits.
    fn hash_bhp768(input: &[Boolean]) -> Field {
        BHP_768.with(|bhp| bhp.hash(input))
    }

    /// Returns the BHP hash with an input hasher of 1024-bits.
    fn hash_bhp1024(input: &[Boolean]) -> Field {
        BHP_1024.with(|bhp| bhp.hash(input))
    }

    /// Returns the Keccak hash with a 256-bit output.
    fn hash_keccak256(input: &[Boolean]) -> Vec<Boolean> {
        KECCAK_256.with(|keccak| keccak.hash(input))
    }

    /// Returns the Keccak hash with a 384-bit output.
    fn hash_keccak384(input: &[Boolean]) -> Vec<Boolean> {
        KECCAK_384.with(|keccak| keccak.hash(input))
    }

    /// Returns the Keccak hash with a 512-bit output.
    fn hash_keccak512(input: &[Boolean]) -> Vec<Boolean> {
        KECCAK_512.with(|keccak| keccak.hash(input))
    }

    /// Returns the Pedersen hash for a given (up to) 64-bit input.
    fn hash_ped64(input: &[Boolean]) -> Field {
        PEDERSEN_64.with(|pedersen| pedersen.hash(input))
    }

    /// Returns the Pedersen hash for a given (up to) 128-bit input.
    fn hash_ped128(input: &[Boolean]) -> Field {
        PEDERSEN_128.with(|pedersen| pedersen.hash(input))
    }

    /// Returns the Poseidon hash with an input rate of 2.
    fn hash_psd2(input: &[Field]) -> Field {
        POSEIDON_2.with(|poseidon| poseidon.hash(input))
    }

    /// Returns the Poseidon hash with an input rate of 4.
    fn hash_psd4(input: &[Field]) -> Field {
        POSEIDON_4.with(|poseidon| poseidon.hash(input))
    }

    /// Returns the Poseidon hash with an input rate of 8.
    fn hash_psd8(input: &[Field]) -> Field {
        POSEIDON_8.with(|poseidon| poseidon.hash(input))
    }

    /// Returns the SHA-3 hash with a 256-bit output.
    fn hash_sha3_256(input: &[Boolean]) -> Vec<Boolean> {
        SHA3_256.with(|sha3| sha3.hash(input))
    }

    /// Returns the SHA-3 hash with a 384-bit output.
    fn hash_sha3_384(input: &[Boolean]) -> Vec<Boolean> {
        SHA3_384.with(|sha3| sha3.hash(input))
    }

    /// Returns the SHA-3 hash with a 512-bit output.
    fn hash_sha3_512(input: &[Boolean]) -> Vec<Boolean> {
        SHA3_512.with(|sha3| sha3.hash(input))
    }

    /// Returns the extended Poseidon hash with an input rate of 2.
    fn hash_many_psd2(input: &[Field], num_outputs: u16) -> Vec<Field> {
        POSEIDON_2.with(|poseidon| poseidon.hash_many(input, num_outputs))
    }

    /// Returns the extended Poseidon hash with an input rate of 4.
    fn hash_many_psd4(input: &[Field], num_outputs: u16) -> Vec<Field> {
        POSEIDON_4.with(|poseidon| poseidon.hash_many(input, num_outputs))
    }

    /// Returns the extended Poseidon hash with an input rate of 8.
    fn hash_many_psd8(input: &[Field], num_outputs: u16) -> Vec<Field> {
        POSEIDON_8.with(|poseidon| poseidon.hash_many(input, num_outputs))
    }

    /// Returns the BHP hash with an input hasher of 256-bits.
    fn hash_to_group_bhp256(input: &[Boolean]) -> Group {
        BHP_256.with(|bhp| bhp.hash_uncompressed(input))
    }

    /// Returns the BHP hash with an input hasher of 512-bits.
    fn hash_to_group_bhp512(input: &[Boolean]) -> Group {
        BHP_512.with(|bhp| bhp.hash_uncompressed(input))
    }

    /// Returns the BHP hash with an input hasher of 768-bits.
    fn hash_to_group_bhp768(input: &[Boolean]) -> Group {
        BHP_768.with(|bhp| bhp.hash_uncompressed(input))
    }

    /// Returns the BHP hash with an input hasher of 1024-bits.
    fn hash_to_group_bhp1024(input: &[Boolean]) -> Group {
        BHP_1024.with(|bhp| bhp.hash_uncompressed(input))
    }

    /// Returns the Pedersen hash for a given (up to) 64-bit input.
    fn hash_to_group_ped64(input: &[Boolean]) -> Group {
        PEDERSEN_64.with(|pedersen| pedersen.hash_uncompressed(input))
    }

    /// Returns the Pedersen hash for a given (up to) 128-bit input.
    fn hash_to_group_ped128(input: &[Boolean]) -> Group {
        PEDERSEN_128.with(|pedersen| pedersen.hash_uncompressed(input))
    }

    /// Returns the Poseidon hash with an input rate of 2 on the affine curve.
    fn hash_to_group_psd2(input: &[Field]) -> Group {
        POSEIDON_2.with(|poseidon| poseidon.hash_to_group(input))
    }

    /// Returns the Poseidon hash with an input rate of 4 on the affine curve.
    fn hash_to_group_psd4(input: &[Field]) -> Group {
        POSEIDON_4.with(|poseidon| poseidon.hash_to_group(input))
    }

    /// Returns the Poseidon hash with an input rate of 8 on the affine curve.
    fn hash_to_group_psd8(input: &[Field]) -> Group {
        POSEIDON_8.with(|poseidon| poseidon.hash_to_group(input))
    }

    /// Returns the Poseidon hash with an input rate of 2 on the scalar field.
    fn hash_to_scalar_psd2(input: &[Field]) -> Scalar {
        POSEIDON_2.with(|poseidon| poseidon.hash_to_scalar(input))
    }

    /// Returns the Poseidon hash with an input rate of 4 on the scalar field.
    fn hash_to_scalar_psd4(input: &[Field]) -> Scalar {
        POSEIDON_4.with(|poseidon| poseidon.hash_to_scalar(input))
    }

    /// Returns the Poseidon hash with an input rate of 8 on the scalar field.
    fn hash_to_scalar_psd8(input: &[Field]) -> Scalar {
        POSEIDON_8.with(|poseidon| poseidon.hash_to_scalar(input))
    }

    /// Returns `true` if the given Merkle path is valid for the given root and leaf.
    #[allow(clippy::ptr_arg)]
    fn verify_merkle_path_bhp<const DEPTH: u8>(path: &MerklePath<DEPTH>, root: &Field, leaf: &Vec<Boolean>) -> Boolean {
        BHP_1024.with(|bhp1024| BHP_512.with(|bhp512| path.verify(bhp1024, bhp512, root, leaf)))
    }

    /// Returns `true` if the given Merkle path is valid for the given root and leaf.
    #[allow(clippy::ptr_arg)]
    fn verify_merkle_path_psd<const DEPTH: u8>(path: &MerklePath<DEPTH>, root: &Field, leaf: &Vec<Field>) -> Boolean {
        POSEIDON_4.with(|psd4| POSEIDON_2.with(|psd2| path.verify(psd4, psd2, root, leaf)))
    }
}
