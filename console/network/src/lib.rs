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
#![warn(clippy::cast_possible_truncation)]

#[macro_use]
extern crate lazy_static;

pub use snarkvm_console_network_environment as environment;
pub use snarkvm_console_network_environment::*;

mod helpers;
pub use helpers::*;

mod canary_v0;
pub use canary_v0::*;

mod mainnet_v0;
pub use mainnet_v0::*;

mod testnet_v0;
pub use testnet_v0::*;

pub mod prelude {
    pub use crate::{
        environment::prelude::*,
        AleoNetwork,
        BlockHash,
        Network,
        RatificationID,
        StateRoot,
        TransactionID,
        TransitionID,
    };
}

use crate::environment::prelude::*;
use snarkvm_algorithms::{
    crypto_hash::PoseidonSponge,
    snark::varuna::{CircuitProvingKey, CircuitVerifyingKey, VarunaHidingMode},
    srs::{UniversalProver, UniversalVerifier},
    AlgebraicSponge,
};
use snarkvm_console_algorithms::{
    Blake2Xs,
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

use snarkvm_console_collections::merkle_tree::{MerklePath, MerkleTree};
use snarkvm_console_types::{Field, Group, Scalar};
use snarkvm_curves::PairingEngine;

use indexmap::IndexMap;
use once_cell::sync::OnceCell;
use std::sync::Arc;

/// A helper type for the BHP Merkle tree.
pub type BHPMerkleTree<const DEPTH: u8> = MerkleTree<BHP1024, BHP512, DEPTH>;
/// A helper type for the Poseidon Merkle tree.
pub type PoseidonMerkleTree<const DEPTH: u8> = MerkleTree<Poseidon4, Poseidon2, DEPTH>;

/// Helper types for the Varuna parameters.
type Fq = <ConsolePairingCurve as PairingEngine>::Fq;
pub type FiatShamir = PoseidonSponge<Fq, 2, 1>;
pub type FiatShamirParameters = <FiatShamir as AlgebraicSponge<Fq, 2>>::Parameters;

/// Helper types for the Varuna proving and verifying key.
pub(crate) type VarunaProvingKey = CircuitProvingKey<ConsolePairingCurve, VarunaHidingMode>;
pub(crate) type VarunaVerifyingKey = CircuitVerifyingKey<ConsolePairingCurve>;

/// The block hash type.
pub type BlockHash = AleoID<Field, { hrp2!("ab") }>;
/// The ratification ID type.
pub type RatificationID = AleoID<Field, { hrp2!("ar") }>;
/// The state root type.
pub type StateRoot = AleoID<Field, { hrp2!("sr") }>;
/// The transaction ID type.
pub type TransactionID = AleoID<Field, { hrp2!(TRANSACTION_PREFIX) }>;
/// The transition ID type.
pub type TransitionID = AleoID<Field, { hrp2!("au") }>;

pub trait Network:
    'static
    + Environment
    + Copy
    + Clone
    + Debug
    + Eq
    + PartialEq
    + core::hash::Hash
    + Serialize
    + DeserializeOwned
    + for<'a> Deserialize<'a>
    + Send
    + Sync
{
    /// The network ID.
    const ID: u16;
    /// The network name.
    const NAME: &'static str;
    /// The network edition.
    const EDITION: u16;

    /// The function name for the inclusion circuit.
    const INCLUSION_FUNCTION_NAME: &'static str;

    /// The fixed timestamp of the genesis block.
    const GENESIS_TIMESTAMP: i64;
    /// The genesis block coinbase target.
    #[cfg(not(feature = "test"))]
    const GENESIS_COINBASE_TARGET: u64 = (1u64 << 10).saturating_sub(1);
    /// The genesis block coinbase target.
    /// This is deliberately set to a low value (32) for testing purposes only.
    #[cfg(feature = "test")]
    const GENESIS_COINBASE_TARGET: u64 = (1u64 << 5).saturating_sub(1);
    /// The genesis block proof target.
    #[cfg(not(feature = "test"))]
    const GENESIS_PROOF_TARGET: u64 = 1u64 << 8;
    /// The genesis block proof target.
    /// This is deliberately set to a low value (8) for testing purposes only.
    #[cfg(feature = "test")]
    const GENESIS_PROOF_TARGET: u64 = 1u64 << 3;
    /// The maximum number of solutions that can be included per block as a power of 2.
    const MAX_SOLUTIONS_AS_POWER_OF_TWO: u8 = 2; // 4 solutions
    /// The maximum number of solutions that can be included per block.
    const MAX_SOLUTIONS: usize = 1 << Self::MAX_SOLUTIONS_AS_POWER_OF_TWO; // 4 solutions

    /// The starting supply of Aleo credits.
    const STARTING_SUPPLY: u64 = 1_500_000_000_000_000; // 1.5B credits
    /// The cost in microcredits per byte for the deployment transaction.
    const DEPLOYMENT_FEE_MULTIPLIER: u64 = 1_000; // 1 millicredit per byte
    /// The constant that divides the storage polynomial.
    const EXECUTION_STORAGE_FEE_SCALING_FACTOR: u64 = 5000;
    /// The maximum size execution transactions can be before a quadratic storage penalty applies.
    const EXECUTION_STORAGE_PENALTY_THRESHOLD: u64 = 5000;
    /// The cost in microcredits per constraint for the deployment transaction.
    const SYNTHESIS_FEE_MULTIPLIER: u64 = 25; // 25 microcredits per constraint
    /// The maximum number of variables in a deployment.
    const MAX_DEPLOYMENT_VARIABLES: u64 = 1 << 20; // 1,048,576 variables
    /// The maximum number of constraints in a deployment.
    const MAX_DEPLOYMENT_CONSTRAINTS: u64 = 1 << 20; // 1,048,576 constraints
    /// The maximum number of microcredits that can be spent as a fee.
    const MAX_FEE: u64 = 1_000_000_000_000_000;
    /// The maximum number of microcredits that can be spent on a finalize block.
    const TRANSACTION_SPEND_LIMIT: u64 = 100_000_000;

    /// The anchor height, defined as the expected number of blocks to reach the coinbase target.
    const ANCHOR_HEIGHT: u32 = Self::ANCHOR_TIME as u32 / Self::BLOCK_TIME as u32;
    /// The anchor time in seconds.
    const ANCHOR_TIME: u16 = 25;
    /// The expected time per block in seconds.
    const BLOCK_TIME: u16 = 10;
    /// The number of blocks per epoch.
    const NUM_BLOCKS_PER_EPOCH: u32 = 3600 / Self::BLOCK_TIME as u32; // 360 blocks == ~1 hour

    /// The maximum number of certificates in a batch.
    const MAX_CERTIFICATES: u16;

    /// The maximum number of bytes in a transaction.
    // Note: This value must **not** be decreased as it would invalidate existing transactions.
    const MAX_TRANSACTION_SIZE: usize = 128_000; // 128 kB

    /// Returns the genesis block bytes.
    fn genesis_bytes() -> &'static [u8];

    /// Returns the restrictions list as a JSON-compatible string.
    fn restrictions_list_as_str() -> &'static str;

    /// Returns the proving key for the given function name in `credits.aleo`.
    fn get_credits_proving_key(function_name: String) -> Result<&'static Arc<VarunaProvingKey>>;

    /// Returns the verifying key for the given function name in `credits.aleo`.
    fn get_credits_verifying_key(function_name: String) -> Result<&'static Arc<VarunaVerifyingKey>>;

    /// Returns the `proving key` for the inclusion circuit.
    fn inclusion_proving_key() -> &'static Arc<VarunaProvingKey>;

    /// Returns the `verifying key` for the inclusion circuit.
    fn inclusion_verifying_key() -> &'static Arc<VarunaVerifyingKey>;
}

pub struct AleoNetwork;

impl AleoNetwork {
    // This ensures the array is not empty.
    /// The maximum number of elements in an array.
    pub const MAX_ARRAY_ELEMENTS: usize = Self::MAX_DATA_ENTRIES;
    /// The maximum number of closures in a program.
    pub const MAX_CLOSURES: usize = 2 * Self::MAX_FUNCTIONS;
    /// The maximum number of commands in finalize.
    pub const MAX_COMMANDS: usize = u16::MAX as usize;
    /// The maximum recursive depth of an entry.
    /// Note: This value must be strictly less than u8::MAX.
    pub const MAX_DATA_DEPTH: usize = 32;
    /// The maximum number of entries in data.
    pub const MAX_DATA_ENTRIES: usize = 32;
    /// The maximum number of fields in data (must not exceed u16::MAX).
    #[allow(clippy::cast_possible_truncation)]
    pub const MAX_DATA_SIZE_IN_FIELDS: u32 = ((128 * 1024 * 8) / Field::SIZE_IN_DATA_BITS) as u32;
    /// The maximum number of functions in a program.
    pub const MAX_FUNCTIONS: usize = 31;
    /// The maximum number of imports.
    pub const MAX_IMPORTS: usize = 64;
    /// The maximum number of inputs per transition.
    pub const MAX_INPUTS: usize = 16;
    /// The maximum number of instructions in a closure or function.
    pub const MAX_INSTRUCTIONS: usize = u16::MAX as usize;
    // 100 KB

    /// The maximum number of mappings in a program.
    pub const MAX_MAPPINGS: usize = 31;
    /// The maximum number of operands in an instruction.
    pub const MAX_OPERANDS: usize = Self::MAX_INPUTS;
    /// The maximum number of outputs per transition.
    pub const MAX_OUTPUTS: usize = 16;
    /// The maximum program depth.
    pub const MAX_PROGRAM_DEPTH: usize = 64;
    /// The maximum program size by number of characters.
    pub const MAX_PROGRAM_SIZE: usize = 100_000;
    /// The maximum number of records in a program.
    pub const MAX_RECORDS: usize = 10 * Self::MAX_FUNCTIONS;
    // This accounts for 'record.owner'.
    /// The maximum number of entries in a record.
    pub const MAX_RECORD_ENTRIES: usize = Self::MIN_RECORD_ENTRIES.saturating_add(Self::MAX_DATA_ENTRIES);
    /// The maximum number of bytes allowed in a string.
    pub const MAX_STRING_BYTES: u32 = Console::MAX_STRING_BYTES;
    /// The maximum number of structs in a program.
    pub const MAX_STRUCTS: usize = 10 * Self::MAX_FUNCTIONS;
    // This ensures the struct is not empty.
    /// The maximum number of entries in a struct.
    pub const MAX_STRUCT_ENTRIES: usize = Self::MAX_DATA_ENTRIES;
    /// The maximum number of write commands in finalize.
    pub const MAX_WRITES: u16 = 16;
    /// The minimum number of elements in an array.
    pub const MIN_ARRAY_ELEMENTS: usize = 1;
    /// The minimum number of entries in a record.
    pub const MIN_RECORD_ENTRIES: usize = 1;
    /// The minimum number of entries in a struct.
    pub const MIN_STRUCT_ENTRIES: usize = 1;

    /// Returns the powers of `G`.
    pub fn g_powers() -> &'static Vec<Group> {
        &GENERATOR_G
    }

    /// Returns the scalar multiplication on the generator `G`.
    pub fn g_scalar_multiply(scalar: &Scalar) -> Group {
        GENERATOR_G
            .iter()
            .zip_eq(&scalar.to_bits_le())
            .filter_map(|(base, bit)| match bit {
                true => Some(base),
                false => None,
            })
            .sum()
    }

    /// Returns the Varuna universal prover.
    pub fn varuna_universal_prover() -> &'static UniversalProver<ConsolePairingCurve> {
        static INSTANCE: OnceCell<UniversalProver<ConsolePairingCurve>> = OnceCell::new();
        INSTANCE.get_or_init(|| {
            snarkvm_algorithms::polycommit::kzg10::UniversalParams::load()
                .expect("Failed to load universal SRS (KZG10).")
                .to_universal_prover()
                .expect("Failed to convert universal SRS (KZG10) to the prover.")
        })
    }

    /// Returns the Varuna universal verifier.
    pub fn varuna_universal_verifier() -> &'static UniversalVerifier<ConsolePairingCurve> {
        static INSTANCE: OnceCell<UniversalVerifier<ConsolePairingCurve>> = OnceCell::new();
        INSTANCE.get_or_init(|| {
            snarkvm_algorithms::polycommit::kzg10::UniversalParams::load()
                .expect("Failed to load universal SRS (KZG10).")
                .to_universal_verifier()
                .expect("Failed to convert universal SRS (KZG10) to the verifier.")
        })
    }

    /// Returns the sponge parameters used for the sponge in the Varuna SNARK.
    pub fn varuna_fs_parameters() -> &'static FiatShamirParameters {
        &VARUNA_FS_PARAMETERS
    }

    /// Returns the encryption domain as a constant field element.
    pub fn encryption_domain() -> Field {
        *ENCRYPTION_DOMAIN
    }

    /// Returns the graph key domain as a constant field element.
    pub fn graph_key_domain() -> Field {
        *GRAPH_KEY_DOMAIN
    }

    /// Returns the serial number domain as a constant field element.
    pub fn serial_number_domain() -> Field {
        *SERIAL_NUMBER_DOMAIN
    }

    /// Returns a BHP commitment with an input hasher of 256-bits and randomizer.
    pub fn commit_bhp256(input: &[bool], randomizer: &Scalar) -> Result<Field> {
        BHP_256.commit(input, randomizer)
    }

    /// Returns a BHP commitment with an input hasher of 512-bits and randomizer.
    pub fn commit_bhp512(input: &[bool], randomizer: &Scalar) -> Result<Field> {
        BHP_512.commit(input, randomizer)
    }

    /// Returns a BHP commitment with an input hasher of 768-bits and randomizer.
    pub fn commit_bhp768(input: &[bool], randomizer: &Scalar) -> Result<Field> {
        BHP_768.commit(input, randomizer)
    }

    /// Returns a BHP commitment with an input hasher of 1024-bits and randomizer.
    pub fn commit_bhp1024(input: &[bool], randomizer: &Scalar) -> Result<Field> {
        BHP_1024.commit(input, randomizer)
    }

    /// Returns a Pedersen commitment for the given (up to) 64-bit input and randomizer.
    pub fn commit_ped64(input: &[bool], randomizer: &Scalar) -> Result<Field> {
        PEDERSEN_64.commit(input, randomizer)
    }

    /// Returns a Pedersen commitment for the given (up to) 128-bit input and randomizer.
    pub fn commit_ped128(input: &[bool], randomizer: &Scalar) -> Result<Field> {
        PEDERSEN_128.commit(input, randomizer)
    }

    /// Returns a BHP commitment with an input hasher of 256-bits and randomizer.
    pub fn commit_to_group_bhp256(input: &[bool], randomizer: &Scalar) -> Result<Group> {
        BHP_256.commit_uncompressed(input, randomizer)
    }

    /// Returns a BHP commitment with an input hasher of 512-bits and randomizer.
    pub fn commit_to_group_bhp512(input: &[bool], randomizer: &Scalar) -> Result<Group> {
        BHP_512.commit_uncompressed(input, randomizer)
    }

    /// Returns a BHP commitment with an input hasher of 768-bits and randomizer.
    pub fn commit_to_group_bhp768(input: &[bool], randomizer: &Scalar) -> Result<Group> {
        BHP_768.commit_uncompressed(input, randomizer)
    }

    /// Returns a BHP commitment with an input hasher of 1024-bits and randomizer.
    pub fn commit_to_group_bhp1024(input: &[bool], randomizer: &Scalar) -> Result<Group> {
        BHP_1024.commit_uncompressed(input, randomizer)
    }

    /// Returns a Pedersen commitment for the given (up to) 64-bit input and randomizer.
    pub fn commit_to_group_ped64(input: &[bool], randomizer: &Scalar) -> Result<Group> {
        PEDERSEN_64.commit_uncompressed(input, randomizer)
    }

    /// Returns a Pedersen commitment for the given (up to) 128-bit input and randomizer.
    pub fn commit_to_group_ped128(input: &[bool], randomizer: &Scalar) -> Result<Group> {
        PEDERSEN_128.commit_uncompressed(input, randomizer)
    }

    /// Returns the BHP hash with an input hasher of 256-bits.
    pub fn hash_bhp256(mut input: &[bool]) -> Result<Field> {
        BHP_256.hash(&mut input)
    }

    /// Returns the BHP hash with an input hasher of 512-bits.
    pub fn hash_bhp512(mut input: &[bool]) -> Result<Field> {
        BHP_512.hash(&mut input)
    }

    /// Returns the BHP hash with an input hasher of 768-bits.
    pub fn hash_bhp768(mut input: &[bool]) -> Result<Field> {
        BHP_768.hash(&mut input)
    }

    /// Returns the BHP hash with an input hasher of 1024-bits.
    pub fn hash_bhp1024(mut input: &[bool]) -> Result<Field> {
        BHP_1024.hash(&mut input)
    }

    /// Returns the Keccak hash with a 256-bit output.
    pub fn hash_keccak256(mut input: &[bool]) -> Result<Vec<bool>> {
        Keccak256::default().hash(&mut input)
    }

    /// Returns the Keccak hash with a 384-bit output.
    pub fn hash_keccak384(mut input: &[bool]) -> Result<Vec<bool>> {
        Keccak384::default().hash(&mut input)
    }

    /// Returns the Keccak hash with a 512-bit output.
    pub fn hash_keccak512(mut input: &[bool]) -> Result<Vec<bool>> {
        Keccak512::default().hash(&mut input)
    }

    /// Returns the Pedersen hash for a given (up to) 64-bit input.
    pub fn hash_ped64(mut input: &[bool]) -> Result<Field> {
        PEDERSEN_64.hash(&mut input)
    }

    /// Returns the Pedersen hash for a given (up to) 128-bit input.
    pub fn hash_ped128(mut input: &[bool]) -> Result<Field> {
        PEDERSEN_128.hash(&mut input)
    }

    /// Returns the Poseidon hash with an input rate of 2.
    pub fn hash_psd2(mut input: &[Field]) -> Result<Field> {
        POSEIDON_2.hash(&mut input)
    }

    /// Returns the Poseidon hash with an input rate of 4.
    pub fn hash_psd4(mut input: &[Field]) -> Result<Field> {
        POSEIDON_4.hash(&mut input)
    }

    /// Returns the Poseidon hash with an input rate of 8.
    pub fn hash_psd8(mut input: &[Field]) -> Result<Field> {
        POSEIDON_8.hash(&mut input)
    }

    /// Returns the SHA-3 hash with a 256-bit output.
    pub fn hash_sha3_256(mut input: &[bool]) -> Result<Vec<bool>> {
        Sha3_256::default().hash(&mut input)
    }

    /// Returns the SHA-3 hash with a 384-bit output.
    pub fn hash_sha3_384(mut input: &[bool]) -> Result<Vec<bool>> {
        Sha3_384::default().hash(&mut input)
    }

    /// Returns the SHA-3 hash with a 512-bit output.
    pub fn hash_sha3_512(mut input: &[bool]) -> Result<Vec<bool>> {
        Sha3_512::default().hash(&mut input)
    }

    /// Returns the extended Poseidon hash with an input rate of 2.
    pub fn hash_many_psd2(input: &[Field], num_outputs: u16) -> Vec<Field> {
        POSEIDON_2.hash_many(input, num_outputs)
    }

    /// Returns the extended Poseidon hash with an input rate of 4.
    pub fn hash_many_psd4(input: &[Field], num_outputs: u16) -> Vec<Field> {
        POSEIDON_4.hash_many(input, num_outputs)
    }

    /// Returns the extended Poseidon hash with an input rate of 8.
    pub fn hash_many_psd8(input: &[Field], num_outputs: u16) -> Vec<Field> {
        POSEIDON_8.hash_many(input, num_outputs)
    }

    /// Returns the BHP hash with an input hasher of 256-bits.
    pub fn hash_to_group_bhp256(input: &[bool]) -> Result<Group> {
        BHP_256.hash_uncompressed(input)
    }

    /// Returns the BHP hash with an input hasher of 512-bits.
    pub fn hash_to_group_bhp512(input: &[bool]) -> Result<Group> {
        BHP_512.hash_uncompressed(input)
    }

    /// Returns the BHP hash with an input hasher of 768-bits.
    pub fn hash_to_group_bhp768(input: &[bool]) -> Result<Group> {
        BHP_768.hash_uncompressed(input)
    }

    /// Returns the BHP hash with an input hasher of 1024-bits.
    pub fn hash_to_group_bhp1024(input: &[bool]) -> Result<Group> {
        BHP_1024.hash_uncompressed(input)
    }

    /// Returns the Pedersen hash for a given (up to) 64-bit input.
    pub fn hash_to_group_ped64(input: &[bool]) -> Result<Group> {
        PEDERSEN_64.hash_uncompressed(input)
    }

    /// Returns the Pedersen hash for a given (up to) 128-bit input.
    pub fn hash_to_group_ped128(input: &[bool]) -> Result<Group> {
        PEDERSEN_128.hash_uncompressed(input)
    }

    /// Returns the Poseidon hash with an input rate of 2 on the affine curve.
    pub fn hash_to_group_psd2(input: &[Field]) -> Result<Group> {
        POSEIDON_2.hash_to_group(input)
    }

    /// Returns the Poseidon hash with an input rate of 4 on the affine curve.
    pub fn hash_to_group_psd4(input: &[Field]) -> Result<Group> {
        POSEIDON_4.hash_to_group(input)
    }

    /// Returns the Poseidon hash with an input rate of 8 on the affine curve.
    pub fn hash_to_group_psd8(input: &[Field]) -> Result<Group> {
        POSEIDON_8.hash_to_group(input)
    }

    /// Returns the Poseidon hash with an input rate of 2 on the scalar field.
    pub fn hash_to_scalar_psd2(input: &[Field]) -> Result<Scalar> {
        POSEIDON_2.hash_to_scalar(input)
    }

    /// Returns the Poseidon hash with an input rate of 4 on the scalar field.
    pub fn hash_to_scalar_psd4(input: &[Field]) -> Result<Scalar> {
        POSEIDON_4.hash_to_scalar(input)
    }

    /// Returns the Poseidon hash with an input rate of 8 on the scalar field.
    pub fn hash_to_scalar_psd8(input: &[Field]) -> Result<Scalar> {
        POSEIDON_8.hash_to_scalar(input)
    }

    /// Returns a Merkle tree with a BHP leaf hasher of 1024-bits and a BHP path hasher of 512-bits.
    pub fn merkle_tree_bhp<const DEPTH: u8>(leaves: &[Vec<bool>]) -> Result<BHPMerkleTree<DEPTH>> {
        MerkleTree::new(&*BHP_1024, &*BHP_512, leaves)
    }

    /// Returns a Merkle tree with a Poseidon leaf hasher with input rate of 4 and a Poseidon path hasher with input rate of 2.
    pub fn merkle_tree_psd<const DEPTH: u8>(leaves: &[Vec<Field>]) -> Result<PoseidonMerkleTree<DEPTH>> {
        MerkleTree::new(&*POSEIDON_4, &*POSEIDON_2, leaves)
    }

    /// Returns `true` if the given Merkle path is valid for the given root and leaf.
    pub fn verify_merkle_path_bhp<const DEPTH: u8>(path: &MerklePath<DEPTH>, root: &Field, leaf: &Vec<bool>) -> bool {
        path.verify(&*BHP_1024, &*BHP_512, root, leaf)
    }

    /// Returns `true` if the given Merkle path is valid for the given root and leaf.
    pub fn verify_merkle_path_psd<const DEPTH: u8>(path: &MerklePath<DEPTH>, root: &Field, leaf: &Vec<Field>) -> bool {
        path.verify(&*POSEIDON_4, &*POSEIDON_2, root, leaf)
    }
}

/// Initializes a new instance of group bases from a given input domain message.
fn new_bases(message: &str) -> Vec<Group> {
    // Hash the given message to a point on the curve, to initialize the starting base.
    let (base, _, _) = Blake2Xs::hash_to_curve::<ConsoleAffine>(message);

    // Compute the bases up to the size of the scalar field (in bits).
    let mut g = Group::new(base);
    let mut g_bases = Vec::with_capacity(Scalar::size_in_bits());
    for _ in 0..Scalar::size_in_bits() {
        g_bases.push(g);
        g = g.double();
    }
    g_bases
}

lazy_static! {
    /// The group bases for the Aleo signature and encryption schemes.
    pub static ref GENERATOR_G: Vec<Group> = new_bases("AleoAccountEncryptionAndSignatureScheme0");

    /// The Varuna sponge parameters.
    pub static ref VARUNA_FS_PARAMETERS: FiatShamirParameters = FiatShamir::sample_parameters();

    /// The encryption domain as a constant field element.
    pub static ref ENCRYPTION_DOMAIN: Field = Field::new_domain_separator("AleoSymmetricEncryption0");
    /// The graph key domain as a constant field element.
    pub static ref GRAPH_KEY_DOMAIN: Field = Field::new_domain_separator("AleoGraphKey0");
    /// The serial number domain as a constant field element.
    pub static ref SERIAL_NUMBER_DOMAIN: Field = Field::new_domain_separator("AleoSerialNumber0");

    /// The BHP hash function, which can take an input of up to 256 bits.
    pub static ref BHP_256: BHP256 = BHP256::setup("AleoBHP256").expect("Failed to setup BHP256");
    /// The BHP hash function, which can take an input of up to 512 bits.
    pub static ref BHP_512: BHP512 = BHP512::setup("AleoBHP512").expect("Failed to setup BHP512");
    /// The BHP hash function, which can take an input of up to 768 bits.
    pub static ref BHP_768: BHP768 = BHP768::setup("AleoBHP768").expect("Failed to setup BHP768");
    /// The BHP hash function, which can take an input of up to 1024 bits.
    pub static ref BHP_1024: BHP1024 = BHP1024::setup("AleoBHP1024").expect("Failed to setup BHP1024");

    /// The Pedersen hash function, which can take an input of up to 64 bits.
    pub static ref PEDERSEN_64: Pedersen64 = Pedersen64::setup("AleoPedersen64");
    /// The Pedersen hash function, which can take an input of up to 128 bits.
    pub static ref PEDERSEN_128: Pedersen128 = Pedersen128::setup("AleoPedersen128");

    /// The Poseidon hash function, using a rate of 2.
    pub static ref POSEIDON_2: Poseidon2 = Poseidon2::setup("AleoPoseidon2").expect("Failed to setup Poseidon2");
    /// The Poseidon hash function, using a rate of 4.
    pub static ref POSEIDON_4: Poseidon4 = Poseidon4::setup("AleoPoseidon4").expect("Failed to setup Poseidon4");
    /// The Poseidon hash function, using a rate of 8.
    pub static ref POSEIDON_8: Poseidon8 = Poseidon8::setup("AleoPoseidon8").expect("Failed to setup Poseidon8");
}

pub const TRANSACTION_PREFIX: &str = "at";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_g_scalar_multiply() {
        // Compute G^r.
        let scalar = Scalar::rand(&mut TestRng::default());
        let group = Network::g_scalar_multiply(&scalar);
        assert_eq!(group, Network::g_powers()[0] * scalar);
    }
}
