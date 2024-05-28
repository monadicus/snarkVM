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

mod configuration;
pub use configuration::*;

mod header_leaf;
pub use header_leaf::*;

mod transaction_leaf;
pub use transaction_leaf::*;

pub mod transition_leaf;
pub use transition_leaf::*;

mod bytes;
mod parse;
mod serialize;
mod verify;

use snarkvm_console_network::prelude::*;
use snarkvm_console_types::Field;

/// The state path proves existence of the transition leaf to either a global or local state root.
#[derive(Clone, PartialEq, Eq)]
pub struct StatePath {
    /// The global state root (Public).
    global_state_root: StateRoot,
    /// The Merkle path for the block hash.
    block_path: BlockPath,
    /// The block hash.
    block_hash: BlockHash,
    /// The previous block hash.
    previous_block_hash: BlockHash,
    /// The block header root.
    header_root: Field,
    /// The Merkle path for the block header leaf.
    header_path: HeaderPath,
    /// The block header leaf.
    header_leaf: HeaderLeaf,
    /// The Merkle path for the transaction ID.
    transactions_path: TransactionsPath,
    /// The transaction ID.
    transaction_id: TransactionID,
    /// The Merkle path for the transaction leaf.
    transaction_path: TransactionPath,
    /// The transaction leaf.
    transaction_leaf: TransactionLeaf,
    /// The transition root.
    transition_root: Field,
    /// The transition commitment.
    tcm: Field,
    /// The Merkle path for the transition leaf.
    transition_path: TransitionPath,
    /// The transition leaf.
    transition_leaf: TransitionLeaf,
}

impl StatePath {
    /// Initializes a new instance of `StatePath`.
    pub fn new_local(
        global_state_root: StateRoot,
        local_state_root: TransactionID,
        transaction_path: TransactionPath,
        transaction_leaf: TransactionLeaf,
        transition_root: Field,
        tcm: Field,
        transition_path: TransitionPath,
        transition_leaf: TransitionLeaf,
    ) -> Result<Self> {
        // Compute an arbitrary transactions path.
        let local_state_root_bits = local_state_root.to_bits_le();
        let transactions_tree: TransactionsTree = AleoNetwork::merkle_tree_bhp(&[local_state_root_bits.clone()])?;
        let transactions_path = transactions_tree.prove(0, &local_state_root_bits)?;
        let transactions_root = transactions_tree.root();

        // Compute an arbitrary block header path.
        let header_leaf = HeaderLeaf::new(0, *transactions_root);
        let header_leaf_bits = header_leaf.to_bits_le();
        let header_tree: HeaderTree = AleoNetwork::merkle_tree_bhp(&[header_leaf_bits.clone()])?;
        let header_path = header_tree.prove(0, &header_leaf_bits)?;
        let header_root = *header_tree.root();

        // Compute an arbitrary block path.
        let previous_block_hash: BlockHash = Field::zero().into();
        let block_hash: BlockHash = previous_block_hash;
        let block_hash_bits = block_hash.to_bits_le();
        let block_tree: BlockTree = AleoNetwork::merkle_tree_bhp(&[block_hash_bits.clone()])?;
        let block_path = block_tree.prove(0, &block_hash_bits)?;

        // Return the state path.
        Ok(Self {
            global_state_root,
            block_path,
            block_hash,
            previous_block_hash,
            header_root,
            header_path,
            header_leaf,
            transactions_path,
            transaction_id: local_state_root,
            transaction_path,
            transaction_leaf,
            transition_root,
            tcm,
            transition_path,
            transition_leaf,
        })
    }

    /// Initializes a new instance of `StatePath`.
    #[allow(clippy::too_many_arguments)]
    pub fn from(
        global_state_root: StateRoot,
        block_path: BlockPath,
        block_hash: BlockHash,
        previous_block_hash: BlockHash,
        header_root: Field,
        header_path: HeaderPath,
        header_leaf: HeaderLeaf,
        transactions_path: TransactionsPath,
        transaction_id: TransactionID,
        transaction_path: TransactionPath,
        transaction_leaf: TransactionLeaf,
        transition_root: Field,
        tcm: Field,
        transition_path: TransitionPath,
        transition_leaf: TransitionLeaf,
    ) -> Self {
        // Return the state path.
        Self {
            global_state_root,
            block_path,
            block_hash,
            previous_block_hash,
            header_root,
            header_path,
            header_leaf,
            transactions_path,
            transaction_id,
            transaction_path,
            transaction_leaf,
            transition_root,
            tcm,
            transition_path,
            transition_leaf,
        }
    }

    /// Returns the global state root.
    pub const fn global_state_root(&self) -> StateRoot {
        self.global_state_root
    }

    /// Returns the block path.
    pub const fn block_path(&self) -> &BlockPath {
        &self.block_path
    }

    /// Returns the block hash.
    pub const fn block_hash(&self) -> BlockHash {
        self.block_hash
    }

    /// Returns the previous block hash.
    pub const fn previous_block_hash(&self) -> BlockHash {
        self.previous_block_hash
    }

    /// Returns the block header root.
    pub const fn header_root(&self) -> &Field {
        &self.header_root
    }

    /// Returns the header path.
    pub const fn header_path(&self) -> &HeaderPath {
        &self.header_path
    }

    /// Returns the header leaf.
    pub const fn header_leaf(&self) -> &HeaderLeaf {
        &self.header_leaf
    }

    /// Returns the transactions path.
    pub const fn transactions_path(&self) -> &TransactionsPath {
        &self.transactions_path
    }

    /// Returns the transaction ID.
    pub const fn transaction_id(&self) -> &TransactionID {
        &self.transaction_id
    }

    /// Returns the Merkle path for the transaction leaf.
    pub const fn transaction_path(&self) -> &TransactionPath {
        &self.transaction_path
    }

    /// Returns the transaction leaf.
    pub const fn transaction_leaf(&self) -> &TransactionLeaf {
        &self.transaction_leaf
    }

    /// Returns the transition root.
    pub const fn transition_root(&self) -> &Field {
        &self.transition_root
    }

    /// Returns the transition commitment.
    pub const fn tcm(&self) -> &Field {
        &self.tcm
    }

    /// Returns the Merkle path for the transition leaf.
    pub const fn transition_path(&self) -> &TransitionPath {
        &self.transition_path
    }

    /// Returns the transition leaf.
    pub const fn transition_leaf(&self) -> &TransitionLeaf {
        &self.transition_leaf
    }
}

#[cfg(any(test, feature = "test"))]
pub mod test_helpers {
    use super::*;
    use snarkvm_console_network::prelude::TestRng;

    /// Randomly sample a state path to a global state root.
    /// If a `commitment` is given, it is used. Otherwise, a `commitment` is randomly sampled.
    pub fn sample_global_state_path(commitment: Option<Field>, rng: &mut TestRng) -> Result<StatePath> {
        // Prepare the commitment.
        let commitment = match commitment {
            Some(commitment) => commitment,
            None => Field::rand(rng),
        };

        // Prepare the tcm.
        let tcm = Field::rand(rng);

        // Construct the transition path and transaction leaf.
        let transition_leaf = TransitionLeaf::new_with_version(0, 3, commitment);
        let transition_tree: TransitionTree = AleoNetwork::merkle_tree_bhp(&[transition_leaf.to_bits_le()])?;
        let transition_root = *transition_tree.root();
        let transition_id = AleoNetwork::hash_bhp512(&(transition_root, tcm).to_bits_le())?;
        let transition_path = transition_tree.prove(0, &transition_leaf.to_bits_le())?;

        // Construct the transaction path and transaction leaf.
        let transaction_leaf = TransactionLeaf::new_execution(0, transition_id);
        let transaction_tree: TransactionTree = AleoNetwork::merkle_tree_bhp(&[transaction_leaf.to_bits_le()])?;
        let transaction_id = *transaction_tree.root();
        let transaction_path = transaction_tree.prove(0, &transaction_leaf.to_bits_le())?;

        // Construct the transactions path.
        let transactions_tree: TransactionsTree = AleoNetwork::merkle_tree_bhp(&[transaction_id.to_bits_le()])?;
        let transactions_root = transactions_tree.root();
        let transactions_path = transactions_tree.prove(0, &transaction_id.to_bits_le())?;

        // Construct the block header path.
        let header_leaf = HeaderLeaf::new(1, *transactions_root);
        let header_tree: HeaderTree =
            AleoNetwork::merkle_tree_bhp(&[Field::zero().to_bits_le(), header_leaf.to_bits_le()])?;
        let header_root = header_tree.root();
        let header_path = header_tree.prove(1, &header_leaf.to_bits_le())?;

        let previous_block_hash: N::BlockHash = Field::rand(rng).into();
        let preimage = (*previous_block_hash).to_bits_le().into_iter().chain(header_root.to_bits_le());
        let block_hash = AleoNetwork::hash_bhp1024(&preimage.collect::<Vec<_>>())?;

        // Construct the global state root and block path.
        let block_tree: BlockTree = AleoNetwork::merkle_tree_bhp(&[block_hash.to_bits_le()])?;
        let global_state_root = *block_tree.root();
        let block_path = block_tree.prove(0, &block_hash.to_bits_le())?;

        Ok(StatePath::from(
            global_state_root.into(),
            block_path,
            block_hash.into(),
            previous_block_hash,
            *header_root,
            header_path,
            header_leaf,
            transactions_path,
            transaction_id.into(),
            transaction_path,
            transaction_leaf,
            transition_root,
            tcm,
            transition_path,
            transition_leaf,
        ))
    }

    /// Randomly sample a state path to a local state root.
    /// If a `commitment` is given, it is used. Otherwise, a `commitment` is randomly sampled.
    pub fn sample_local_state_path(commitment: Option<Field>, rng: &mut TestRng) -> Result<StatePath> {
        // Prepare the commitment.
        let commitment = match commitment {
            Some(commitment) => commitment,
            None => Field::rand(rng),
        };

        // Prepare the tcm.
        let tcm = Field::rand(rng);

        // Construct the transition path and transaction leaf.
        let transition_leaf = TransitionLeaf::new_with_version(0, 3, commitment);
        let transition_tree: TransitionTree = AleoNetwork::merkle_tree_bhp(&[transition_leaf.to_bits_le()])?;
        let transition_root = *transition_tree.root();
        let transition_id = AleoNetwork::hash_bhp512(&(transition_root, tcm).to_bits_le())?;
        let transition_path = transition_tree.prove(0, &transition_leaf.to_bits_le())?;

        // Construct the transaction path and transaction leaf.
        let transaction_leaf = TransactionLeaf::new_execution(0, transition_id);
        let transaction_tree: TransactionTree = AleoNetwork::merkle_tree_bhp(&[transaction_leaf.to_bits_le()])?;
        let transaction_id = *transaction_tree.root();
        let transaction_path = transaction_tree.prove(0, &transaction_leaf.to_bits_le())?;

        // Construct the transactions path.
        let transactions_tree: TransactionsTree = AleoNetwork::merkle_tree_bhp(&[transaction_id.to_bits_le()])?;
        let transactions_root = transactions_tree.root();
        let transactions_path = transactions_tree.prove(0, &transaction_id.to_bits_le())?;

        // Prepare random header leaves.
        let random_header_index = rng.gen_range(0..7);
        let mut random_header_leaves = vec![Field::zero().to_bits_le(); (random_header_index + 1) as usize];
        let header_leaf = HeaderLeaf::new(random_header_index, *transactions_root);
        random_header_leaves[random_header_index as usize] = header_leaf.to_bits_le();

        // Construct the block header path.
        let header_tree: HeaderTree = AleoNetwork::merkle_tree_bhp(&random_header_leaves)?;
        let header_root = header_tree.root();
        let header_path = header_tree.prove(random_header_index as usize, &header_leaf.to_bits_le())?;

        let previous_block_hash: N::BlockHash = Field::rand(rng).into();
        let block_hash: N::BlockHash = Field::rand(rng).into();

        // Construct the global state root and block path.
        let block_tree: BlockTree = AleoNetwork::merkle_tree_bhp(&[block_hash.to_bits_le()])?;
        let global_state_root = *block_tree.root();
        let block_path = block_tree.prove(0, &block_hash.to_bits_le())?;

        Ok(StatePath::from(
            global_state_root.into(),
            block_path,
            block_hash,
            previous_block_hash,
            *header_root,
            header_path,
            header_leaf,
            transactions_path,
            transaction_id.into(),
            transaction_path,
            transaction_leaf,
            transition_root,
            tcm,
            transition_path,
            transition_leaf,
        ))
    }
}
