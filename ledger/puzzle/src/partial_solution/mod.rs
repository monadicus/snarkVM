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

use crate::SolutionID;
use console::{account::Address, network::prelude::*, prelude::DeserializeExt};

/// The partial solution for the puzzle from a prover.
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct PartialSolution {
    /// The solution ID.
    solution_id: SolutionID,
    /// The epoch hash.
    epoch_hash: BlockHash,
    /// The address of the prover.
    address: Address,
    /// The counter for the solution.
    counter: u64,
}

impl PartialSolution {
    /// Initializes a new instance of the partial solution.
    pub fn new(epoch_hash: BlockHash, address: Address, counter: u64) -> Result<Self> {
        // Compute the solution ID.
        let solution_id = SolutionID::new(epoch_hash, address, counter)?;
        // Return the partial solution.
        Ok(Self { solution_id, epoch_hash, address, counter })
    }

    /// Returns the solution ID.
    pub const fn id(&self) -> SolutionID {
        self.solution_id
    }

    /// Returns the epoch hash of the solution.
    pub const fn epoch_hash(&self) -> BlockHash {
        self.epoch_hash
    }

    /// Returns the address of the prover.
    pub const fn address(&self) -> Address {
        self.address
    }

    /// Returns the counter for the solution.
    pub const fn counter(&self) -> u64 {
        self.counter
    }
}
