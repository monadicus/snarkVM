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

use snarkvm_console_types::{prelude::*, Field};

use core::ops::{Index, IndexMut, Range};

#[derive(Copy, Clone, Debug)]
pub struct State<const RATE: usize, const CAPACITY: usize> {
    capacity_state: [Field; CAPACITY],
    rate_state: [Field; RATE],
}

impl<const RATE: usize, const CAPACITY: usize> Default for State<RATE, CAPACITY> {
    fn default() -> Self {
        Self { capacity_state: [Field::zero(); CAPACITY], rate_state: [Field::zero(); RATE] }
    }
}

impl<const RATE: usize, const CAPACITY: usize> State<RATE, CAPACITY> {
    /// Returns a reference to a range of the rate state.
    pub(super) fn rate_state(&self, range: Range<usize>) -> &[Field] {
        &self.rate_state[range]
    }

    /// Returns a mutable rate state.
    pub(super) fn rate_state_mut(&mut self) -> &mut [Field; RATE] {
        &mut self.rate_state
    }
}

impl<const RATE: usize, const CAPACITY: usize> State<RATE, CAPACITY> {
    /// Returns an immutable iterator over the state.
    pub fn iter(&self) -> impl Iterator<Item = &Field> + Clone {
        self.capacity_state.iter().chain(self.rate_state.iter())
    }

    /// Returns an mutable iterator over the state.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Field> {
        self.capacity_state.iter_mut().chain(self.rate_state.iter_mut())
    }
}

impl<const RATE: usize, const CAPACITY: usize> Index<usize> for State<RATE, CAPACITY> {
    type Output = Field;

    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < RATE + CAPACITY, "Index out of bounds: index is {} but length is {}", index, RATE + CAPACITY);
        if index < CAPACITY { &self.capacity_state[index] } else { &self.rate_state[index - CAPACITY] }
    }
}

impl<const RATE: usize, const CAPACITY: usize> IndexMut<usize> for State<RATE, CAPACITY> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert!(index < RATE + CAPACITY, "Index out of bounds: index is {} but length is {}", index, RATE + CAPACITY);
        if index < CAPACITY { &mut self.capacity_state[index] } else { &mut self.rate_state[index - CAPACITY] }
    }
}
