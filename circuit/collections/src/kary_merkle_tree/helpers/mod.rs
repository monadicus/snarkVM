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

mod leaf_hash;
pub use leaf_hash::*;

mod path_hash;
pub use path_hash::*;
use snarkvm_circuit_types::environment::Circuit;

#[derive(Clone, Debug)]
pub struct BooleanHash<const VARIANT: usize>(pub [Boolean; VARIANT]);

impl<const VARIANT: usize> Default for BooleanHash<VARIANT> {
    /// Initializes a new "empty" boolean hash.
    fn default() -> Self {
        Self::new(Mode::Constant, console::kary_merkle_tree::BooleanHash::new())
    }
}

#[cfg(console)]
impl<const VARIANT: usize> Inject for BooleanHash<VARIANT> {
    type Primitive = console::kary_merkle_tree::BooleanHash<VARIANT>;

    /// Initializes a boolean hash from the given mode and native boolean hash.
    fn new(mode: Mode, hash: Self::Primitive) -> Self {
        // Initialize the boolean hash.
        let hash = hash.iter().map(|b| Boolean::new(mode, *b)).collect::<Vec<_>>();

        // Return the boolean hash.
        match hash.len() == VARIANT {
            true => Self(hash.try_into().unwrap()),
            false => Circuit::halt("Boolean hash is not the correct length"),
        }
    }
}

#[cfg(console)]
impl<const VARIANT: usize> Eject for BooleanHash<VARIANT> {
    type Primitive = console::kary_merkle_tree::BooleanHash<VARIANT>;

    /// Ejects the mode of the boolean hash.
    fn eject_mode(&self) -> Mode {
        self.0.eject_mode()
    }

    /// Ejects the Merkle path.
    fn eject_value(&self) -> Self::Primitive {
        console::kary_merkle_tree::BooleanHash::<VARIANT>(self.0.eject_value().try_into().unwrap())
    }
}

impl<const VARIANT: usize> Equal<Self> for BooleanHash<VARIANT> {
    type Output = Boolean;

    /// Returns `true` if `self` and `other` are equal.
    fn is_equal(&self, other: &Self) -> Self::Output {
        self.iter().zip_eq(other.iter()).map(|(a, b)| a.is_equal(b)).fold(Boolean::constant(true), Boolean::bitand)
    }

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        !self.is_equal(other)
    }
}

impl<const VARIANT: usize> Ternary for BooleanHash<VARIANT> {
    type Boolean = Boolean;
    type Output = Self;

    /// Returns `first` if `condition` is `true`, otherwise returns `second`.
    fn ternary(condition: &Self::Boolean, first: &Self, second: &Self) -> Self::Output {
        let mut result = Vec::with_capacity(VARIANT);
        for (a, b) in first.iter().zip_eq(second.iter()) {
            result.push(Self::Boolean::ternary(condition, a, b));
        }
        Self(result.try_into().unwrap())
    }
}

impl<const VARIANT: usize> Deref for BooleanHash<VARIANT> {
    type Target = [Boolean; VARIANT];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
