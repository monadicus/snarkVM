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

impl Equal<Self> for Value {
    type Output = Boolean;

    /// Returns `true` if `self` and `other` are equal.
    fn is_equal(&self, other: &Self) -> Self::Output {
        match (self, other) {
            (Self::Plaintext(a), Self::Plaintext(b)) => a.is_equal(b),
            (Self::Record(a), Self::Record(b)) => a.is_equal(b),
            (Self::Future(a), Self::Future(b)) => a.is_equal(b),
            (Self::Plaintext(..), _) | (Self::Record(..), _) | (Self::Future(..), _) => Boolean::constant(false),
        }
    }

    /// Returns `true` if `self` and `other` are *not* equal.
    fn is_not_equal(&self, other: &Self) -> Self::Output {
        match (self, other) {
            (Self::Plaintext(a), Self::Plaintext(b)) => a.is_not_equal(b),
            (Self::Record(a), Self::Record(b)) => a.is_not_equal(b),
            (Self::Future(a), Self::Future(b)) => a.is_not_equal(b),
            (Self::Plaintext(..), _) | (Self::Record(..), _) | (Self::Future(..), _) => Boolean::constant(true),
        }
    }
}
