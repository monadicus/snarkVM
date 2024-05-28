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
use crate::data::literal::cast_lossy::CastLossy;

impl Cast<Address> for Boolean {
    /// Casts a `Boolean` to an `Address`.
    #[inline]
    fn cast(&self) -> Result<Address> {
        Ok(self.cast_lossy())
    }
}

impl Cast<Boolean> for Boolean {
    /// Casts a `Boolean` to a `Boolean`.
    #[inline]
    fn cast(&self) -> Result<Boolean> {
        Ok(self.cast_lossy())
    }
}

impl Cast<Field> for Boolean {
    /// Casts a `Boolean` to a `Field`.
    #[inline]
    fn cast(&self) -> Result<Field> {
        Ok(self.cast_lossy())
    }
}

impl Cast<Group> for Boolean {
    /// Casts a `Boolean` to a `Group`.
    #[inline]
    fn cast(&self) -> Result<Group> {
        Ok(self.cast_lossy())
    }
}

impl<I: IntegerType> Cast<Integer<I>> for Boolean {
    /// Casts a `Boolean` to an `Integer`.
    #[inline]
    fn cast(&self) -> Result<Integer<I>> {
        match **self {
            true => Ok(Integer::one()),
            false => Ok(Integer::zero()),
        }
    }
}

impl Cast<Scalar> for Boolean {
    /// Casts a `Boolean` to a `Scalar`.
    #[inline]
    fn cast(&self) -> Result<Scalar> {
        Ok(self.cast_lossy())
    }
}
