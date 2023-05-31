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

impl<E: Environment> Zero for Field<E> {
    /// Returns the `0` element of the field.
    fn zero() -> Self {
        Self::new(E::Field::zero())
    }

    /// Returns `true` if the element is zero.
    fn is_zero(&self) -> bool {
        self.field.is_zero()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network_environment::Console;

    type CurrentEnvironment = Console;

    const ITERATIONS: u64 = 100;

    #[test]
    fn test_zero() {
        let zero = Field::<CurrentEnvironment>::zero();

        for bit in zero.to_bits_le().iter() {
            assert!(!bit)
        }
    }

    #[test]
    fn test_is_zero() {
        assert!(Field::<CurrentEnvironment>::zero().is_zero());

        let mut rng = TestRng::default();

        // Note: This test technically has a `1 / MODULUS` probability of being flaky.
        for _ in 0..ITERATIONS {
            let field: Field<CurrentEnvironment> = Uniform::rand(&mut rng);
            assert!(!field.is_zero());
        }
    }
}
