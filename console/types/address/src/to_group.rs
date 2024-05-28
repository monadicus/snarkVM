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

impl Address {
    /// Returns the address as a group element.
    pub const fn to_group(&self) -> &Group {
        &self.address
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ITERATIONS: u64 = 10_000;

    #[test]
    fn test_to_group() -> Result<()> {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random value.
            let address = Address::rand(&mut rng);

            let candidate = address.to_group();

            let expected = address.to_bits_le();
            for (index, candidate_bit) in candidate.to_bits_le().iter().enumerate() {
                assert_eq!(expected[index], *candidate_bit);
            }
        }
        Ok(())
    }
}
