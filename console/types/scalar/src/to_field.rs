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

impl ToField for Scalar {
    type Field = Field;

    /// Returns the scalar as a field element.
    fn to_field(&self) -> Result<Self::Field> {
        // Note: We are reconstituting the scalar field into a base field.
        // This is safe as the scalar field modulus is less than the base field modulus,
        // and thus will always fit within a single base field element.
        debug_assert!(Scalar::size_in_bits() < Field::size_in_bits());

        Field::from_bits_le(&self.to_bits_le())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ITERATIONS: u64 = 10_000;

    #[test]
    fn test_to_field() -> Result<()> {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random value.
            let scalar: Scalar = Uniform::rand(&mut rng);

            let candidate = scalar.to_field()?;

            let expected = scalar.to_bits_le();
            for (index, candidate_bit) in candidate.to_bits_le().iter().enumerate() {
                match index < Scalar::size_in_bits() {
                    true => assert_eq!(expected[index], *candidate_bit),
                    false => assert!(!*candidate_bit),
                }
            }
        }
        Ok(())
    }
}
