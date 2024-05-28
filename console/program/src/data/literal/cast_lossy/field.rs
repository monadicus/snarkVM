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

impl CastLossy<Address> for Field {
    /// Casts a `Field` to an `Address`.
    ///
    /// This operation attempts to recover the group element from the given field,
    /// which is then used to construct the address. See the documentation of `Field::cast_lossy`
    /// on the `Group` type for more details.
    #[inline]
    fn cast_lossy(&self) -> Address {
        // Perform a lossy cast to a group element.
        let group: Group = self.cast_lossy();
        // Convert the group element to an address.
        Address::new(group)
    }
}

impl CastLossy<Boolean> for Field {
    /// Casts a `Field` to a `Boolean`, with lossy truncation.
    /// This operation returns the least significant bit of the field.
    #[inline]
    fn cast_lossy(&self) -> Boolean {
        let bits_le = self.to_bits_le();
        debug_assert!(!bits_le.is_empty(), "An integer must have at least one bit");
        Boolean::new(bits_le[0])
    }
}

impl CastLossy<Field> for Field {
    /// Casts a `Field` to a `Field`.
    /// This is an identity cast, so it is **always** lossless.
    #[inline]
    fn cast_lossy(&self) -> Field {
        *self
    }
}

impl CastLossy<Group> for Field {
    /// Casts a `Field` to a `Group`.
    ///
    /// This operation attempts to recover the group element from the given field.
    ///
    /// If the field is a valid x-coordinate, then the group element is returned.
    /// If the field is not a valid x-coordinate, then if the field is the one element,
    /// the generator of the prime-order subgroup is returned.
    /// Otherwise, Elligator-2 is applied to the field element to recover a group element.
    #[inline]
    fn cast_lossy(&self) -> Group {
        match Group::from_x_coordinate(*self) {
            Ok(group) => group,
            Err(_) => match self.is_one() {
                true => Group::generator(),
                false => {
                    // Perform Elligator-2 on the field element, to recover a group element.
                    let result = Elligator2::encode(self);
                    debug_assert!(result.is_ok(), "Elligator-2 should never fail to encode a field element");
                    result.unwrap().0
                }
            },
        }
    }
}

impl<I: IntegerType> CastLossy<Integer<I>> for Field {
    /// Casts a `Field` to an `Integer`, with lossy truncation.
    /// This operation truncates the field to an integer.
    #[inline]
    fn cast_lossy(&self) -> Integer<I> {
        Integer::from_field_lossy(self)
    }
}

impl CastLossy<Scalar> for Field {
    /// Casts a `Field` to a `Scalar`, with lossy truncation.
    /// This operation truncates the field to a scalar.
    #[inline]
    fn cast_lossy(&self) -> Scalar {
        Scalar::from_field_lossy(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ITERATIONS: u64 = 10_000;

    #[test]
    fn test_field_to_address() {
        let rng = &mut TestRng::default();

        let field = Field::one();
        let address: Address = field.cast_lossy();
        assert_eq!(address, Address::new(Group::generator()));
        assert_eq!(address.to_group(), &Group::generator());

        let field = Field::zero();
        let address: Address = field.cast_lossy();
        assert_eq!(address, Address::zero());
        assert_eq!(address.to_group(), &Group::zero());

        for _ in 0..ITERATIONS {
            // Sample a random field.
            let field = Field::rand(rng);
            // Perform the operation.
            let candidate: Address = field.cast_lossy();
            // Compare the result against the group element. (This is the most we can do.)
            let expected: Group = field.cast_lossy();
            assert_eq!(Address::new(expected), candidate);
        }
    }

    #[test]
    fn test_field_to_boolean() {
        let rng = &mut TestRng::default();

        let field = Field::one();
        let boolean: Boolean = field.cast_lossy();
        assert_eq!(boolean, Boolean::new(true));

        let field = Field::zero();
        let boolean: Boolean = field.cast_lossy();
        assert_eq!(boolean, Boolean::new(false));

        for _ in 0..ITERATIONS {
            // Sample a random field.
            let field = Field::rand(rng);
            // Perform the operation.
            let candidate: Boolean = field.cast_lossy();
            // Compare the result against the least significant bit of the field.
            let expected = Boolean::new(field.to_bits_be().pop().unwrap());
            assert_eq!(expected, candidate);
        }
    }

    #[test]
    fn test_field_to_field() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random field.
            let field = Field::rand(rng);
            // Perform the operation.
            let candidate: Field = field.cast_lossy();
            assert_eq!(field, candidate);
        }
    }

    #[test]
    fn test_field_to_group() {
        let rng = &mut TestRng::default();

        let field = Field::one();
        let group: Group = field.cast_lossy();
        assert_eq!(group, Group::generator());

        let field = Field::zero();
        let group: Group = field.cast_lossy();
        assert_eq!(group, Group::zero());

        for _ in 0..ITERATIONS {
            // Sample a random field.
            let field = Field::rand(rng);
            // Perform the operation.
            let candidate: Group = field.cast_lossy();
            // Compare the result against the address. (This is the most we can do.)
            let expected: Address = field.cast_lossy();
            assert_eq!(expected.to_group(), &candidate);
        }
    }

    #[test]
    fn test_field_to_scalar() {
        let rng = &mut TestRng::default();

        let field = Field::one();
        let scalar: Scalar = field.cast_lossy();
        assert_eq!(scalar, Scalar::one());

        let field = Field::zero();
        let scalar: Scalar = field.cast_lossy();
        assert_eq!(scalar, Scalar::zero());

        for _ in 0..ITERATIONS {
            // Sample a random field.
            let field = Field::rand(rng);
            // Perform the operation.
            let candidate: Scalar = field.cast_lossy();
            assert_eq!(Scalar::from_field_lossy(&field), candidate);
        }
    }

    macro_rules! check_field_to_integer {
        ($type:ty) => {
            let rng = &mut TestRng::default();

            let field = Field::one();
            let integer: $type = field.cast_lossy();
            assert_eq!(integer, <$type>::one());

            let field = Field::zero();
            let integer: $type = field.cast_lossy();
            assert_eq!(integer, <$type>::zero());

            for _ in 0..ITERATIONS {
                // Sample a random field.
                let field = Field::rand(rng);
                // Perform the operation.
                let candidate: $type = field.cast_lossy();
                assert_eq!(<$type>::from_field_lossy(&field), candidate);
            }
        };
    }

    #[test]
    fn test_field_to_i8() {
        check_field_to_integer!(I8);
    }

    #[test]
    fn test_field_to_i16() {
        check_field_to_integer!(I16);
    }

    #[test]
    fn test_field_to_i32() {
        check_field_to_integer!(I32);
    }

    #[test]
    fn test_field_to_i64() {
        check_field_to_integer!(I64);
    }

    #[test]
    fn test_field_to_i128() {
        check_field_to_integer!(I128);
    }

    #[test]
    fn test_field_to_u8() {
        check_field_to_integer!(U8);
    }

    #[test]
    fn test_field_to_u16() {
        check_field_to_integer!(U16);
    }

    #[test]
    fn test_field_to_u32() {
        check_field_to_integer!(U32);
    }

    #[test]
    fn test_field_to_u64() {
        check_field_to_integer!(U64);
    }

    #[test]
    fn test_field_to_u128() {
        check_field_to_integer!(U128);
    }
}
