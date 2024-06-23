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

impl CastLossy<Address> for Scalar {
    /// Casts a `Scalar` to an `Address`.
    ///
    /// This operation converts the scalar into a field element, and then attempts to recover
    /// the group element to construct the address. See the documentation of `Field::cast_lossy`
    /// on the `Group` type for more details.
    #[inline]
    fn cast_lossy(&self) -> Address {
        let field: Field = self.cast_lossy();
        field.cast_lossy()
    }
}

impl CastLossy<Boolean> for Scalar {
    /// Casts a `Scalar` to a `Boolean`, with lossy truncation.
    /// This operation returns the least significant bit of the field.
    #[inline]
    fn cast_lossy(&self) -> Boolean {
        let bits_le = self.to_bits_le();
        debug_assert!(!bits_le.is_empty(), "An integer must have at least one bit");
        Boolean::new(bits_le[0])
    }
}

impl CastLossy<Group> for Scalar {
    /// Casts a `Scalar` to a `Group`.
    ///
    /// This operation converts the scalar into a field element, and then attempts to recover
    /// the group element. See the documentation of `Field::cast_lossy` on the `Group` type
    /// for more details.
    #[inline]
    fn cast_lossy(&self) -> Group {
        let field: Field = self.cast_lossy();
        field.cast_lossy()
    }
}

impl CastLossy<Field> for Scalar {
    /// Casts a `Scalar` to a `Field`.
    /// This operation is **always** lossless.
    #[inline]
    fn cast_lossy(&self) -> Field {
        let result = self.to_field();
        debug_assert!(result.is_ok(), "A scalar should always be able to be converted to a field");
        result.unwrap()
    }
}

impl<I: IntegerType> CastLossy<Integer<I>> for Scalar {
    /// Casts a `Scalar` to an `Integer`, with lossy truncation.
    #[inline]
    fn cast_lossy(&self) -> Integer<I> {
        // Note: We are reconstituting the integer from the scalar field.
        // This is safe as the number of bits in the integer is less than the scalar field modulus,
        // and thus will always fit within a single scalar field element.
        debug_assert!(I::BITS < Scalar::size_in_bits() as u64);

        // Truncate the field to the size of the integer domain.
        // Slicing here is safe as the base field is larger than the integer domain.
        let result = Integer::<I>::from_bits_le(&self.to_bits_le()[..usize::try_from(I::BITS).unwrap()]);
        debug_assert!(result.is_ok(), "A lossy integer should always be able to be constructed from scalar bits");
        result.unwrap()
    }
}

impl CastLossy<Scalar> for Scalar {
    /// Casts a `Scalar` to a `Scalar`.
    /// This is an identity cast, so it is **always** lossless.
    #[inline]
    fn cast_lossy(&self) -> Scalar {
        *self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ITERATIONS: u64 = 10_000;

    #[test]
    fn test_scalar_to_address() {
        let rng = &mut TestRng::default();

        let scalar = Scalar::one();
        let address: Address = scalar.cast_lossy();
        assert_eq!(address, Address::new(Group::generator()));
        assert_eq!(address.to_group(), &Group::generator());

        let scalar = Scalar::zero();
        let address: Address = scalar.cast_lossy();
        assert_eq!(address, Address::zero());
        assert_eq!(address.to_group(), &Group::zero());

        for _ in 0..ITERATIONS {
            // Sample a random scalar.
            let scalar = Scalar::rand(rng);
            // Perform the operation.
            let candidate = scalar.cast_lossy();
            // Compare the result against the group element. (This is the most we can do.)
            let expected: Group = scalar.cast_lossy();
            assert_eq!(Address::new(expected), candidate);
        }
    }

    #[test]
    fn test_scalar_to_boolean() {
        let rng = &mut TestRng::default();

        let scalar = Scalar::one();
        let boolean: Boolean = scalar.cast_lossy();
        assert_eq!(boolean, Boolean::new(true));

        let scalar = Scalar::zero();
        let boolean: Boolean = scalar.cast_lossy();
        assert_eq!(boolean, Boolean::new(false));

        for _ in 0..ITERATIONS {
            // Sample a random scalar.
            let scalar = Scalar::rand(rng);
            // Perform the operation.
            let candidate = scalar.cast_lossy();
            // Compare the result against the least significant bit of the scalar.
            let expected = Boolean::new(scalar.to_bits_be().pop().unwrap());
            assert_eq!(expected, candidate);
        }
    }

    #[test]
    fn test_scalar_to_field() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random scalar.
            let scalar = Scalar::rand(rng);
            // Perform the operation.
            let candidate = scalar.cast_lossy();
            assert_eq!(scalar.to_field().unwrap(), candidate);
        }
    }

    #[test]
    fn test_scalar_to_group() {
        let rng = &mut TestRng::default();

        let scalar = Scalar::one();
        let group: Group = scalar.cast_lossy();
        assert_eq!(group, Group::generator());

        let scalar = Scalar::zero();
        let group: Group = scalar.cast_lossy();
        assert_eq!(group, Group::zero());

        for _ in 0..ITERATIONS {
            // Sample a random scalar.
            let scalar = Scalar::rand(rng);
            // Perform the operation.
            let candidate: Group = scalar.cast_lossy();
            // Compare the result against the address. (This is the most we can do.)
            let expected: Address = scalar.cast_lossy();
            assert_eq!(expected.to_group(), &candidate);
        }
    }

    #[test]
    fn test_scalar_to_scalar() {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a random scalar.
            let scalar = Scalar::rand(rng);
            // Perform the operation.
            let candidate: Scalar = scalar.cast_lossy();
            assert_eq!(scalar, candidate);
        }
    }

    macro_rules! check_scalar_to_integer {
        ($type:ty) => {
            let rng = &mut TestRng::default();

            let scalar = Scalar::one();
            let integer: Integer<$type> = scalar.cast_lossy();
            assert_eq!(integer, Integer::<$type>::one());

            let scalar = Scalar::zero();
            let integer: Integer<$type> = scalar.cast_lossy();
            assert_eq!(integer, Integer::<$type>::zero());

            for _ in 0..ITERATIONS {
                // Sample a random scalar.
                let scalar = Scalar::rand(rng);
                // Perform the operation.
                let candidate: Integer<$type> = scalar.cast_lossy();
                // Compare the result against the least significant bits of the scalar.
                let expected =
                    Integer::<$type>::from_bits_le(&scalar.to_bits_le()[..usize::try_from(<$type>::BITS).unwrap()])
                        .unwrap();
                assert_eq!(expected, candidate);
            }
        };
    }

    #[test]
    fn test_scalar_to_i8() {
        check_scalar_to_integer!(i8);
    }

    #[test]
    fn test_scalar_to_i16() {
        check_scalar_to_integer!(i16);
    }

    #[test]
    fn test_scalar_to_i32() {
        check_scalar_to_integer!(i32);
    }

    #[test]
    fn test_scalar_to_i64() {
        check_scalar_to_integer!(i64);
    }

    #[test]
    fn test_scalar_to_i128() {
        check_scalar_to_integer!(i128);
    }

    #[test]
    fn test_scalar_to_u8() {
        check_scalar_to_integer!(u8);
    }

    #[test]
    fn test_scalar_to_u16() {
        check_scalar_to_integer!(u16);
    }

    #[test]
    fn test_scalar_to_u32() {
        check_scalar_to_integer!(u32);
    }

    #[test]
    fn test_scalar_to_u64() {
        check_scalar_to_integer!(u64);
    }

    #[test]
    fn test_scalar_to_u128() {
        check_scalar_to_integer!(u128);
    }
}
