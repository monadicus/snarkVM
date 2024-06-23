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
    /// This operation returns the least significant bit of the scalar.
    #[inline]
    fn cast_lossy(&self) -> Boolean {
        let bits_le = self.to_bits_le();
        debug_assert!(!bits_le.is_empty(), "An integer must have at least one bit");
        bits_le[0].clone()
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
        self.to_field()
    }
}

impl<I: IntegerType> CastLossy<Integer<I>> for Scalar {
    /// Casts a `Scalar` to an `Integer`, with lossy truncation.
    #[inline]
    fn cast_lossy(&self) -> Integer<I> {
        // Note: We are reconstituting the integer from the scalar field.
        // This is safe as the number of bits in the integer is less than the scalar field modulus,
        // and thus will always fit within a single scalar field element.
        debug_assert!(I::BITS < <console::Scalar as console::SizeInBits>::size_in_bits() as u64);

        // Truncate the field to the size of the integer domain.
        // Slicing here is safe as the base field is larger than the integer domain.
        Integer::<I>::from_bits_le(&self.to_bits_le()[..usize::try_from(I::BITS).unwrap()])
    }
}

impl CastLossy<Scalar> for Scalar {
    /// Casts a `Scalar` to a `Scalar`.
    /// This is an identity cast, so it is **always** lossless.
    #[inline]
    fn cast_lossy(&self) -> Scalar {
        self.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::CastLossy as _;
    use console_root::{
        network::MainnetV0,
        prelude::{One, TestRng, Uniform, Zero},
    };
    use snarkvm_circuit_types::environment::{count_is, count_less_than, Circuit, Eject, Inject, Mode, UpdatableCount};

    use std::fmt::Debug;

    const ITERATIONS: usize = 100;

    fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console_root::types::Scalar, Scalar) {
        let console_value = match i {
            0 => console_root::types::Scalar::zero(),
            1 => console_root::types::Scalar::one(),
            _ => Uniform::rand(rng),
        };
        let circuit_value = Scalar::new(mode, console_value);
        (console_value, circuit_value)
    }

    check_cast_lossy!(cast_lossy, Scalar, console_root::types::Scalar);

    #[test]
    fn test_scalar_to_address() {
        check_cast_lossy::<Address, console_root::types::Address>(Mode::Constant, count_less_than!(4303, 0, 0, 0));
        check_cast_lossy::<Address, console_root::types::Address>(Mode::Public, count_is!(2029, 0, 6745, 6750));
        check_cast_lossy::<Address, console_root::types::Address>(Mode::Private, count_is!(2029, 0, 6745, 6750));
    }

    #[test]
    fn test_scalar_to_boolean() {
        check_cast_lossy::<Boolean, console_root::types::Boolean>(Mode::Constant, count_is!(251, 0, 0, 0));
        check_cast_lossy::<Boolean, console_root::types::Boolean>(Mode::Public, count_is!(0, 0, 501, 503));
        check_cast_lossy::<Boolean, console_root::types::Boolean>(Mode::Private, count_is!(0, 0, 501, 503));
    }

    #[test]
    fn test_scalar_to_field() {
        check_cast_lossy::<Field, console_root::types::Field>(Mode::Constant, count_is!(0, 0, 0, 0));
        check_cast_lossy::<Field, console_root::types::Field>(Mode::Public, count_is!(0, 0, 0, 0));
        check_cast_lossy::<Field, console_root::types::Field>(Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_scalar_to_group() {
        check_cast_lossy::<Group, console_root::types::Group>(Mode::Constant, count_less_than!(4303, 0, 0, 0));
        check_cast_lossy::<Group, console_root::types::Group>(Mode::Public, count_is!(2029, 0, 6745, 6750));
        check_cast_lossy::<Group, console_root::types::Group>(Mode::Private, count_is!(2029, 0, 6745, 6750));
    }

    #[test]
    fn test_scalar_to_i8() {
        check_cast_lossy::<I8, console_root::types::I8>(Mode::Constant, count_is!(251, 0, 0, 0));
        check_cast_lossy::<I8, console_root::types::I8>(Mode::Public, count_is!(0, 0, 501, 503));
        check_cast_lossy::<I8, console_root::types::I8>(Mode::Private, count_is!(0, 0, 501, 503));
    }

    #[test]
    fn test_scalar_to_i16() {
        check_cast_lossy::<I16, console_root::types::I16>(Mode::Constant, count_is!(251, 0, 0, 0));
        check_cast_lossy::<I16, console_root::types::I16>(Mode::Public, count_is!(0, 0, 501, 503));
        check_cast_lossy::<I16, console_root::types::I16>(Mode::Private, count_is!(0, 0, 501, 503));
    }

    #[test]
    fn test_scalar_to_i32() {
        check_cast_lossy::<I32, console_root::types::I32>(Mode::Constant, count_is!(251, 0, 0, 0));
        check_cast_lossy::<I32, console_root::types::I32>(Mode::Public, count_is!(0, 0, 501, 503));
        check_cast_lossy::<I32, console_root::types::I32>(Mode::Private, count_is!(0, 0, 501, 503));
    }

    #[test]
    fn test_scalar_to_i64() {
        check_cast_lossy::<I64, console_root::types::I64>(Mode::Constant, count_is!(251, 0, 0, 0));
        check_cast_lossy::<I64, console_root::types::I64>(Mode::Public, count_is!(0, 0, 501, 503));
        check_cast_lossy::<I64, console_root::types::I64>(Mode::Private, count_is!(0, 0, 501, 503));
    }

    #[test]
    fn test_scalar_to_i128() {
        check_cast_lossy::<I128, console_root::types::I128>(Mode::Constant, count_is!(251, 0, 0, 0));
        check_cast_lossy::<I128, console_root::types::I128>(Mode::Public, count_is!(0, 0, 501, 503));
        check_cast_lossy::<I128, console_root::types::I128>(Mode::Private, count_is!(0, 0, 501, 503));
    }

    #[test]
    fn test_scalar_to_scalar() {
        check_cast_lossy::<Scalar, console_root::types::Scalar>(Mode::Constant, count_is!(0, 0, 0, 0));
        check_cast_lossy::<Scalar, console_root::types::Scalar>(Mode::Public, count_is!(0, 0, 0, 0));
        check_cast_lossy::<Scalar, console_root::types::Scalar>(Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_scalar_to_u8() {
        check_cast_lossy::<U8, console_root::types::U8>(Mode::Constant, count_is!(251, 0, 0, 0));
        check_cast_lossy::<U8, console_root::types::U8>(Mode::Public, count_is!(0, 0, 501, 503));
        check_cast_lossy::<U8, console_root::types::U8>(Mode::Private, count_is!(0, 0, 501, 503));
    }

    #[test]
    fn test_scalar_to_u16() {
        check_cast_lossy::<U16, console_root::types::U16>(Mode::Constant, count_is!(251, 0, 0, 0));
        check_cast_lossy::<U16, console_root::types::U16>(Mode::Public, count_is!(0, 0, 501, 503));
        check_cast_lossy::<U16, console_root::types::U16>(Mode::Private, count_is!(0, 0, 501, 503));
    }

    #[test]
    fn test_scalar_to_u32() {
        check_cast_lossy::<U32, console_root::types::U32>(Mode::Constant, count_is!(251, 0, 0, 0));
        check_cast_lossy::<U32, console_root::types::U32>(Mode::Public, count_is!(0, 0, 501, 503));
        check_cast_lossy::<U32, console_root::types::U32>(Mode::Private, count_is!(0, 0, 501, 503));
    }

    #[test]
    fn test_scalar_to_u64() {
        check_cast_lossy::<U64, console_root::types::U64>(Mode::Constant, count_is!(251, 0, 0, 0));
        check_cast_lossy::<U64, console_root::types::U64>(Mode::Public, count_is!(0, 0, 501, 503));
        check_cast_lossy::<U64, console_root::types::U64>(Mode::Private, count_is!(0, 0, 501, 503));
    }

    #[test]
    fn test_scalar_to_u128() {
        check_cast_lossy::<U128, console_root::types::U128>(Mode::Constant, count_is!(251, 0, 0, 0));
        check_cast_lossy::<U128, console_root::types::U128>(Mode::Public, count_is!(0, 0, 501, 503));
        check_cast_lossy::<U128, console_root::types::U128>(Mode::Private, count_is!(0, 0, 501, 503));
    }
}
