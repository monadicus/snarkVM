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

use snarkvm_circuit_types::environment::Circuit;

use super::*;

impl<I: IntegerType> Cast<Address> for Integer<I> {
    /// Casts an `Integer` to an `Address`.
    ///
    /// This operation converts the integer to a field element, and then attempts to recover
    /// the group element by treating the field element as an x-coordinate. The group element
    /// is then converted to an address.
    ///
    /// To cast arbitrary integers to addresses, use `Integer::cast_lossy`.
    #[inline]
    fn cast(&self) -> Address {
        let field: Field = self.cast();
        field.cast()
    }
}

impl<I: IntegerType> Cast<Boolean> for Integer<I> {
    /// Casts an `Integer` to a `Boolean`, if the integer is zero or one.
    ///
    /// To cast arbitrary integers to booleans, use `Integer::cast_lossy`.
    #[inline]
    fn cast(&self) -> Boolean {
        let is_one = self.is_one();
        Circuit::assert(self.is_zero().bitor(&is_one));
        is_one
    }
}

impl<I: IntegerType> Cast<Field> for Integer<I> {
    /// Casts an `Integer` to a `Field`.
    #[inline]
    fn cast(&self) -> Field {
        self.to_field()
    }
}

impl<I: IntegerType> Cast<Group> for Integer<I> {
    /// Casts an `Integer` to a `Group`.
    ///
    /// This operation converts the integer to a field element, and then attempts to recover
    /// the group element by treating the field element as an x-coordinate.
    ///
    /// To cast arbitrary integers to groups, use `Integer::cast_lossy`.
    #[inline]
    fn cast(&self) -> Group {
        let field: Field = self.cast();
        field.cast()
    }
}

impl<I0: IntegerType, I1: IntegerType> Cast<Integer<I1>> for Integer<I0> {
    /// Casts an `Integer` to another `Integer`, if the conversion is lossless.
    #[inline]
    fn cast(&self) -> Integer<I1> {
        let mut bits_le = self.to_bits_le();
        match (I0::is_signed(), I1::is_signed()) {
            // If the two types are both unsigned, instantiate the new integer from the bits.
            (false, false) => Integer::<I1>::from_bits_le(&bits_le),
            // If the source type is unsigned and the destination type is signed, perform the required checks.
            (false, true) => match I0::BITS < I1::BITS {
                // If the source type is smaller than the destination type, instantiate the new integer from the bits.
                true => Integer::<I1>::from_bits_le(&bits_le),
                // If the source type is the same size or larger than the destination type, check that the most significant bits are zero.
                // Then instantiate the new integer from the lower bits.
                false => {
                    Boolean::assert_bits_are_zero(&bits_le[(I1::BITS.saturating_sub(1) as usize)..]);
                    Integer::<I1>::from_bits_le(&bits_le[..(I1::BITS as usize)])
                }
            },
            // If the source type is signed and the destination type is unsigned, perform the required checks.
            (true, false) => match I0::BITS <= I1::BITS {
                // If the source type is smaller than or equal to the destination type, check that the most significant bit is zero.
                // Then instantiate the new integer from the lower bits.
                true => {
                    Circuit::assert(!&bits_le[I0::BITS.saturating_sub(1) as usize]);
                    Integer::<I1>::from_bits_le(&bits_le)
                }
                // If the source type is larger than the destination type, check that the upper bits are zero.
                // Then instantiate the new integer from the lower bits.
                false => {
                    Boolean::assert_bits_are_zero(&bits_le[(I1::BITS as usize)..]);
                    Integer::<I1>::from_bits_le(&bits_le[..(I1::BITS as usize)])
                }
            },
            // If the two types are both signed, perform the required checks.
            (true, true) => match I0::BITS <= I1::BITS {
                // If the source type is smaller than or equal to the destination type, sign extend the source integer.
                // Then instantiate the new integer from the bits.
                true => {
                    bits_le.resize(I1::BITS as usize, self.msb().clone());
                    Integer::<I1>::from_bits_le(&bits_le)
                }
                // If the source type is larger than the destination type, check that the upper bits match the most significant bit.
                // Then instantiate the new integer from the appropriate lower bits.
                false => {
                    // Get the most significant bit.
                    let msb = match bits_le.pop() {
                        Some(bit) => bit,
                        None => Circuit::halt("Failed to extract the MSB from the integer."),
                    };
                    // Check that the upper bits match the most significant bit.
                    let upper_bits = bits_le.iter().skip(I1::BITS.saturating_sub(1) as usize);
                    for bit in upper_bits {
                        Circuit::assert_eq(&msb, bit);
                    }
                    // Instantiate the new integer from the lower bits and the most significant bit.
                    let mut lower_bits: Vec<_> =
                        bits_le.into_iter().take(I1::BITS.saturating_sub(1) as usize).collect();
                    lower_bits.push(msb);
                    Integer::<I1>::from_bits_le(&lower_bits)
                }
            },
        }
    }
}

impl<I: IntegerType> Cast<Scalar> for Integer<I> {
    /// Casts an `Integer` to a `Scalar`.
    #[inline]
    fn cast(&self) -> Scalar {
        let bits_le = self.to_bits_le();
        Scalar::from_bits_le(&bits_le)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::Cast as _;
    use console_root::{
        network::MainnetV0,
        prelude::{One, TestRng, Uniform, Zero},
    };
    use snarkvm_circuit_types::environment::{count_is, count_less_than, Circuit, Eject, Inject, Mode, UpdatableCount};

    use std::fmt::Debug;

    const ITERATIONS: usize = 1000;

    fn sample_values<I: IntegerType>(
        i: usize,
        mode: Mode,
        rng: &mut TestRng,
    ) -> (console_root::types::integers::Integer<I>, Integer<I>) {
        let console_value = match i {
            0 => console_root::types::integers::Integer::<I>::zero(),
            1 => console_root::types::integers::Integer::<I>::one(),
            2 => console_root::types::integers::Integer::<I>::new(I::MAX),
            3 => console_root::types::integers::Integer::<I>::new(I::MIN),
            4 if I::is_signed() => -console_root::types::integers::Integer::<I>::one(),
            _ => Uniform::rand(rng),
        };
        let circuit_value = Integer::<I>::new(mode, console_value);
        (console_value, circuit_value)
    }

    mod i8 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console_root::types::I8, I8) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, I8, console_root::types::I8);

        #[test]
        fn test_i8_to_address() {
            check_cast::<Address, console_root::types::Address>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Address, console_root::types::Address>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Address, console_root::types::Address>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_i8_to_boolean() {
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Constant, count_is!(16, 0, 0, 0));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Public, count_is!(16, 0, 5, 6));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Private, count_is!(16, 0, 5, 6));
        }

        #[test]
        fn test_i8_to_field() {
            check_cast::<Field, console_root::types::Field>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_group() {
            check_cast::<Group, console_root::types::Group>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Group, console_root::types::Group>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Group, console_root::types::Group>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_i8_to_i8() {
            check_cast::<I8, console_root::types::I8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8, console_root::types::I8>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I8, console_root::types::I8>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_i16() {
            check_cast::<I16, console_root::types::I16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16, console_root::types::I16>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I16, console_root::types::I16>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_i32() {
            check_cast::<I32, console_root::types::I32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32, console_root::types::I32>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I32, console_root::types::I32>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_i64() {
            check_cast::<I64, console_root::types::I64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_i128() {
            check_cast::<I128, console_root::types::I128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_scalar() {
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i8_to_u8() {
            check_cast::<U8, console_root::types::U8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8, console_root::types::U8>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U8, console_root::types::U8>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i8_to_u16() {
            check_cast::<U16, console_root::types::U16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16, console_root::types::U16>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U16, console_root::types::U16>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i8_to_u32() {
            check_cast::<U32, console_root::types::U32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32, console_root::types::U32>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U32, console_root::types::U32>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i8_to_u64() {
            check_cast::<U64, console_root::types::U64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64, console_root::types::U64>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U64, console_root::types::U64>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i8_to_u128() {
            check_cast::<U128, console_root::types::U128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128, console_root::types::U128>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U128, console_root::types::U128>(Mode::Private, count_is!(0, 0, 0, 1));
        }
    }

    mod i16 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console_root::types::I16, I16) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, I16, console_root::types::I16);

        #[test]
        fn test_i16_to_address() {
            check_cast::<Address, console_root::types::Address>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Address, console_root::types::Address>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Address, console_root::types::Address>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_i16_to_boolean() {
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Constant, count_is!(32, 0, 0, 0));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Public, count_is!(32, 0, 5, 6));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Private, count_is!(32, 0, 5, 6));
        }

        #[test]
        fn test_i16_to_field() {
            check_cast::<Field, console_root::types::Field>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i16_to_group() {
            check_cast::<Group, console_root::types::Group>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Group, console_root::types::Group>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Group, console_root::types::Group>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_i16_to_i8() {
            check_cast::<I8, console_root::types::I8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8, console_root::types::I8>(Mode::Public, count_is!(0, 0, 0, 8));
            check_cast::<I8, console_root::types::I8>(Mode::Private, count_is!(0, 0, 0, 8));
        }

        #[test]
        fn test_i16_to_i16() {
            check_cast::<I16, console_root::types::I16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16, console_root::types::I16>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I16, console_root::types::I16>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i16_to_i32() {
            check_cast::<I32, console_root::types::I32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32, console_root::types::I32>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I32, console_root::types::I32>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i16_to_i64() {
            check_cast::<I64, console_root::types::I64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i16_to_i128() {
            check_cast::<I128, console_root::types::I128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i16_to_scalar() {
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i16_to_u8() {
            check_cast::<U8, console_root::types::U8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8, console_root::types::U8>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U8, console_root::types::U8>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i16_to_u16() {
            check_cast::<U16, console_root::types::U16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16, console_root::types::U16>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U16, console_root::types::U16>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i16_to_u32() {
            check_cast::<U32, console_root::types::U32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32, console_root::types::U32>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U32, console_root::types::U32>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i16_to_u64() {
            check_cast::<U64, console_root::types::U64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64, console_root::types::U64>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U64, console_root::types::U64>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i16_to_u128() {
            check_cast::<U128, console_root::types::U128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128, console_root::types::U128>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U128, console_root::types::U128>(Mode::Private, count_is!(0, 0, 0, 1));
        }
    }

    mod i32 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console_root::types::I32, I32) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, I32, console_root::types::I32);

        #[test]
        fn test_i32_to_address() {
            check_cast::<Address, console_root::types::Address>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Address, console_root::types::Address>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Address, console_root::types::Address>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_i32_to_boolean() {
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Constant, count_is!(64, 0, 0, 0));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Public, count_is!(64, 0, 5, 6));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Private, count_is!(64, 0, 5, 6));
        }

        #[test]
        fn test_i32_to_field() {
            check_cast::<Field, console_root::types::Field>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i32_to_group() {
            check_cast::<Group, console_root::types::Group>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Group, console_root::types::Group>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Group, console_root::types::Group>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_i32_to_i8() {
            check_cast::<I8, console_root::types::I8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8, console_root::types::I8>(Mode::Public, count_is!(0, 0, 0, 24));
            check_cast::<I8, console_root::types::I8>(Mode::Private, count_is!(0, 0, 0, 24));
        }

        #[test]
        fn test_i32_to_i16() {
            check_cast::<I16, console_root::types::I16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16, console_root::types::I16>(Mode::Public, count_is!(0, 0, 0, 16));
            check_cast::<I16, console_root::types::I16>(Mode::Private, count_is!(0, 0, 0, 16));
        }

        #[test]
        fn test_i32_to_i32() {
            check_cast::<I32, console_root::types::I32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32, console_root::types::I32>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I32, console_root::types::I32>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i32_to_i64() {
            check_cast::<I64, console_root::types::I64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i32_to_i128() {
            check_cast::<I128, console_root::types::I128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i32_to_scalar() {
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i32_to_u8() {
            check_cast::<U8, console_root::types::U8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8, console_root::types::U8>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U8, console_root::types::U8>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i32_to_u16() {
            check_cast::<U16, console_root::types::U16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16, console_root::types::U16>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U16, console_root::types::U16>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i32_to_u32() {
            check_cast::<U32, console_root::types::U32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32, console_root::types::U32>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U32, console_root::types::U32>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i32_to_u64() {
            check_cast::<U64, console_root::types::U64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64, console_root::types::U64>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U64, console_root::types::U64>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i32_to_u128() {
            check_cast::<U128, console_root::types::U128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128, console_root::types::U128>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U128, console_root::types::U128>(Mode::Private, count_is!(0, 0, 0, 1));
        }
    }

    mod i64 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console_root::types::I64, I64) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, I64, console_root::types::I64);

        #[test]
        fn test_i64_to_address() {
            check_cast::<Address, console_root::types::Address>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Address, console_root::types::Address>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Address, console_root::types::Address>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_i64_to_boolean() {
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Constant, count_is!(128, 0, 0, 0));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Public, count_is!(128, 0, 5, 6));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Private, count_is!(128, 0, 5, 6));
        }

        #[test]
        fn test_i64_to_field() {
            check_cast::<Field, console_root::types::Field>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i64_to_group() {
            check_cast::<Group, console_root::types::Group>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Group, console_root::types::Group>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Group, console_root::types::Group>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_i64_to_i8() {
            check_cast::<I8, console_root::types::I8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8, console_root::types::I8>(Mode::Public, count_is!(0, 0, 0, 56));
            check_cast::<I8, console_root::types::I8>(Mode::Private, count_is!(0, 0, 0, 56));
        }

        #[test]
        fn test_i64_to_i16() {
            check_cast::<I16, console_root::types::I16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16, console_root::types::I16>(Mode::Public, count_is!(0, 0, 0, 48));
            check_cast::<I16, console_root::types::I16>(Mode::Private, count_is!(0, 0, 0, 48));
        }

        #[test]
        fn test_i64_to_i32() {
            check_cast::<I32, console_root::types::I32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32, console_root::types::I32>(Mode::Public, count_is!(0, 0, 0, 32));
            check_cast::<I32, console_root::types::I32>(Mode::Private, count_is!(0, 0, 0, 32));
        }

        #[test]
        fn test_i64_to_i64() {
            check_cast::<I64, console_root::types::I64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i64_to_i128() {
            check_cast::<I128, console_root::types::I128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i64_to_scalar() {
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i64_to_u8() {
            check_cast::<U8, console_root::types::U8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8, console_root::types::U8>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U8, console_root::types::U8>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i64_to_u16() {
            check_cast::<U16, console_root::types::U16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16, console_root::types::U16>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U16, console_root::types::U16>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i64_to_u32() {
            check_cast::<U32, console_root::types::U32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32, console_root::types::U32>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U32, console_root::types::U32>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i64_to_u64() {
            check_cast::<U64, console_root::types::U64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64, console_root::types::U64>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U64, console_root::types::U64>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i64_to_u128() {
            check_cast::<U128, console_root::types::U128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128, console_root::types::U128>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U128, console_root::types::U128>(Mode::Private, count_is!(0, 0, 0, 1));
        }
    }

    mod i128 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console_root::types::I128, I128) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, I128, console_root::types::I128);

        #[test]
        fn test_i128_to_address() {
            check_cast::<Address, console_root::types::Address>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Address, console_root::types::Address>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Address, console_root::types::Address>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_i128_to_boolean() {
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Constant, count_is!(256, 0, 0, 0));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Public, count_is!(256, 0, 5, 6));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Private, count_is!(256, 0, 5, 6));
        }

        #[test]
        fn test_i128_to_field() {
            check_cast::<Field, console_root::types::Field>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i128_to_group() {
            check_cast::<Group, console_root::types::Group>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Group, console_root::types::Group>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Group, console_root::types::Group>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_i128_to_i8() {
            check_cast::<I8, console_root::types::I8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8, console_root::types::I8>(Mode::Public, count_is!(0, 0, 0, 120));
            check_cast::<I8, console_root::types::I8>(Mode::Private, count_is!(0, 0, 0, 120));
        }

        #[test]
        fn test_i128_to_i16() {
            check_cast::<I16, console_root::types::I16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16, console_root::types::I16>(Mode::Public, count_is!(0, 0, 0, 112));
            check_cast::<I16, console_root::types::I16>(Mode::Private, count_is!(0, 0, 0, 112));
        }

        #[test]
        fn test_i128_to_i32() {
            check_cast::<I32, console_root::types::I32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32, console_root::types::I32>(Mode::Public, count_is!(0, 0, 0, 96));
            check_cast::<I32, console_root::types::I32>(Mode::Private, count_is!(0, 0, 0, 96));
        }

        #[test]
        fn test_i128_to_i64() {
            check_cast::<I64, console_root::types::I64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Public, count_is!(0, 0, 0, 64));
            check_cast::<I64, console_root::types::I64>(Mode::Private, count_is!(0, 0, 0, 64));
        }

        #[test]
        fn test_i128_to_i128() {
            check_cast::<I128, console_root::types::I128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i128_to_scalar() {
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_i128_to_u8() {
            check_cast::<U8, console_root::types::U8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8, console_root::types::U8>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U8, console_root::types::U8>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i128_to_u16() {
            check_cast::<U16, console_root::types::U16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16, console_root::types::U16>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U16, console_root::types::U16>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i128_to_u32() {
            check_cast::<U32, console_root::types::U32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32, console_root::types::U32>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U32, console_root::types::U32>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i128_to_u64() {
            check_cast::<U64, console_root::types::U64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64, console_root::types::U64>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U64, console_root::types::U64>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_i128_to_u128() {
            check_cast::<U128, console_root::types::U128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128, console_root::types::U128>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U128, console_root::types::U128>(Mode::Private, count_is!(0, 0, 0, 1));
        }
    }

    mod u8 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console_root::types::U8, U8) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, U8, console_root::types::U8);

        #[test]
        fn test_u8_to_address() {
            check_cast::<Address, console_root::types::Address>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Address, console_root::types::Address>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Address, console_root::types::Address>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_u8_to_boolean() {
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Constant, count_is!(16, 0, 0, 0));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Public, count_is!(16, 0, 5, 6));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Private, count_is!(16, 0, 5, 6));
        }

        #[test]
        fn test_u8_to_field() {
            check_cast::<Field, console_root::types::Field>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_group() {
            check_cast::<Group, console_root::types::Group>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Group, console_root::types::Group>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Group, console_root::types::Group>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_u8_to_i8() {
            check_cast::<I8, console_root::types::I8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8, console_root::types::I8>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<I8, console_root::types::I8>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u8_to_i16() {
            check_cast::<I16, console_root::types::I16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16, console_root::types::I16>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I16, console_root::types::I16>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_i32() {
            check_cast::<I32, console_root::types::I32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32, console_root::types::I32>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I32, console_root::types::I32>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_i64() {
            check_cast::<I64, console_root::types::I64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_i128() {
            check_cast::<I128, console_root::types::I128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_scalar() {
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_u8() {
            check_cast::<U8, console_root::types::U8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8, console_root::types::U8>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U8, console_root::types::U8>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_u16() {
            check_cast::<U16, console_root::types::U16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16, console_root::types::U16>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U16, console_root::types::U16>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_u32() {
            check_cast::<U32, console_root::types::U32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32, console_root::types::U32>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U32, console_root::types::U32>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_u64() {
            check_cast::<U64, console_root::types::U64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64, console_root::types::U64>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U64, console_root::types::U64>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u8_to_u128() {
            check_cast::<U128, console_root::types::U128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128, console_root::types::U128>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U128, console_root::types::U128>(Mode::Private, count_is!(0, 0, 0, 0));
        }
    }

    mod u16 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console_root::types::U16, U16) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, U16, console_root::types::U16);

        #[test]
        fn test_u16_to_address() {
            check_cast::<Address, console_root::types::Address>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Address, console_root::types::Address>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Address, console_root::types::Address>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_u16_to_boolean() {
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Constant, count_is!(32, 0, 0, 0));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Public, count_is!(32, 0, 5, 6));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Private, count_is!(32, 0, 5, 6));
        }

        #[test]
        fn test_u16_to_field() {
            check_cast::<Field, console_root::types::Field>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_group() {
            check_cast::<Group, console_root::types::Group>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Group, console_root::types::Group>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Group, console_root::types::Group>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_u16_to_i8() {
            check_cast::<I8, console_root::types::I8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8, console_root::types::I8>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<I8, console_root::types::I8>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u16_to_i16() {
            check_cast::<I16, console_root::types::I16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16, console_root::types::I16>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<I16, console_root::types::I16>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u16_to_i32() {
            check_cast::<I32, console_root::types::I32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32, console_root::types::I32>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I32, console_root::types::I32>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_i64() {
            check_cast::<I64, console_root::types::I64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_i128() {
            check_cast::<I128, console_root::types::I128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_scalar() {
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_u8() {
            check_cast::<U8, console_root::types::U8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8, console_root::types::U8>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U8, console_root::types::U8>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u16_to_u16() {
            check_cast::<U16, console_root::types::U16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16, console_root::types::U16>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U16, console_root::types::U16>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_u32() {
            check_cast::<U32, console_root::types::U32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32, console_root::types::U32>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U32, console_root::types::U32>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_u64() {
            check_cast::<U64, console_root::types::U64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64, console_root::types::U64>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U64, console_root::types::U64>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u16_to_u128() {
            check_cast::<U128, console_root::types::U128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128, console_root::types::U128>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U128, console_root::types::U128>(Mode::Private, count_is!(0, 0, 0, 0));
        }
    }

    mod u32 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console_root::types::U32, U32) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, U32, console_root::types::U32);

        #[test]
        fn test_u32_to_address() {
            check_cast::<Address, console_root::types::Address>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Address, console_root::types::Address>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Address, console_root::types::Address>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_u32_to_boolean() {
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Constant, count_is!(64, 0, 0, 0));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Public, count_is!(64, 0, 5, 6));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Private, count_is!(64, 0, 5, 6));
        }

        #[test]
        fn test_u32_to_field() {
            check_cast::<Field, console_root::types::Field>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u32_to_group() {
            check_cast::<Group, console_root::types::Group>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Group, console_root::types::Group>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Group, console_root::types::Group>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_u32_to_i8() {
            check_cast::<I8, console_root::types::I8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8, console_root::types::I8>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<I8, console_root::types::I8>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u32_to_i16() {
            check_cast::<I16, console_root::types::I16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16, console_root::types::I16>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<I16, console_root::types::I16>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u32_to_i32() {
            check_cast::<I32, console_root::types::I32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32, console_root::types::I32>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<I32, console_root::types::I32>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u32_to_i64() {
            check_cast::<I64, console_root::types::I64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u32_to_i128() {
            check_cast::<I128, console_root::types::I128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u32_to_scalar() {
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u32_to_u8() {
            check_cast::<U8, console_root::types::U8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8, console_root::types::U8>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U8, console_root::types::U8>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u32_to_u16() {
            check_cast::<U16, console_root::types::U16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16, console_root::types::U16>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U16, console_root::types::U16>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u32_to_u32() {
            check_cast::<U32, console_root::types::U32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32, console_root::types::U32>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U32, console_root::types::U32>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u32_to_u64() {
            check_cast::<U64, console_root::types::U64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64, console_root::types::U64>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U64, console_root::types::U64>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u32_to_u128() {
            check_cast::<U128, console_root::types::U128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128, console_root::types::U128>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U128, console_root::types::U128>(Mode::Private, count_is!(0, 0, 0, 0));
        }
    }

    mod u64 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console_root::types::U64, U64) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, U64, console_root::types::U64);

        #[test]
        fn test_u64_to_address() {
            check_cast::<Address, console_root::types::Address>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Address, console_root::types::Address>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Address, console_root::types::Address>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_u64_to_boolean() {
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Constant, count_is!(128, 0, 0, 0));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Public, count_is!(128, 0, 5, 6));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Private, count_is!(128, 0, 5, 6));
        }

        #[test]
        fn test_u64_to_field() {
            check_cast::<Field, console_root::types::Field>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u64_to_group() {
            check_cast::<Group, console_root::types::Group>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Group, console_root::types::Group>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Group, console_root::types::Group>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_u64_to_i8() {
            check_cast::<I8, console_root::types::I8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8, console_root::types::I8>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<I8, console_root::types::I8>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u64_to_i16() {
            check_cast::<I16, console_root::types::I16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16, console_root::types::I16>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<I16, console_root::types::I16>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u64_to_i32() {
            check_cast::<I32, console_root::types::I32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32, console_root::types::I32>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<I32, console_root::types::I32>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u64_to_i64() {
            check_cast::<I64, console_root::types::I64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<I64, console_root::types::I64>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u64_to_i128() {
            check_cast::<I128, console_root::types::I128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u64_to_scalar() {
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u64_to_u8() {
            check_cast::<U8, console_root::types::U8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8, console_root::types::U8>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U8, console_root::types::U8>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u64_to_u16() {
            check_cast::<U16, console_root::types::U16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16, console_root::types::U16>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U16, console_root::types::U16>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u64_to_u32() {
            check_cast::<U32, console_root::types::U32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32, console_root::types::U32>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U32, console_root::types::U32>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u64_to_u64() {
            check_cast::<U64, console_root::types::U64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64, console_root::types::U64>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U64, console_root::types::U64>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u64_to_u128() {
            check_cast::<U128, console_root::types::U128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128, console_root::types::U128>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U128, console_root::types::U128>(Mode::Private, count_is!(0, 0, 0, 0));
        }
    }

    mod u128 {
        use super::*;

        fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console_root::types::U128, U128) {
            super::sample_values(i, mode, rng)
        }

        impl_check_cast!(cast, U128, console_root::types::U128);

        #[test]
        fn test_u128_to_address() {
            check_cast::<Address, console_root::types::Address>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Address, console_root::types::Address>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Address, console_root::types::Address>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_u128_to_boolean() {
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Constant, count_is!(256, 0, 0, 0));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Public, count_is!(256, 0, 5, 6));
            check_cast::<Boolean, console_root::types::Boolean>(Mode::Private, count_is!(256, 0, 5, 6));
        }

        #[test]
        fn test_u128_to_field() {
            check_cast::<Field, console_root::types::Field>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Field, console_root::types::Field>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u128_to_group() {
            check_cast::<Group, console_root::types::Group>(Mode::Constant, count_less_than!(11, 0, 0, 0));
            check_cast::<Group, console_root::types::Group>(Mode::Public, count_is!(4, 0, 13, 13));
            check_cast::<Group, console_root::types::Group>(Mode::Private, count_is!(4, 0, 13, 13));
        }

        #[test]
        fn test_u128_to_i8() {
            check_cast::<I8, console_root::types::I8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I8, console_root::types::I8>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<I8, console_root::types::I8>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u128_to_i16() {
            check_cast::<I16, console_root::types::I16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I16, console_root::types::I16>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<I16, console_root::types::I16>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u128_to_i32() {
            check_cast::<I32, console_root::types::I32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I32, console_root::types::I32>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<I32, console_root::types::I32>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u128_to_i64() {
            check_cast::<I64, console_root::types::I64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I64, console_root::types::I64>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<I64, console_root::types::I64>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u128_to_i128() {
            check_cast::<I128, console_root::types::I128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<I128, console_root::types::I128>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<I128, console_root::types::I128>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u128_to_scalar() {
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<Scalar, console_root::types::Scalar>(Mode::Private, count_is!(0, 0, 0, 0));
        }

        #[test]
        fn test_u128_to_u8() {
            check_cast::<U8, console_root::types::U8>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U8, console_root::types::U8>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U8, console_root::types::U8>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u128_to_u16() {
            check_cast::<U16, console_root::types::U16>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U16, console_root::types::U16>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U16, console_root::types::U16>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u128_to_u32() {
            check_cast::<U32, console_root::types::U32>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U32, console_root::types::U32>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U32, console_root::types::U32>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u128_to_u64() {
            check_cast::<U64, console_root::types::U64>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U64, console_root::types::U64>(Mode::Public, count_is!(0, 0, 0, 1));
            check_cast::<U64, console_root::types::U64>(Mode::Private, count_is!(0, 0, 0, 1));
        }

        #[test]
        fn test_u128_to_u128() {
            check_cast::<U128, console_root::types::U128>(Mode::Constant, count_is!(0, 0, 0, 0));
            check_cast::<U128, console_root::types::U128>(Mode::Public, count_is!(0, 0, 0, 0));
            check_cast::<U128, console_root::types::U128>(Mode::Private, count_is!(0, 0, 0, 0));
        }
    }
}
