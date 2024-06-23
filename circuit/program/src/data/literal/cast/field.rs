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

impl Cast<Address> for Field {
    /// Casts a `Field` to an `Address`.
    ///
    /// This operation attempts to recover the group element from the field element, and then
    /// constructs an address from the group element.
    ///
    /// To cast arbitrary field elements to addresses, use `Field::cast_lossy`.
    #[inline]
    fn cast(&self) -> Address {
        Address::from_field(self.clone())
    }
}

impl Cast<Boolean> for Field {
    /// Casts a `Field` to a `Boolean`, if the field is zero or one.
    ///
    /// To cast arbitrary field elements to booleans, use `Field::cast_lossy`.
    #[inline]
    fn cast(&self) -> Boolean {
        let is_one = self.is_one();
        Circuit::assert(self.is_zero().bitor(&is_one));
        is_one
    }
}

impl Cast<Field> for Field {
    /// Casts a `Field` to a `Field`.
    #[inline]
    fn cast(&self) -> Field {
        self.clone()
    }
}

impl Cast<Group> for Field {
    /// Casts a `Field` to a `Group`.
    ///
    /// This operation attempts to recover the group element from the field element,
    /// and returns an error if the field element is not a valid x-coordinate.
    ///
    /// To cast arbitrary field elements to groups, use `Field::cast_lossy`.
    #[inline]
    fn cast(&self) -> Group {
        Group::from_x_coordinate(self.clone())
    }
}

impl<I: IntegerType> Cast<Integer<I>> for Field {
    /// Casts a `Field` to an `Integer`, if the field element is in the integer's range.
    ///
    /// To cast arbitrary field elements to integers, use `Field::cast_lossy`.
    #[inline]
    fn cast(&self) -> Integer<I> {
        Integer::from_field(self.clone())
    }
}

impl Cast<Scalar> for Field {
    /// Casts a `Field` to a `Scalar`, if the field element is in the scalar's range.
    ///
    /// To cast arbitrary field elements to scalars, use `Field::cast_lossy`.
    #[inline]
    fn cast(&self) -> Scalar {
        Scalar::from_field(self.clone())
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

    const ITERATIONS: usize = 100;

    fn sample_values(i: usize, mode: Mode, rng: &mut TestRng) -> (console_root::types::Field, Field) {
        let console_value = match i {
            0 => console_root::types::Field::zero(),
            1 => console_root::types::Field::one(),
            _ => Uniform::rand(rng),
        };
        let circuit_value = Field::new(mode, console_value);
        (console_value, circuit_value)
    }

    impl_check_cast!(cast, Field, console_root::types::Field);

    #[test]
    fn test_field_to_address() {
        check_cast::<Address, console_root::types::Address>(Mode::Constant, count_less_than!(11, 0, 0, 0));
        check_cast::<Address, console_root::types::Address>(Mode::Public, count_is!(4, 0, 13, 13));
        check_cast::<Address, console_root::types::Address>(Mode::Private, count_is!(4, 0, 13, 13));
    }

    #[test]
    fn test_field_to_boolean() {
        check_cast::<Boolean, console_root::types::Boolean>(Mode::Constant, count_is!(2, 0, 0, 0));
        check_cast::<Boolean, console_root::types::Boolean>(Mode::Public, count_is!(0, 0, 5, 6));
        check_cast::<Boolean, console_root::types::Boolean>(Mode::Private, count_is!(0, 0, 5, 6));
    }

    #[test]
    fn test_field_to_field() {
        check_cast::<Field, console_root::types::Field>(Mode::Constant, count_is!(0, 0, 0, 0));
        check_cast::<Field, console_root::types::Field>(Mode::Public, count_is!(0, 0, 0, 0));
        check_cast::<Field, console_root::types::Field>(Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_field_to_group() {
        check_cast::<Group, console_root::types::Group>(Mode::Constant, count_less_than!(11, 0, 0, 0));
        check_cast::<Group, console_root::types::Group>(Mode::Public, count_is!(4, 0, 13, 13));
        check_cast::<Group, console_root::types::Group>(Mode::Private, count_is!(4, 0, 13, 13));
    }

    #[test]
    fn test_field_to_i8() {
        check_cast::<I8, console_root::types::I8>(Mode::Constant, count_is!(8, 0, 0, 0));
        check_cast::<I8, console_root::types::I8>(Mode::Public, count_is!(0, 0, 8, 9));
        check_cast::<I8, console_root::types::I8>(Mode::Private, count_is!(0, 0, 8, 9));
    }

    #[test]
    fn test_field_to_i16() {
        check_cast::<I16, console_root::types::I16>(Mode::Constant, count_is!(16, 0, 0, 0));
        check_cast::<I16, console_root::types::I16>(Mode::Public, count_is!(0, 0, 16, 17));
        check_cast::<I16, console_root::types::I16>(Mode::Private, count_is!(0, 0, 16, 17));
    }

    #[test]
    fn test_field_to_i32() {
        check_cast::<I32, console_root::types::I32>(Mode::Constant, count_is!(32, 0, 0, 0));
        check_cast::<I32, console_root::types::I32>(Mode::Public, count_is!(0, 0, 32, 33));
        check_cast::<I32, console_root::types::I32>(Mode::Private, count_is!(0, 0, 32, 33));
    }

    #[test]
    fn test_field_to_i64() {
        check_cast::<I64, console_root::types::I64>(Mode::Constant, count_is!(64, 0, 0, 0));
        check_cast::<I64, console_root::types::I64>(Mode::Public, count_is!(0, 0, 64, 65));
        check_cast::<I64, console_root::types::I64>(Mode::Private, count_is!(0, 0, 64, 65));
    }

    #[test]
    fn test_field_to_i128() {
        check_cast::<I128, console_root::types::I128>(Mode::Constant, count_is!(128, 0, 0, 0));
        check_cast::<I128, console_root::types::I128>(Mode::Public, count_is!(0, 0, 128, 129));
        check_cast::<I128, console_root::types::I128>(Mode::Private, count_is!(0, 0, 128, 129));
    }

    #[test]
    fn test_field_to_scalar() {
        check_cast::<Scalar, console_root::types::Scalar>(Mode::Constant, count_is!(253, 0, 0, 0));
        check_cast::<Scalar, console_root::types::Scalar>(Mode::Public, count_is!(0, 0, 755, 759));
        check_cast::<Scalar, console_root::types::Scalar>(Mode::Private, count_is!(0, 0, 755, 759));
    }

    #[test]
    fn test_field_to_u8() {
        check_cast::<U8, console_root::types::U8>(Mode::Constant, count_is!(8, 0, 0, 0));
        check_cast::<U8, console_root::types::U8>(Mode::Public, count_is!(0, 0, 8, 9));
        check_cast::<U8, console_root::types::U8>(Mode::Private, count_is!(0, 0, 8, 9));
    }

    #[test]
    fn test_field_to_u16() {
        check_cast::<U16, console_root::types::U16>(Mode::Constant, count_is!(16, 0, 0, 0));
        check_cast::<U16, console_root::types::U16>(Mode::Public, count_is!(0, 0, 16, 17));
        check_cast::<U16, console_root::types::U16>(Mode::Private, count_is!(0, 0, 16, 17));
    }

    #[test]
    fn test_field_to_u32() {
        check_cast::<U32, console_root::types::U32>(Mode::Constant, count_is!(32, 0, 0, 0));
        check_cast::<U32, console_root::types::U32>(Mode::Public, count_is!(0, 0, 32, 33));
        check_cast::<U32, console_root::types::U32>(Mode::Private, count_is!(0, 0, 32, 33));
    }

    #[test]
    fn test_field_to_u64() {
        check_cast::<U64, console_root::types::U64>(Mode::Constant, count_is!(64, 0, 0, 0));
        check_cast::<U64, console_root::types::U64>(Mode::Public, count_is!(0, 0, 64, 65));
        check_cast::<U64, console_root::types::U64>(Mode::Private, count_is!(0, 0, 64, 65));
    }

    #[test]
    fn test_field_to_u128() {
        check_cast::<U128, console_root::types::U128>(Mode::Constant, count_is!(128, 0, 0, 0));
        check_cast::<U128, console_root::types::U128>(Mode::Public, count_is!(0, 0, 128, 129));
        check_cast::<U128, console_root::types::U128>(Mode::Private, count_is!(0, 0, 128, 129));
    }
}
