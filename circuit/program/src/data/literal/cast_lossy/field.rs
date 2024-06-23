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
        Address::from_group(group)
    }
}

impl CastLossy<Boolean> for Field {
    /// Casts a `Field` to a `Boolean`, with lossy truncation.
    /// This operation returns the least significant bit of the field.
    #[inline]
    fn cast_lossy(&self) -> Boolean {
        let bits_le = self.to_bits_le();
        debug_assert!(!bits_le.is_empty(), "An integer must have at least one bit");
        bits_le[0].clone()
    }
}

impl CastLossy<Field> for Field {
    /// Casts a `Field` to a `Field`.
    /// This is an identity cast, so it is **always** lossless.
    #[inline]
    fn cast_lossy(&self) -> Field {
        self.clone()
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
        // This method requires that an `x-coordinate` of 1 is an invalid group element.
        // This is used by the ternary below, which uses 'is_x_one' to determine whether to return the generator.
        debug_assert!(console::Group::from_x_coordinate(<console::Field as console::One>::one()).is_err());

        // Attempt to find a group element with self as the x-coordinate.
        let (point_with_x, x_is_not_in_group) = Group::from_x_coordinate_flagged(self.clone());

        // Determine if the field element is zero.
        let is_x_zero = self.is_zero();
        // Determine if the field element is one.
        let is_x_one = self.is_one();

        // Initialize the group generator.
        let generator = Group::generator();

        // Determine the input to Elligator-2, based on the x-coordinate.
        // If self is 0, we pass 1 to Elligator-2 instead.
        // Note that, in this case, we won't use the result of Elligator-2,
        // because the point (0, 1) is in the subgroup, and that is what we return.
        let elligator_input = Field::ternary(&is_x_zero, &Field::one(), self);
        // Perform Elligator-2 on the field element, to recover a group element.
        let elligator_point = Elligator2::encode(&elligator_input);

        // Select either the generator or the result of Elligator-2, depending on whether x is 1 or not.
        // This is only used when x is not in the group, see below.
        let generator_or_elligator_point = Group::ternary(&is_x_one, &generator, &elligator_point);

        // Select either the group point with x or the generator or the result of Elligator-2,
        // depending on whether x is in the group or not, and, if it is not, based on whether it is 1 or not.
        Group::ternary(&x_is_not_in_group, &generator_or_elligator_point, &point_with_x)
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
    use console::CastLossy as _;
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

    check_cast_lossy!(cast_lossy, Field, console_root::types::Field);

    #[test]
    fn test_field_to_address() {
        check_cast_lossy::<Address, console_root::types::Address>(Mode::Constant, count_less_than!(4303, 0, 0, 0));
        check_cast_lossy::<Address, console_root::types::Address>(Mode::Public, count_is!(2029, 0, 6745, 6750));
        check_cast_lossy::<Address, console_root::types::Address>(Mode::Private, count_is!(2029, 0, 6745, 6750));
    }

    #[test]
    fn test_field_to_boolean() {
        check_cast_lossy::<Boolean, console_root::types::Boolean>(Mode::Constant, count_is!(253, 0, 0, 0));
        check_cast_lossy::<Boolean, console_root::types::Boolean>(Mode::Public, count_is!(0, 0, 505, 507));
        check_cast_lossy::<Boolean, console_root::types::Boolean>(Mode::Private, count_is!(0, 0, 505, 507));
    }

    #[test]
    fn test_field_to_field() {
        check_cast_lossy::<Field, console_root::types::Field>(Mode::Constant, count_is!(0, 0, 0, 0));
        check_cast_lossy::<Field, console_root::types::Field>(Mode::Public, count_is!(0, 0, 0, 0));
        check_cast_lossy::<Field, console_root::types::Field>(Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_field_to_group() {
        check_cast_lossy::<Group, console_root::types::Group>(Mode::Constant, count_less_than!(4303, 0, 0, 0));
        check_cast_lossy::<Group, console_root::types::Group>(Mode::Public, count_is!(2029, 0, 6745, 6750));
        check_cast_lossy::<Group, console_root::types::Group>(Mode::Private, count_is!(2029, 0, 6745, 6750));
    }

    #[test]
    fn test_field_to_i8() {
        check_cast_lossy::<I8, console_root::types::I8>(Mode::Constant, count_is!(253, 0, 0, 0));
        check_cast_lossy::<I8, console_root::types::I8>(Mode::Public, count_is!(0, 0, 505, 507));
        check_cast_lossy::<I8, console_root::types::I8>(Mode::Private, count_is!(0, 0, 505, 507));
    }

    #[test]
    fn test_field_to_i16() {
        check_cast_lossy::<I16, console_root::types::I16>(Mode::Constant, count_is!(253, 0, 0, 0));
        check_cast_lossy::<I16, console_root::types::I16>(Mode::Public, count_is!(0, 0, 505, 507));
        check_cast_lossy::<I16, console_root::types::I16>(Mode::Private, count_is!(0, 0, 505, 507));
    }

    #[test]
    fn test_field_to_i32() {
        check_cast_lossy::<I32, console_root::types::I32>(Mode::Constant, count_is!(253, 0, 0, 0));
        check_cast_lossy::<I32, console_root::types::I32>(Mode::Public, count_is!(0, 0, 505, 507));
        check_cast_lossy::<I32, console_root::types::I32>(Mode::Private, count_is!(0, 0, 505, 507));
    }

    #[test]
    fn test_field_to_i64() {
        check_cast_lossy::<I64, console_root::types::I64>(Mode::Constant, count_is!(253, 0, 0, 0));
        check_cast_lossy::<I64, console_root::types::I64>(Mode::Public, count_is!(0, 0, 505, 507));
        check_cast_lossy::<I64, console_root::types::I64>(Mode::Private, count_is!(0, 0, 505, 507));
    }

    #[test]
    fn test_field_to_i128() {
        check_cast_lossy::<I128, console_root::types::I128>(Mode::Constant, count_is!(253, 0, 0, 0));
        check_cast_lossy::<I128, console_root::types::I128>(Mode::Public, count_is!(0, 0, 505, 507));
        check_cast_lossy::<I128, console_root::types::I128>(Mode::Private, count_is!(0, 0, 505, 507));
    }

    #[test]
    fn test_field_to_scalar() {
        check_cast_lossy::<Scalar, console_root::types::Scalar>(Mode::Constant, count_is!(253, 0, 0, 0));
        check_cast_lossy::<Scalar, console_root::types::Scalar>(Mode::Public, count_is!(0, 0, 505, 507));
        check_cast_lossy::<Scalar, console_root::types::Scalar>(Mode::Private, count_is!(0, 0, 505, 507));
    }

    #[test]
    fn test_field_to_u8() {
        check_cast_lossy::<U8, console_root::types::U8>(Mode::Constant, count_is!(253, 0, 0, 0));
        check_cast_lossy::<U8, console_root::types::U8>(Mode::Public, count_is!(0, 0, 505, 507));
        check_cast_lossy::<U8, console_root::types::U8>(Mode::Private, count_is!(0, 0, 505, 507));
    }

    #[test]
    fn test_field_to_u16() {
        check_cast_lossy::<U16, console_root::types::U16>(Mode::Constant, count_is!(253, 0, 0, 0));
        check_cast_lossy::<U16, console_root::types::U16>(Mode::Public, count_is!(0, 0, 505, 507));
        check_cast_lossy::<U16, console_root::types::U16>(Mode::Private, count_is!(0, 0, 505, 507));
    }

    #[test]
    fn test_field_to_u32() {
        check_cast_lossy::<U32, console_root::types::U32>(Mode::Constant, count_is!(253, 0, 0, 0));
        check_cast_lossy::<U32, console_root::types::U32>(Mode::Public, count_is!(0, 0, 505, 507));
        check_cast_lossy::<U32, console_root::types::U32>(Mode::Private, count_is!(0, 0, 505, 507));
    }

    #[test]
    fn test_field_to_u64() {
        check_cast_lossy::<U64, console_root::types::U64>(Mode::Constant, count_is!(253, 0, 0, 0));
        check_cast_lossy::<U64, console_root::types::U64>(Mode::Public, count_is!(0, 0, 505, 507));
        check_cast_lossy::<U64, console_root::types::U64>(Mode::Private, count_is!(0, 0, 505, 507));
    }

    #[test]
    fn test_field_to_u128() {
        check_cast_lossy::<U128, console_root::types::U128>(Mode::Constant, count_is!(253, 0, 0, 0));
        check_cast_lossy::<U128, console_root::types::U128>(Mode::Public, count_is!(0, 0, 505, 507));
        check_cast_lossy::<U128, console_root::types::U128>(Mode::Private, count_is!(0, 0, 505, 507));
    }
}
