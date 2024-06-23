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

impl Cast<Address> for Boolean {
    /// Casts a `Boolean` to an `Address`.
    #[inline]
    fn cast(&self) -> Address {
        self.cast_lossy()
    }
}

impl Cast<Boolean> for Boolean {
    /// Casts a `Boolean` to a `Boolean`.
    #[inline]
    fn cast(&self) -> Boolean {
        self.cast_lossy()
    }
}

impl Cast<Field> for Boolean {
    /// Casts a `Boolean` to a `Field`.
    #[inline]
    fn cast(&self) -> Field {
        self.cast_lossy()
    }
}

impl Cast<Group> for Boolean {
    /// Casts a `Boolean` to a `Group`.
    #[inline]
    fn cast(&self) -> Group {
        self.cast_lossy()
    }
}

impl<I: IntegerType> Cast<Integer<I>> for Boolean {
    /// Casts a `Boolean` to an `Integer`.
    #[inline]
    fn cast(&self) -> Integer<I> {
        self.cast_lossy()
    }
}

impl Cast<Scalar> for Boolean {
    /// Casts a `Boolean` to a `Scalar`.
    #[inline]
    fn cast(&self) -> Scalar {
        self.cast_lossy()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::Cast as _;
    use console_root::prelude::TestRng;
    use snarkvm_circuit_types::environment::{count_is, Circuit, Eject, Inject, Mode, UpdatableCount};

    use std::fmt::Debug;

    const ITERATIONS: usize = 2;

    fn sample_values(i: usize, mode: Mode, _: &mut TestRng) -> (console_root::types::Boolean, Boolean) {
        (console_root::types::Boolean::new(i % 2 == 0), Boolean::new(mode, i % 2 == 0))
    }

    impl_check_cast!(cast, Boolean, console_root::types::Boolean);

    #[test]
    fn test_boolean_to_address() {
        check_cast::<Address, console_root::types::Address>(Mode::Constant, count_is!(10, 0, 0, 0));
        check_cast::<Address, console_root::types::Address>(Mode::Public, count_is!(10, 0, 0, 0));
        check_cast::<Address, console_root::types::Address>(Mode::Private, count_is!(10, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_boolean() {
        check_cast::<Boolean, console_root::types::Boolean>(Mode::Constant, count_is!(0, 0, 0, 0));
        check_cast::<Boolean, console_root::types::Boolean>(Mode::Public, count_is!(0, 0, 0, 0));
        check_cast::<Boolean, console_root::types::Boolean>(Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_field() {
        check_cast::<Field, console_root::types::Field>(Mode::Constant, count_is!(0, 0, 0, 0));
        check_cast::<Field, console_root::types::Field>(Mode::Public, count_is!(0, 0, 0, 0));
        check_cast::<Field, console_root::types::Field>(Mode::Private, count_is!(0, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_group() {
        check_cast::<Group, console_root::types::Group>(Mode::Constant, count_is!(10, 0, 0, 0));
        check_cast::<Group, console_root::types::Group>(Mode::Public, count_is!(10, 0, 0, 0));
        check_cast::<Group, console_root::types::Group>(Mode::Private, count_is!(10, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_i8() {
        check_cast::<I8, console_root::types::I8>(Mode::Constant, count_is!(16, 0, 0, 0));
        check_cast::<I8, console_root::types::I8>(Mode::Public, count_is!(16, 0, 0, 0));
        check_cast::<I8, console_root::types::I8>(Mode::Private, count_is!(16, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_i16() {
        check_cast::<I16, console_root::types::I16>(Mode::Constant, count_is!(32, 0, 0, 0));
        check_cast::<I16, console_root::types::I16>(Mode::Public, count_is!(32, 0, 0, 0));
        check_cast::<I16, console_root::types::I16>(Mode::Private, count_is!(32, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_i32() {
        check_cast::<I32, console_root::types::I32>(Mode::Constant, count_is!(64, 0, 0, 0));
        check_cast::<I32, console_root::types::I32>(Mode::Public, count_is!(64, 0, 0, 0));
        check_cast::<I32, console_root::types::I32>(Mode::Private, count_is!(64, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_i64() {
        check_cast::<I64, console_root::types::I64>(Mode::Constant, count_is!(128, 0, 0, 0));
        check_cast::<I64, console_root::types::I64>(Mode::Public, count_is!(128, 0, 0, 0));
        check_cast::<I64, console_root::types::I64>(Mode::Private, count_is!(128, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_i128() {
        check_cast::<I128, console_root::types::I128>(Mode::Constant, count_is!(256, 0, 0, 0));
        check_cast::<I128, console_root::types::I128>(Mode::Public, count_is!(256, 0, 0, 0));
        check_cast::<I128, console_root::types::I128>(Mode::Private, count_is!(256, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_scalar() {
        check_cast::<Scalar, console_root::types::Scalar>(Mode::Constant, count_is!(2, 0, 0, 0));
        check_cast::<Scalar, console_root::types::Scalar>(Mode::Public, count_is!(2, 0, 0, 0));
        check_cast::<Scalar, console_root::types::Scalar>(Mode::Private, count_is!(2, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_u8() {
        check_cast::<U8, console_root::types::U8>(Mode::Constant, count_is!(16, 0, 0, 0));
        check_cast::<U8, console_root::types::U8>(Mode::Public, count_is!(16, 0, 0, 0));
        check_cast::<U8, console_root::types::U8>(Mode::Private, count_is!(16, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_u16() {
        check_cast::<U16, console_root::types::U16>(Mode::Constant, count_is!(32, 0, 0, 0));
        check_cast::<U16, console_root::types::U16>(Mode::Public, count_is!(32, 0, 0, 0));
        check_cast::<U16, console_root::types::U16>(Mode::Private, count_is!(32, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_u32() {
        check_cast::<U32, console_root::types::U32>(Mode::Constant, count_is!(64, 0, 0, 0));
        check_cast::<U32, console_root::types::U32>(Mode::Public, count_is!(64, 0, 0, 0));
        check_cast::<U32, console_root::types::U32>(Mode::Private, count_is!(64, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_u64() {
        check_cast::<U64, console_root::types::U64>(Mode::Constant, count_is!(128, 0, 0, 0));
        check_cast::<U64, console_root::types::U64>(Mode::Public, count_is!(128, 0, 0, 0));
        check_cast::<U64, console_root::types::U64>(Mode::Private, count_is!(128, 0, 0, 0));
    }

    #[test]
    fn test_boolean_to_u128() {
        check_cast::<U128, console_root::types::U128>(Mode::Constant, count_is!(256, 0, 0, 0));
        check_cast::<U128, console_root::types::U128>(Mode::Public, count_is!(256, 0, 0, 0));
        check_cast::<U128, console_root::types::U128>(Mode::Private, count_is!(256, 0, 0, 0));
    }
}
