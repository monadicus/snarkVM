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

impl<I: IntegerType> Neg for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `negation` of `self`.
    #[inline]
    fn neg(self) -> Self::Output {
        match I::is_signed() {
            true => match self.integer.checked_neg() {
                Some(integer) => Integer::new(integer),
                None => Console::halt(format!("Integer negation failed on: {}", self.integer)),
            },
            false => Console::halt("Negation of unsigned integers is not supported."),
        }
    }
}

impl<I: IntegerType> AbsChecked for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `absolute value` of `self`.
    #[inline]
    fn abs_checked(self) -> Self::Output {
        match I::is_signed() {
            true => match self.integer.checked_abs() {
                Some(integer) => Integer::new(integer),
                None => Console::halt(format!("Integer absolute value failed on: {}", self.integer)),
            },
            false => self,
        }
    }
}

impl<I: IntegerType> AbsWrapped for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `absolute value` of `self`.
    #[inline]
    fn abs_wrapped(self) -> Self::Output {
        match I::is_signed() {
            true => Integer::new(self.integer.wrapping_abs()),
            false => self,
        }
    }
}

impl<I: IntegerType> Add<Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: Integer<I>) -> Self::Output {
        match self.integer.checked_add(&other.integer) {
            Some(integer) => Integer::new(integer),
            None => Console::halt(format!("Integer addition failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> Add<&Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: &Integer<I>) -> Self::Output {
        match self.integer.checked_add(&other.integer) {
            Some(integer) => Integer::new(integer),
            None => Console::halt(format!("Integer addition failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> AddWrapped<Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add_wrapped(&self, other: &Integer<I>) -> Self::Output {
        Integer::new(self.integer.wrapping_add(&other.integer))
    }
}

impl<I: IntegerType> AddAssign<Integer<I>> for Integer<I> {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: Integer<I>) {
        match self.integer.checked_add(&other.integer) {
            Some(integer) => self.integer = integer,
            None => Console::halt(format!("Integer addition failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> AddAssign<&Integer<I>> for Integer<I> {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: &Integer<I>) {
        match self.integer.checked_add(&other.integer) {
            Some(integer) => self.integer = integer,
            None => Console::halt(format!("Integer addition failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> Sub<Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: Integer<I>) -> Self::Output {
        match self.integer.checked_sub(&other.integer) {
            Some(integer) => Integer::new(integer),
            None => Console::halt(format!("Integer subtraction failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> Sub<&Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: &Integer<I>) -> Self::Output {
        match self.integer.checked_sub(&other.integer) {
            Some(integer) => Integer::new(integer),
            None => Console::halt(format!("Integer subtraction failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> SubWrapped<Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub_wrapped(&self, other: &Integer<I>) -> Self::Output {
        Integer::new(self.integer.wrapping_sub(&other.integer))
    }
}

impl<I: IntegerType> SubAssign<Integer<I>> for Integer<I> {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: Integer<I>) {
        match self.integer.checked_sub(&other.integer) {
            Some(integer) => self.integer = integer,
            None => Console::halt(format!("Integer subtraction failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> SubAssign<&Integer<I>> for Integer<I> {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: &Integer<I>) {
        match self.integer.checked_sub(&other.integer) {
            Some(integer) => self.integer = integer,
            None => Console::halt(format!("Integer subtraction failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> Mul<Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: Integer<I>) -> Self::Output {
        match self.integer.checked_mul(&other.integer) {
            Some(integer) => Integer::new(integer),
            None => Console::halt(format!("Integer multiplication failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> Mul<&Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: &Integer<I>) -> Self::Output {
        match self.integer.checked_mul(&other.integer) {
            Some(integer) => Integer::new(integer),
            None => Console::halt(format!("Integer multiplication failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> MulWrapped<Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul_wrapped(&self, other: &Integer<I>) -> Self::Output {
        Integer::new(self.integer.wrapping_mul(&other.integer))
    }
}

impl<I: IntegerType> MulAssign<Integer<I>> for Integer<I> {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: Integer<I>) {
        match self.integer.checked_mul(&other.integer) {
            Some(integer) => self.integer = integer,
            None => Console::halt(format!("Integer multiplication failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> MulAssign<&Integer<I>> for Integer<I> {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: &Integer<I>) {
        match self.integer.checked_mul(&other.integer) {
            Some(integer) => self.integer = integer,
            None => Console::halt(format!("Integer multiplication failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> Div<Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `quotient` of `self` and `other`.
    #[inline]
    fn div(self, other: Integer<I>) -> Self::Output {
        match self.integer.checked_div(&other.integer) {
            Some(integer) => Integer::new(integer),
            None => Console::halt(format!("Integer division failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> Div<&Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `quotient` of `self` and `other`.
    #[inline]
    fn div(self, other: &Integer<I>) -> Self::Output {
        match self.integer.checked_div(&other.integer) {
            Some(integer) => Integer::new(integer),
            None => Console::halt(format!("Integer division failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> DivWrapped<Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `quotient` of `self` and `other`.
    #[inline]
    fn div_wrapped(&self, other: &Integer<I>) -> Self::Output {
        match other.is_zero() {
            true => Console::halt(format!("Integer division by zero: {self} / {other}")),
            false => Integer::new(self.integer.wrapping_div(&other.integer)),
        }
    }
}

impl<I: IntegerType> DivAssign<Integer<I>> for Integer<I> {
    /// Divides `self` by `other`.
    #[inline]
    fn div_assign(&mut self, other: Integer<I>) {
        match self.integer.checked_div(&other.integer) {
            Some(integer) => self.integer = integer,
            None => Console::halt(format!("Integer division failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> DivAssign<&Integer<I>> for Integer<I> {
    /// Divides `self` by `other`.
    #[inline]
    fn div_assign(&mut self, other: &Integer<I>) {
        match self.integer.checked_div(&other.integer) {
            Some(integer) => self.integer = integer,
            None => Console::halt(format!("Integer division failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> Modulo<Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the result of taking the modulus of `self` with respect to `other`.
    #[inline]
    fn modulo(&self, other: &Integer<I>) -> Self {
        match I::is_signed() {
            true => Console::halt("Taking the modulus of signed integers is not supported"),
            false => match other.is_zero() {
                true => Console::halt(format!("Integer modulus by zero: {self} % {other}")),
                false => Integer::new(self.integer.modulo(&other.integer)),
            },
        }
    }
}

impl<I: IntegerType> Rem<Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `remainder` of `self` divided by `other`.
    #[inline]
    fn rem(self, other: Integer<I>) -> Self {
        match self.integer.checked_rem(&other.integer) {
            Some(integer) => Integer::new(integer),
            None => Console::halt(format!("Integer remainder failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> Rem<&Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `remainder` of `self` divided by `other`.
    #[inline]
    fn rem(self, other: &Integer<I>) -> Self {
        match self.integer.checked_rem(&other.integer) {
            Some(integer) => Integer::new(integer),
            None => Console::halt(format!("Integer remainder failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> RemWrapped<Integer<I>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `remainder` of `self` divided by `other`.
    #[inline]
    fn rem_wrapped(&self, other: &Integer<I>) -> Self::Output {
        match other.is_zero() {
            true => Console::halt(format!("Integer remainder by zero: {self} % {other}")),
            false => Integer::new(self.integer.wrapping_rem(&other.integer)),
        }
    }
}

impl<I: IntegerType> RemAssign<Integer<I>> for Integer<I> {
    /// Returns the `remainder` of `self` divided by `other`.
    #[inline]
    fn rem_assign(&mut self, other: Integer<I>) {
        match self.integer.checked_rem(&other.integer) {
            Some(integer) => self.integer = integer,
            None => Console::halt(format!("Integer remainder failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType> RemAssign<&Integer<I>> for Integer<I> {
    /// Returns the `remainder` of `self` divided by `other`.
    #[inline]
    fn rem_assign(&mut self, other: &Integer<I>) {
        match self.integer.checked_rem(&other.integer) {
            Some(integer) => self.integer = integer,
            None => Console::halt(format!("Integer remainder failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType, M: Magnitude> Pow<Integer<M>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `power` of `self` to the power of `other`.
    #[inline]
    fn pow(self, other: Integer<M>) -> Self::Output {
        match self.integer.checked_pow(&other.integer.to_u32().unwrap()) {
            // Unwrap is safe as we only cast up.
            Some(integer) => Integer::new(integer),
            None => Console::halt(format!("Integer power failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType, M: Magnitude> Pow<&Integer<M>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `power` of `self` to the power of `other`.
    #[inline]
    fn pow(self, other: &Integer<M>) -> Self::Output {
        match self.integer.checked_pow(&other.integer.to_u32().unwrap()) {
            // Unwrap is safe as we only cast up.
            Some(integer) => Integer::new(integer),
            None => Console::halt(format!("Integer power failed on: {self} and {other}")),
        }
    }
}

impl<I: IntegerType, M: Magnitude> PowWrapped<Integer<M>> for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `power` of `self` to the power of `other`.
    #[inline]
    fn pow_wrapped(&self, other: &Integer<M>) -> Self::Output {
        Integer::new(self.integer.wrapping_pow(&other.integer.to_u32().unwrap()))
    }
}

impl<I: IntegerType> Square for Integer<I> {
    type Output = Integer<I>;

    /// Returns the `square` of `self`.
    #[inline]
    fn square(&self) -> Self::Output {
        match self.integer.checked_mul(&self.integer) {
            Some(integer) => Integer::new(integer),
            None => Console::halt(format!("Integer square failed on: {}", self.integer)),
        }
    }
}
