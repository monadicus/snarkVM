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

impl Neg for Scalar {
    type Output = Scalar;

    /// Returns the `negation` of `self`.
    #[inline]
    fn neg(self) -> Self::Output {
        Scalar::new(-self.scalar)
    }
}

impl Add<Scalar> for Scalar {
    type Output = Scalar;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: Scalar) -> Self::Output {
        Scalar::new(self.scalar + other.scalar)
    }
}

impl Add<&Scalar> for Scalar {
    type Output = Scalar;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: &Scalar) -> Self::Output {
        Scalar::new(self.scalar + other.scalar)
    }
}

impl AddAssign<Scalar> for Scalar {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: Scalar) {
        self.scalar += other.scalar;
    }
}

impl AddAssign<&Scalar> for Scalar {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: &Scalar) {
        self.scalar += other.scalar;
    }
}

impl Sub<Scalar> for Scalar {
    type Output = Scalar;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: Scalar) -> Self::Output {
        Scalar::new(self.scalar - other.scalar)
    }
}

impl Sub<&Scalar> for Scalar {
    type Output = Scalar;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: &Scalar) -> Self::Output {
        Scalar::new(self.scalar - other.scalar)
    }
}

impl SubAssign<Scalar> for Scalar {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: Scalar) {
        self.scalar -= other.scalar;
    }
}

impl SubAssign<&Scalar> for Scalar {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: &Scalar) {
        self.scalar -= other.scalar;
    }
}

impl Mul<Scalar> for Scalar {
    type Output = Scalar;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: Scalar) -> Self::Output {
        Scalar::new(self.scalar * other.scalar)
    }
}

impl Mul<&Scalar> for Scalar {
    type Output = Scalar;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: &Scalar) -> Self::Output {
        Scalar::new(self.scalar * other.scalar)
    }
}

impl MulAssign<Scalar> for Scalar {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: Scalar) {
        self.scalar *= other.scalar;
    }
}

impl MulAssign<&Scalar> for Scalar {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: &Scalar) {
        self.scalar *= other.scalar;
    }
}

impl Div<Scalar> for Scalar {
    type Output = Scalar;

    /// Returns the `quotient` of `self` and `other`.
    #[inline]
    fn div(self, other: Scalar) -> Self::Output {
        match other.is_zero() {
            true => Console::halt(format!("Scalar division by zero: {self} / {other}")),
            false => Scalar::new(self.scalar / other.scalar),
        }
    }
}

impl Div<&Scalar> for Scalar {
    type Output = Scalar;

    /// Returns the `quotient` of `self` and `other`.
    #[inline]
    fn div(self, other: &Scalar) -> Self::Output {
        match other.is_zero() {
            true => Console::halt(format!("Scalar division by zero: {self} / {other}")),
            false => Scalar::new(self.scalar / other.scalar),
        }
    }
}

impl DivAssign<Scalar> for Scalar {
    /// Divides `self` by `other`.
    #[inline]
    fn div_assign(&mut self, other: Scalar) {
        match other.is_zero() {
            true => Console::halt(format!("Scalar division by zero: {self} / {other}")),
            false => self.scalar /= other.scalar,
        }
    }
}

impl DivAssign<&Scalar> for Scalar {
    /// Divides `self` by `other`.
    #[inline]
    fn div_assign(&mut self, other: &Scalar) {
        match other.is_zero() {
            true => Console::halt(format!("Scalar division by zero: {self} / {other}")),
            false => self.scalar /= other.scalar,
        }
    }
}

impl Pow<Scalar> for Scalar {
    type Output = Scalar;

    /// Returns the `power` of `self` to the power of `other`.
    #[inline]
    fn pow(self, other: Scalar) -> Self::Output {
        Scalar::new(self.scalar.pow(other.scalar.to_bigint()))
    }
}

impl Pow<&Scalar> for Scalar {
    type Output = Scalar;

    /// Returns the `power` of `self` to the power of `other`.
    #[inline]
    fn pow(self, other: &Scalar) -> Self::Output {
        Scalar::new(self.scalar.pow(other.scalar.to_bigint()))
    }
}

impl Double for Scalar {
    type Output = Scalar;

    /// Returns the `double` of `self`.
    #[inline]
    fn double(&self) -> Self::Output {
        Scalar::new(self.scalar.double())
    }
}

impl Inverse for Scalar {
    type Output = Scalar;

    /// Returns the `inverse` of `self`.
    #[inline]
    fn inverse(&self) -> Result<Self::Output> {
        match self.scalar.inverse() {
            Some(inverse) => Ok(Scalar::new(inverse)),
            None => bail!("Failed to invert a scalar element: {self}"),
        }
    }
}

impl Square for Scalar {
    type Output = Scalar;

    /// Returns the `square` of `self`.
    #[inline]
    fn square(&self) -> Self::Output {
        Scalar::new(self.scalar.square())
    }
}

impl Sum<Scalar> for Scalar {
    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn sum<I: Iterator<Item = Scalar>>(iter: I) -> Self {
        iter.fold(Scalar::zero(), |a, b| a + b)
    }
}

impl<'a> Sum<&'a Scalar> for Scalar {
    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn sum<I: Iterator<Item = &'a Scalar>>(iter: I) -> Self {
        iter.fold(Scalar::zero(), |a, b| a + b)
    }
}

impl Product<Scalar> for Scalar {
    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn product<I: Iterator<Item = Scalar>>(iter: I) -> Self {
        iter.fold(Scalar::one(), |a, b| a * b)
    }
}

impl<'a> Product<&'a Scalar> for Scalar {
    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn product<I: Iterator<Item = &'a Scalar>>(iter: I) -> Self {
        iter.fold(Scalar::one(), |a, b| a * b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_div_by_zero_fails() {
        let one = Scalar::one();
        let zero = Scalar::zero();

        let result = std::panic::catch_unwind(|| one / zero);
        assert!(result.is_err()); // Probe further for specific error type here, if desired
    }
}
