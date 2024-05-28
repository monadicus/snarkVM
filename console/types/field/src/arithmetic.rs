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

impl Neg for Field {
    type Output = Field;

    /// Returns the `negation` of `self`.
    #[inline]
    fn neg(self) -> Self::Output {
        Field::new(-self.field)
    }
}

impl Add<Field> for Field {
    type Output = Field;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: Field) -> Self::Output {
        Field::new(self.field + other.field)
    }
}

impl Add<&Field> for Field {
    type Output = Field;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: &Field) -> Self::Output {
        Field::new(self.field + other.field)
    }
}

impl AddAssign<Field> for Field {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: Field) {
        self.field += other.field;
    }
}

impl AddAssign<&Field> for Field {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: &Field) {
        self.field += other.field;
    }
}

impl Sub<Field> for Field {
    type Output = Field;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: Field) -> Self::Output {
        Field::new(self.field - other.field)
    }
}

impl Sub<&Field> for Field {
    type Output = Field;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: &Field) -> Self::Output {
        Field::new(self.field - other.field)
    }
}

impl SubAssign<Field> for Field {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: Field) {
        self.field -= other.field;
    }
}

impl SubAssign<&Field> for Field {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: &Field) {
        self.field -= other.field;
    }
}

impl Mul<Field> for Field {
    type Output = Field;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: Field) -> Self::Output {
        Field::new(self.field * other.field)
    }
}

impl Mul<&Field> for Field {
    type Output = Field;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: &Field) -> Self::Output {
        Field::new(self.field * other.field)
    }
}

impl MulAssign<Field> for Field {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: Field) {
        self.field *= other.field;
    }
}

impl MulAssign<&Field> for Field {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: &Field) {
        self.field *= other.field;
    }
}

impl Div<Field> for Field {
    type Output = Field;

    /// Returns the `quotient` of `self` and `other`.
    #[inline]
    fn div(self, other: Field) -> Self::Output {
        match other.is_zero() {
            true => Console::halt(format!("Field division by zero: {self} / {other}")),
            false => Field::new(self.field / other.field),
        }
    }
}

impl Div<&Field> for Field {
    type Output = Field;

    /// Returns the `quotient` of `self` and `other`.
    #[inline]
    fn div(self, other: &Field) -> Self::Output {
        match other.is_zero() {
            true => Console::halt(format!("Field division by zero: {self} / {other}")),
            false => Field::new(self.field / other.field),
        }
    }
}

impl DivAssign<Field> for Field {
    /// Divides `self` by `other`.
    #[inline]
    fn div_assign(&mut self, other: Field) {
        match other.is_zero() {
            true => Console::halt(format!("Field division by zero: {self} / {other}")),
            false => self.field /= other.field,
        }
    }
}

impl DivAssign<&Field> for Field {
    /// Divides `self` by `other`.
    #[inline]
    fn div_assign(&mut self, other: &Field) {
        match other.is_zero() {
            true => Console::halt(format!("Field division by zero: {self} / {other}")),
            false => self.field /= other.field,
        }
    }
}

impl Pow<Field> for Field {
    type Output = Field;

    /// Returns the `power` of `self` to the power of `other`.
    #[inline]
    fn pow(self, other: Field) -> Self::Output {
        Field::new(self.field.pow(other.field.to_bigint()))
    }
}

impl Pow<&Field> for Field {
    type Output = Field;

    /// Returns the `power` of `self` to the power of `other`.
    #[inline]
    fn pow(self, other: &Field) -> Self::Output {
        Field::new(self.field.pow(other.field.to_bigint()))
    }
}

impl Double for Field {
    type Output = Field;

    /// Returns the `double` of `self`.
    #[inline]
    fn double(&self) -> Self::Output {
        Field::new(self.field.double())
    }
}

impl Inverse for Field {
    type Output = Field;

    /// Returns the `inverse` of `self`.
    #[inline]
    fn inverse(&self) -> Result<Self::Output> {
        match self.field.inverse() {
            Some(inverse) => Ok(Field::new(inverse)),
            None => bail!("Failed to invert a field element: {self}"),
        }
    }
}

impl Square for Field {
    type Output = Field;

    /// Returns the `square` of `self`.
    #[inline]
    fn square(&self) -> Self::Output {
        Field::new(self.field.square())
    }
}

impl SquareRoot for Field {
    type Output = Field;

    /// Returns the `square_root` of `self`.
    /// If there are two square roots, the bitwise lesser one is returned.
    #[inline]
    fn square_root(&self) -> Result<Self::Output> {
        match self.field.sqrt() {
            Some(sqrt) => {
                // Return the smaller square root.
                let sqrt = Field::new(sqrt);
                let negative_sqrt: Field = -sqrt;
                match *(sqrt.is_less_than_or_equal(&negative_sqrt)) {
                    true => Ok(sqrt),
                    false => Ok(negative_sqrt),
                }
            }
            None => bail!("Failed to square root a field element: {self}"),
        }
    }
}

impl Field {
    /// Returns the `square_root` of `self`, where the least significant bit of the square root is zero.
    #[inline]
    pub fn even_square_root(&self) -> Result<Self> {
        match self.field.sqrt() {
            Some(sqrt) => {
                let sqrt: Field = Field::new(sqrt);
                // Check the least significant bit of the square root.
                // Note that the unwrap is safe since the number of bits is always greater than zero.
                match *sqrt.to_bits_be().last().unwrap() {
                    // If the lsb is set, return the negated square root.
                    true => Ok(-sqrt),
                    // Otherwise, return the square root.
                    false => Ok(sqrt),
                }
            }
            None => bail!("Failed to square root a field element: {self}"),
        }
    }
}

impl Sum<Field> for Field {
    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn sum<I: Iterator<Item = Field>>(iter: I) -> Self {
        iter.fold(Field::zero(), |a, b| a + b)
    }
}

impl<'a> Sum<&'a Field> for Field {
    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn sum<I: Iterator<Item = &'a Field>>(iter: I) -> Self {
        iter.fold(Field::zero(), |a, b| a + b)
    }
}

impl Product<Field> for Field {
    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn product<I: Iterator<Item = Field>>(iter: I) -> Self {
        iter.fold(Field::one(), |a, b| a * b)
    }
}

impl<'a> Product<&'a Field> for Field {
    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn product<I: Iterator<Item = &'a Field>>(iter: I) -> Self {
        iter.fold(Field::one(), |a, b| a * b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_div_by_zero_fails() {
        let one = Field::one();
        let zero = Field::zero();

        let result = std::panic::catch_unwind(|| one / zero);
        assert!(result.is_err()); // Probe further for specific error type here, if desired
    }
}
