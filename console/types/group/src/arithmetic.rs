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

impl Neg for Group {
    type Output = Group;

    /// Returns the `negation` of `self`.
    #[inline]
    fn neg(self) -> Self::Output {
        Group::from_projective(-self.group)
    }
}

impl Add<Group> for Group {
    type Output = Group;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: Group) -> Self::Output {
        Group::from_projective(self.group + other.group)
    }
}

impl Add<&Group> for Group {
    type Output = Group;

    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn add(self, other: &Group) -> Self::Output {
        Group::from_projective(self.group + other.group)
    }
}

impl AddAssign<Group> for Group {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: Group) {
        self.group += other.group;
    }
}

impl AddAssign<&Group> for Group {
    /// Adds `other` to `self`.
    #[inline]
    fn add_assign(&mut self, other: &Group) {
        self.group += other.group;
    }
}

impl Sub<Group> for Group {
    type Output = Group;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: Group) -> Self::Output {
        Group::from_projective(self.group - other.group)
    }
}

impl Sub<&Group> for Group {
    type Output = Group;

    /// Returns the `difference` of `self` and `other`.
    #[inline]
    fn sub(self, other: &Group) -> Self::Output {
        Group::from_projective(self.group - other.group)
    }
}

impl SubAssign<Group> for Group {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: Group) {
        self.group -= other.group;
    }
}

impl SubAssign<&Group> for Group {
    /// Subtracts `other` from `self`.
    #[inline]
    fn sub_assign(&mut self, other: &Group) {
        self.group -= other.group;
    }
}

impl Mul<Scalar> for Group {
    type Output = Group;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: Scalar) -> Self::Output {
        Group::from_projective(self.group * *other)
    }
}

impl Mul<&Scalar> for Group {
    type Output = Group;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: &Scalar) -> Self::Output {
        Group::from_projective(self.group * **other)
    }
}

impl Mul<Group> for Scalar {
    type Output = Group;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: Group) -> Self::Output {
        Group::from_projective(other.group * *self)
    }
}

impl Mul<&Group> for Scalar {
    type Output = Group;

    /// Returns the `product` of `self` and `other`.
    #[inline]
    fn mul(self, other: &Group) -> Self::Output {
        Group::from_projective(other.group * *self)
    }
}

impl MulAssign<Scalar> for Group {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: Scalar) {
        self.group *= *other;
    }
}

impl MulAssign<&Scalar> for Group {
    /// Multiplies `self` by `other`.
    #[inline]
    fn mul_assign(&mut self, other: &Scalar) {
        self.group *= **other;
    }
}

impl Double for Group {
    type Output = Group;

    /// Returns the `double` of `self`.
    #[inline]
    fn double(&self) -> Self::Output {
        Group::from_projective(self.group.double())
    }
}

impl Sum<Group> for Group {
    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn sum<I: Iterator<Item = Group>>(iter: I) -> Self {
        iter.fold(Group::zero(), |a, b| a + b)
    }
}

impl<'a> Sum<&'a Group> for Group {
    /// Returns the `sum` of `self` and `other`.
    #[inline]
    fn sum<I: Iterator<Item = &'a Group>>(iter: I) -> Self {
        iter.fold(Group::zero(), |a, b| a + b)
    }
}
