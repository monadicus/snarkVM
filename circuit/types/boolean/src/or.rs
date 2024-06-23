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

impl BitOr<Boolean> for Boolean {
    type Output = Boolean;

    /// Returns `(self OR other)`.
    fn bitor(self, other: Boolean) -> Self::Output {
        self | &other
    }
}

impl BitOr<Boolean> for &Boolean {
    type Output = Boolean;

    /// Returns `(self OR other)`.
    fn bitor(self, other: Boolean) -> Self::Output {
        self | &other
    }
}

impl BitOr<&Boolean> for Boolean {
    type Output = Boolean;

    /// Returns `(self OR other)`.
    fn bitor(self, other: &Boolean) -> Self::Output {
        &self | other
    }
}

impl BitOr<&Boolean> for &Boolean {
    type Output = Boolean;

    /// Returns `(self OR other)`.
    fn bitor(self, other: &Boolean) -> Self::Output {
        let mut output = self.clone();
        output |= other;
        output
    }
}

impl BitOrAssign<Boolean> for Boolean {
    /// Sets `self` as `(self OR other)`.
    fn bitor_assign(&mut self, other: Boolean) {
        *self |= &other;
    }
}

#[allow(clippy::suspicious_op_assign_impl)]
impl BitOrAssign<&Boolean> for Boolean {
    /// Sets `self` as `(self OR other)`.
    fn bitor_assign(&mut self, other: &Boolean) {
        // Stores the bitwise OR of `self` and `other` in `self`.
        *self =
            // Constant `self`
            if self.is_constant() {
                match self.eject_value() {
                    true => self.clone(),
                    false => other.clone(),
                }
            }
            // Constant `other`
            else if other.is_constant() {
                match other.eject_value() {
                    true => other.clone(),
                    false => self.clone(),
                }
            }
            // Variable OR Variable
            else {
                // Declare a new variable with the expected output as witness.
                // Note: The constraint below will ensure `output` is either 0 or 1,
                // assuming `self` and `other` are well-formed (they are either 0 or 1).
                let output = Boolean(
                    Circuit::new_variable(Mode::Private, match self.eject_value() | other.eject_value() {
                        true => ConsoleField::one(),
                        false => ConsoleField::zero(),
                    })
                        .into(),
                );

                // Ensure (1 - `self`) * (1 - `other`) = (1 - `output`)
                // `output` is `1` iff `self` OR `other` is `1`.
                Circuit::enforce(|| (Circuit::one() - &self.0, Circuit::one() - &other.0, Circuit::one() - &output.0));

                output
            }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_or(
        name: &str,
        expected: bool,
        a: Boolean,
        b: Boolean,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        Circuit::scope(name, || {
            let candidate = &a | &b;
            assert_eq!(expected, candidate.eject_value(), "({} OR {})", a.eject_value(), b.eject_value());
            assert_scope!(num_constants, num_public, num_private, num_constraints);
        });
    }

    #[test]
    fn test_constant_or_constant() {
        // false OR false
        let expected = false;
        let a = Boolean::new(Mode::Constant, false);
        let b = Boolean::new(Mode::Constant, false);
        check_or("false OR false", expected, a, b, 0, 0, 0, 0);

        // false OR true
        let expected = true;
        let a = Boolean::new(Mode::Constant, false);
        let b = Boolean::new(Mode::Constant, true);
        check_or("false OR true", expected, a, b, 0, 0, 0, 0);

        // true OR false
        let expected = true;
        let a = Boolean::new(Mode::Constant, true);
        let b = Boolean::new(Mode::Constant, false);
        check_or("true OR false", expected, a, b, 0, 0, 0, 0);

        // true OR true
        let expected = true;
        let a = Boolean::new(Mode::Constant, true);
        let b = Boolean::new(Mode::Constant, true);
        check_or("true OR true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_or_public() {
        // false OR false
        let expected = false;
        let a = Boolean::new(Mode::Constant, false);
        let b = Boolean::new(Mode::Public, false);
        check_or("false OR false", expected, a, b, 0, 0, 0, 0);

        // false OR true
        let expected = true;
        let a = Boolean::new(Mode::Constant, false);
        let b = Boolean::new(Mode::Public, true);
        check_or("false OR true", expected, a, b, 0, 0, 0, 0);

        // true OR false
        let expected = true;
        let a = Boolean::new(Mode::Constant, true);
        let b = Boolean::new(Mode::Public, false);
        check_or("true OR false", expected, a, b, 0, 0, 0, 0);

        // true OR true
        let expected = true;
        let a = Boolean::new(Mode::Constant, true);
        let b = Boolean::new(Mode::Public, true);
        check_or("true OR true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_constant_or_private() {
        // false OR false
        let expected = false;
        let a = Boolean::new(Mode::Constant, false);
        let b = Boolean::new(Mode::Private, false);
        check_or("false OR false", expected, a, b, 0, 0, 0, 0);

        // false OR true
        let expected = true;
        let a = Boolean::new(Mode::Constant, false);
        let b = Boolean::new(Mode::Private, true);
        check_or("false OR true", expected, a, b, 0, 0, 0, 0);

        // true OR false
        let expected = true;
        let a = Boolean::new(Mode::Constant, true);
        let b = Boolean::new(Mode::Private, false);
        check_or("true OR false", expected, a, b, 0, 0, 0, 0);

        // true OR true
        let expected = true;
        let a = Boolean::new(Mode::Constant, true);
        let b = Boolean::new(Mode::Private, true);
        check_or("true OR true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_public_or_constant() {
        // false OR false
        let expected = false;
        let a = Boolean::new(Mode::Public, false);
        let b = Boolean::new(Mode::Constant, false);
        check_or("false OR false", expected, a, b, 0, 0, 0, 0);

        // false OR true
        let expected = true;
        let a = Boolean::new(Mode::Public, false);
        let b = Boolean::new(Mode::Constant, true);
        check_or("false OR true", expected, a, b, 0, 0, 0, 0);

        // true OR false
        let expected = true;
        let a = Boolean::new(Mode::Public, true);
        let b = Boolean::new(Mode::Constant, false);
        check_or("true OR false", expected, a, b, 0, 0, 0, 0);

        // true OR true
        let expected = true;
        let a = Boolean::new(Mode::Public, true);
        let b = Boolean::new(Mode::Constant, true);
        check_or("true OR true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_public_or_public() {
        // false OR false
        let expected = false;
        let a = Boolean::new(Mode::Public, false);
        let b = Boolean::new(Mode::Public, false);
        check_or("false OR false", expected, a, b, 0, 0, 1, 1);

        // false OR true
        let expected = true;
        let a = Boolean::new(Mode::Public, false);
        let b = Boolean::new(Mode::Public, true);
        check_or("false OR true", expected, a, b, 0, 0, 1, 1);

        // true OR false
        let expected = true;
        let a = Boolean::new(Mode::Public, true);
        let b = Boolean::new(Mode::Public, false);
        check_or("true OR false", expected, a, b, 0, 0, 1, 1);

        // true OR true
        let expected = true;
        let a = Boolean::new(Mode::Public, true);
        let b = Boolean::new(Mode::Public, true);
        check_or("true OR true", expected, a, b, 0, 0, 1, 1);
    }

    #[test]
    fn test_public_or_private() {
        // false OR false
        let expected = false;
        let a = Boolean::new(Mode::Public, false);
        let b = Boolean::new(Mode::Private, false);
        check_or("false OR false", expected, a, b, 0, 0, 1, 1);

        // false OR true
        let expected = true;
        let a = Boolean::new(Mode::Public, false);
        let b = Boolean::new(Mode::Private, true);
        check_or("false OR true", expected, a, b, 0, 0, 1, 1);

        // true OR false
        let expected = true;
        let a = Boolean::new(Mode::Public, true);
        let b = Boolean::new(Mode::Private, false);
        check_or("true OR false", expected, a, b, 0, 0, 1, 1);

        // true OR true
        let expected = true;
        let a = Boolean::new(Mode::Public, true);
        let b = Boolean::new(Mode::Private, true);
        check_or("true OR true", expected, a, b, 0, 0, 1, 1);
    }

    #[test]
    fn test_private_or_constant() {
        // false OR false
        let expected = false;
        let a = Boolean::new(Mode::Private, false);
        let b = Boolean::new(Mode::Constant, false);
        check_or("false OR false", expected, a, b, 0, 0, 0, 0);

        // false OR true
        let expected = true;
        let a = Boolean::new(Mode::Private, false);
        let b = Boolean::new(Mode::Constant, true);
        check_or("false OR true", expected, a, b, 0, 0, 0, 0);

        // true OR false
        let expected = true;
        let a = Boolean::new(Mode::Private, true);
        let b = Boolean::new(Mode::Constant, false);
        check_or("true OR false", expected, a, b, 0, 0, 0, 0);

        // true OR true
        let expected = true;
        let a = Boolean::new(Mode::Private, true);
        let b = Boolean::new(Mode::Constant, true);
        check_or("true OR true", expected, a, b, 0, 0, 0, 0);
    }

    #[test]
    fn test_private_or_public() {
        // false OR false
        let expected = false;
        let a = Boolean::new(Mode::Private, false);
        let b = Boolean::new(Mode::Public, false);
        check_or("false OR false", expected, a, b, 0, 0, 1, 1);

        // false OR true
        let expected = true;
        let a = Boolean::new(Mode::Private, false);
        let b = Boolean::new(Mode::Public, true);
        check_or("false OR true", expected, a, b, 0, 0, 1, 1);

        // true OR false
        let expected = true;
        let a = Boolean::new(Mode::Private, true);
        let b = Boolean::new(Mode::Public, false);
        check_or("true OR false", expected, a, b, 0, 0, 1, 1);

        // true OR true
        let expected = true;
        let a = Boolean::new(Mode::Private, true);
        let b = Boolean::new(Mode::Public, true);
        check_or("true OR true", expected, a, b, 0, 0, 1, 1);
    }

    #[test]
    fn test_private_or_private() {
        // false OR false
        let expected = false;
        let a = Boolean::new(Mode::Private, false);
        let b = Boolean::new(Mode::Private, false);
        check_or("false OR false", expected, a, b, 0, 0, 1, 1);

        // false OR true
        let expected = true;
        let a = Boolean::new(Mode::Private, false);
        let b = Boolean::new(Mode::Private, true);
        check_or("false OR true", expected, a, b, 0, 0, 1, 1);

        // true OR false
        let expected = true;
        let a = Boolean::new(Mode::Private, true);
        let b = Boolean::new(Mode::Private, false);
        check_or("true OR false", expected, a, b, 0, 0, 1, 1);

        // true OR true
        let expected = true;
        let a = Boolean::new(Mode::Private, true);
        let b = Boolean::new(Mode::Private, true);
        check_or("true OR true", expected, a, b, 0, 0, 1, 1);
    }
}
