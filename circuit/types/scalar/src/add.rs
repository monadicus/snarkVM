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

use console::ConsoleScalar;

use super::*;

impl Add<Scalar> for Scalar {
    type Output = Scalar;

    fn add(self, other: Scalar) -> Self::Output {
        self + &other
    }
}

impl Add<Scalar> for &Scalar {
    type Output = Scalar;

    fn add(self, other: Scalar) -> Self::Output {
        self + &other
    }
}

impl Add<&Scalar> for Scalar {
    type Output = Scalar;

    fn add(self, other: &Scalar) -> Self::Output {
        &self + other
    }
}

impl Add<&Scalar> for &Scalar {
    type Output = Scalar;

    fn add(self, other: &Scalar) -> Self::Output {
        let mut result = self.clone();
        result += other;
        result
    }
}

impl AddAssign<Scalar> for Scalar {
    fn add_assign(&mut self, other: Scalar) {
        *self += &other;
    }
}

impl AddAssign<&Scalar> for Scalar {
    fn add_assign(&mut self, other: &Scalar) {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            // Compute the sum and set the new constant in `self`.
            *self = witness!(|self, other| self + other);
        } else {
            // Instead of adding the bits of `self` and `other` directly, the scalars are
            // converted into a field elements, and summed, before converting back to scalars.
            // Note: This is safe as the base field is larger than the scalar field.
            let sum = self.to_field() + other.to_field();

            // Extract the scalar field bits from the field element, with a carry bit.
            // (For advanced users) This operation saves us 2 private variables and 2 constraints.
            let bits_le = sum.to_lower_bits_le(ConsoleScalar::size_in_bits() + 1);

            // Recover the sanitized (truncated) sum on the base field.
            // (For advanced users) This operation saves us 2 private variables and 2 constraints.
            let sum = Field::from_bits_le(&bits_le);

            // Initialize the scalar field modulus as a constant base field variable.
            //
            // Note: We are reconstituting the scalar field into a base field here in order to
            // compute the difference between the sum and modulus. This is safe as the scalar field modulus
            // is less that the base field modulus, and thus will always fit in a base field element.
            let modulus =
                Field::constant(match console::FromBits::from_bits_le(&ConsoleScalar::modulus().to_bits_le()) {
                    Ok(modulus) => modulus,
                    Err(error) => Circuit::halt(format!("Failed to retrieve the scalar modulus as bytes: {error}")),
                });

            // Determine the wrapping sum, by computing the difference between the sum and modulus, if `sum` < `modulus`.
            let wrapping_sum = Ternary::ternary(&sum.is_less_than(&modulus), &sum, &(&sum - &modulus));

            // Retrieve the bits of the wrapping sum.
            let bits_le = wrapping_sum.to_lower_bits_le(console::Scalar::size_in_bits());

            // Set the sum of `self` and `other`, in `self`.
            *self = Scalar { field: wrapping_sum, bits_le: OnceCell::with_value(bits_le) };
        }
    }
}

impl Metrics<dyn Add<Scalar, Output = Scalar>> for Scalar {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match (case.0, case.1) {
            (Mode::Constant, Mode::Constant) => Count::is(1, 0, 0, 0),
            (_, _) => Count::is(1, 0, 755, 757),
        }
    }
}

impl OutputMode<dyn Add<Scalar, Output = Scalar>> for Scalar {
    type Case = (Mode, Mode);

    fn output_mode(case: &Self::Case) -> Mode {
        match (case.0, case.1) {
            (Mode::Constant, Mode::Constant) => Mode::Constant,
            (_, _) => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 128;

    #[rustfmt::skip]
    fn check_add(
        name: &str,
        first: console::Scalar,
        second: console::Scalar,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Scalar::new(mode_a, first);
        let b = Scalar::new(mode_b, second);
        let case = format!("({} + {})", a.eject_value(), b.eject_value());
        let expected = first + second;

        Circuit::scope(name, || {
            let candidate = a + b;
            assert_eq!(expected, candidate.eject_value(), "{case}");
            assert_count!(Add(Scalar, Scalar) => Scalar, &(mode_a, mode_b));
            assert_output_mode!(Add(Scalar, Scalar) => Scalar, &(mode_a, mode_b), candidate);
        });
    }

    #[rustfmt::skip]
    fn run_test(
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let mut rng = TestRng::default();

        for i in 0..ITERATIONS {
            let first = Uniform::rand(&mut rng);
            let second = Uniform::rand(&mut rng);

            let name = format!("Add: {mode_a} + {mode_b} {i}");
            check_add(&name, first, second, mode_a, mode_b);

            let name = format!("Add: {mode_a} + {mode_b} {i} (commutative)");
            check_add(&name, second, first, mode_a, mode_b);
        }
    }

    #[test]
    fn test_scalar_constant_plus_constant() {
        run_test(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_scalar_constant_plus_public() {
        run_test(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_scalar_constant_plus_private() {
        run_test(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_scalar_public_plus_constant() {
        run_test(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_scalar_private_plus_constant() {
        run_test(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_scalar_public_plus_public() {
        run_test(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_scalar_public_plus_private() {
        run_test(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_scalar_private_plus_public() {
        run_test(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_scalar_private_plus_private() {
        run_test(Mode::Private, Mode::Private);
    }
}
