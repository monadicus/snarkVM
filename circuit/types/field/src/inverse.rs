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

impl Inv for Field {
    type Output = Self;

    fn inv(self) -> Self::Output {
        Self::inverse(&self)
    }
}

impl Inv for &Field {
    type Output = Field;

    fn inv(self) -> Self::Output {
        self.inverse()
    }
}

impl Inverse for Field {
    type Output = Field;

    fn inverse(&self) -> Self::Output {
        let inverse = witness!(|self| match self.inverse() {
            Ok(inverse) => inverse,
            _ => console::Field::zero(),
        });

        // Ensure `self` * `self^(-1)` == 1.
        Circuit::enforce(|| (self, &inverse, Circuit::one()));

        inverse
    }
}

impl Metrics<dyn Inverse<Output = Field>> for Field {
    type Case = Mode;

    fn count(case: &Self::Case) -> Count {
        match case.is_constant() {
            true => Count::is(1, 0, 0, 0),
            false => Count::is(0, 0, 1, 1),
        }
    }
}

impl OutputMode<dyn Inverse<Output = Field>> for Field {
    type Case = Mode;

    fn output_mode(case: &Self::Case) -> Mode {
        match case.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 1_000;

    fn check_inverse(name: &str, mode: Mode, rng: &mut TestRng) {
        for _ in 0..ITERATIONS {
            // Sample a random element.
            let given: console::Field = Uniform::rand(rng);
            // Compute it's inverse, or skip this iteration if it does not natively exist.
            if let Ok(expected) = given.inverse() {
                let candidate = Field::new(mode, given);

                Circuit::scope(name, || {
                    let result = candidate.inverse();
                    assert_eq!(expected, result.eject_value());
                    assert_count!(Inverse(Field) => Field, &mode);
                    assert_output_mode!(Inverse(Field) => Field, &mode, result);
                });
                Circuit::reset();
            }
        }
    }

    #[test]
    fn test_inverse() {
        let mut rng = TestRng::default();

        check_inverse("Constant", Mode::Constant, &mut rng);
        check_inverse("Public", Mode::Public, &mut rng);
        check_inverse("Private", Mode::Private, &mut rng);
    }

    #[test]
    fn test_zero_inverse_fails() {
        let zero = console::Field::zero();

        let result = std::panic::catch_unwind(|| Field::zero().inverse());
        assert!(result.is_err());
        Circuit::reset();

        let result = std::panic::catch_unwind(|| Field::new(Mode::Constant, zero).inverse());
        assert!(result.is_err());
        Circuit::reset();

        let candidate = Field::new(Mode::Public, zero).inverse();
        assert_eq!(zero, candidate.eject_value());
        assert!(!Circuit::is_satisfied());
        Circuit::reset();

        let candidate = Field::new(Mode::Private, zero).inverse();
        assert_eq!(zero, candidate.eject_value());
        assert!(!Circuit::is_satisfied());
        Circuit::reset();
    }
}
