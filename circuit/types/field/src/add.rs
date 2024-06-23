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

use console::{Console, Environment};

use super::*;

impl Add<Field> for Field {
    type Output = Field;

    fn add(self, other: Field) -> Self::Output {
        self + &other
    }
}

impl Add<&Field> for Field {
    type Output = Field;

    fn add(self, other: &Field) -> Self::Output {
        let mut result = self;
        result += other;
        result
    }
}

impl Add<Field> for &Field {
    type Output = Field;

    fn add(self, other: Field) -> Self::Output {
        self + &other
    }
}

impl Add<&Field> for &Field {
    type Output = Field;

    fn add(self, other: &Field) -> Self::Output {
        let mut result = self.clone();
        result += other;
        result
    }
}

impl AddAssign<Field> for Field {
    fn add_assign(&mut self, other: Field) {
        *self += &other;
    }
}

impl AddAssign<&Field> for Field {
    fn add_assign(&mut self, other: &Field) {
        self.linear_combination += &other.linear_combination;
        self.bits_le = Default::default();
    }
}

impl Metrics<dyn Add<Field, Output = Field>> for Field {
    type Case = (Mode, Mode);

    fn count(_case: &Self::Case) -> Count {
        Count::is(0, 0, 0, 0)
    }
}

impl OutputMode<dyn Add<Field, Output = Field>> for Field {
    type Case = (CircuitType<Field>, CircuitType<Field>);

    fn output_mode(case: &Self::Case) -> Mode {
        match (case.0.mode(), case.1.mode()) {
            (Mode::Constant, Mode::Constant) => Mode::Constant,
            (Mode::Constant, Mode::Public) => match &case.0 {
                CircuitType::Constant(constant) => match constant.eject_value().is_zero() {
                    true => Mode::Public,
                    false => Mode::Private,
                },
                _ => Console::halt("The constant is required to determine the output mode of Public + Constant"),
            },
            (Mode::Public, Mode::Constant) => match &case.1 {
                CircuitType::Constant(constant) => match constant.eject_value().is_zero() {
                    true => Mode::Public,
                    false => Mode::Private,
                },
                _ => Console::halt("The constant is required to determine the output mode of Public + Constant"),
            },
            (_, _) => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::{Circuit, Environment};

    const ITERATIONS: u64 = 10_000;

    fn check_add(name: &str, expected: &console::Field, a: &Field, b: &Field) {
        Circuit::scope(name, || {
            let candidate = a + b;
            assert_eq!(*expected, candidate.eject_value(), "({} + {})", a.eject_value(), b.eject_value());
            assert_count!(Add(Field, Field) => Field, &(a.eject_mode(), b.eject_mode()));
            assert_output_mode!(Add(Field, Field) => Field, &(CircuitType::from(a), CircuitType::from(b)), candidate);
        });
    }

    fn check_add_assign(name: &str, expected: &console::Field, a: &Field, b: &Field) {
        Circuit::scope(name, || {
            let mut candidate = a.clone();
            candidate += b;
            assert_eq!(*expected, candidate.eject_value(), "({} + {})", a.eject_value(), b.eject_value());
            assert_count!(Add(Field, Field) => Field, &(a.eject_mode(), b.eject_mode()));
            assert_output_mode!(Add(Field, Field) => Field, &(CircuitType::from(a), CircuitType::from(b)), candidate);
        });
    }

    fn run_test(mode_a: Mode, mode_b: Mode) {
        let mut rng = TestRng::default();

        for i in 0..ITERATIONS {
            let first = Uniform::rand(&mut rng);
            let second = Uniform::rand(&mut rng);

            let expected = first + second;
            let a = Field::new(mode_a, first);
            let b = Field::new(mode_b, second);

            let name = format!("Add: a + b {i}");
            check_add(&name, &expected, &a, &b);
            let name = format!("AddAssign: a + b {i}");
            check_add_assign(&name, &expected, &a, &b);

            // Test identity.
            let name = format!("Add: a + 0 {i}");
            let zero = Field::new(mode_b, console::Field::zero());
            check_add(&name, &first, &a, &zero);
            let name = format!("AddAssign: a + 0 {i}");
            check_add_assign(&name, &first, &a, &zero);

            let name = format!("Add: 0 + b {i}");
            let zero = Field::new(mode_a, console::Field::zero());
            check_add(&name, &second, &zero, &b);
            let name = format!("AddAssign: 0 + b {i}");
            check_add_assign(&name, &second, &zero, &b);
        }
    }

    #[test]
    fn test_constant_plus_constant() {
        run_test(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_constant_plus_public() {
        run_test(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_public_plus_constant() {
        run_test(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_constant_plus_private() {
        run_test(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_private_plus_constant() {
        run_test(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_public_plus_public() {
        run_test(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_public_plus_private() {
        run_test(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_private_plus_public() {
        run_test(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_private_plus_private() {
        run_test(Mode::Private, Mode::Private);
    }

    #[test]
    fn test_0_plus_0() {
        let zero = console::Field::zero();

        let candidate = Field::zero() + Field::zero();
        assert_eq!(zero, candidate.eject_value());

        let candidate = Field::zero() + &Field::zero();
        assert_eq!(zero, candidate.eject_value());

        let candidate = Field::new(Mode::Public, zero) + Field::new(Mode::Public, zero);
        assert_eq!(zero, candidate.eject_value());

        let candidate = Field::new(Mode::Public, zero) + Field::new(Mode::Private, zero);
        assert_eq!(zero, candidate.eject_value());

        let candidate = Field::new(Mode::Private, zero) + Field::new(Mode::Private, zero);
        assert_eq!(zero, candidate.eject_value());
    }

    #[test]
    fn test_0_plus_1() {
        let zero = console::Field::zero();
        let one = console::Field::one();

        let candidate = Field::zero() + Field::one();
        assert_eq!(one, candidate.eject_value());

        let candidate = Field::zero() + &Field::one();
        assert_eq!(one, candidate.eject_value());

        let candidate = Field::one() + Field::zero();
        assert_eq!(one, candidate.eject_value());

        let candidate = Field::one() + &Field::zero();
        assert_eq!(one, candidate.eject_value());

        let candidate = Field::new(Mode::Public, one) + Field::new(Mode::Public, zero);
        assert_eq!(one, candidate.eject_value());

        let candidate = Field::new(Mode::Public, one) + Field::new(Mode::Private, zero);
        assert_eq!(one, candidate.eject_value());

        let candidate = Field::new(Mode::Private, one) + Field::new(Mode::Private, zero);
        assert_eq!(one, candidate.eject_value());
    }

    #[test]
    fn test_1_plus_1() {
        let one = console::Field::one();
        let two = one + one;

        let candidate = Field::one() + Field::one();
        assert_eq!(two, candidate.eject_value());

        let candidate = Field::one() + &Field::one();
        assert_eq!(two, candidate.eject_value());

        let candidate = Field::new(Mode::Public, one) + Field::new(Mode::Public, one);
        assert_eq!(two, candidate.eject_value());

        let candidate = Field::new(Mode::Private, one) + Field::new(Mode::Public, one);
        assert_eq!(two, candidate.eject_value());

        let candidate = Field::new(Mode::Private, one) + Field::new(Mode::Private, one);
        assert_eq!(two, candidate.eject_value());
    }

    #[test]
    fn test_1_plus_2() {
        let one = console::Field::one();
        let two = one + one;
        let three = two + one;

        let candidate_two = Field::one() + Field::one();
        let candidate = candidate_two + Field::one();
        assert_eq!(three, candidate.eject_value());

        let candidate_two = Field::one() + &Field::one();
        let candidate = candidate_two + &Field::one();
        assert_eq!(three, candidate.eject_value());

        let candidate = Field::new(Mode::Public, one) + Field::new(Mode::Public, two);
        assert_eq!(three, candidate.eject_value());

        let candidate = Field::new(Mode::Private, one) + Field::new(Mode::Public, two);
        assert_eq!(three, candidate.eject_value());

        let candidate = Field::new(Mode::Private, one) + Field::new(Mode::Private, two);
        assert_eq!(three, candidate.eject_value());
    }
}
