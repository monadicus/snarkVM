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

impl Ternary for Field {
    type Boolean = Boolean;
    type Output = Self;

    /// Returns `first` if `condition` is `true`, otherwise returns `second`.
    fn ternary(condition: &Self::Boolean, first: &Self, second: &Self) -> Self::Output {
        // Constant `condition`
        if condition.is_constant() {
            match condition.eject_value() {
                true => first.clone(),
                false => second.clone(),
            }
        }
        // Constant `first` and `second`
        else if first.is_constant() && second.is_constant() {
            let not_condition = Field::from_boolean(&!condition);
            let condition = Field::from_boolean(condition);
            (condition * first) + (not_condition * second)
        }
        // Variables
        else {
            // Initialize the witness.
            let witness = witness!(|condition, first, second| match condition {
                true => first,
                false => second,
            });

            //
            // Ternary Enforcement
            // -------------------------------------------------------
            //    witness = condition * a + (1 - condition) * b
            // => witness = b + condition * (a - b)
            // => (a - b) * condition = witness - b
            //
            //
            // Assumption
            // -------------------------------------------------------
            // If a == b, either values suffices as a valid witness,
            // and we may forgo the cases below. Else, we consider
            // the following four cases.
            //
            //
            // Case 1: condition = 0 AND witness = a (dishonest)
            // -------------------------------------------------------
            // (a - b) * 0 = a - b
            //           0 = a - b
            // => if a != b, as LHS != RHS, the witness is incorrect.
            //
            //
            // Case 2: condition = 0 AND witness = b (honest)
            // -------------------------------------------------------
            // (a - b) * 0 = b - b
            //           0 = 0
            // => as LHS == RHS, the witness is correct.
            //
            //
            // Case 3: condition = 1 AND witness = a (honest)
            // -------------------------------------------------------
            // (a - b) * 1 = a - b
            //       a - b = a - b
            // => as LHS == RHS, the witness is correct.
            //
            //
            // Case 4: condition = 1 AND witness = b (dishonest)
            // -------------------------------------------------------
            // (a - b) * 1 = b - b
            //       a - b = 0
            // => if a != b, as LHS != RHS, the witness is incorrect.
            //
            Circuit::enforce(|| ((first - second), condition, (&witness - second)));

            witness
        }
    }
}

impl Metrics<dyn Ternary<Boolean = Boolean, Output = Field>> for Field {
    type Case = (Mode, Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match case {
            (Mode::Constant, _, _)
            | (Mode::Public, Mode::Constant, Mode::Constant)
            | (Mode::Private, Mode::Constant, Mode::Constant) => Count::is(0, 0, 0, 0),
            _ => Count::is(0, 0, 1, 1),
        }
    }
}

impl OutputMode<dyn Ternary<Boolean = Boolean, Output = Field>> for Field {
    type Case = (CircuitType<Boolean>, Mode, Mode);

    fn output_mode(parameter: &Self::Case) -> Mode {
        match parameter.0.mode().is_constant() {
            true => match &parameter.0 {
                CircuitType::Constant(circuit) => match circuit.eject_value() {
                    true => parameter.1,
                    false => parameter.2,
                },
                _ => Circuit::halt("Circuit is required to determine output mode."),
            },
            false => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_ternary(name: &str, expected: console::Field, condition: Boolean, a: Field, b: Field) {
        Circuit::scope(name, || {
            let case = format!("({} ? {} : {})", condition.eject_value(), a.eject_value(), b.eject_value());
            let candidate = Field::ternary(&condition, &a, &b);
            assert_eq!(expected, candidate.eject_value(), "{case}");
            assert_count!(Ternary(Boolean, Field, Field) => Field, &(condition.eject_mode(), a.eject_mode(), b.eject_mode()));
            assert_output_mode!(Ternary(Boolean, Field, Field) => Field, &(CircuitType::from(&condition), a.eject_mode(), b.eject_mode()), candidate);
        });
    }

    #[test]
    fn test_constant_condition() {
        let mut rng = TestRng::default();

        let first = Uniform::rand(&mut rng);
        let second = Uniform::rand(&mut rng);

        // false ? Constant : Constant
        let expected = second;
        let condition = Boolean::new(Mode::Constant, false);
        let a = Field::new(Mode::Constant, first);
        let b = Field::new(Mode::Constant, second);
        check_ternary("false ? Constant : Constant", expected, condition, a, b);

        // false ? Constant : Public
        let expected = second;
        let condition = Boolean::new(Mode::Constant, false);
        let a = Field::new(Mode::Constant, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("false ? Constant : Public", expected, condition, a, b);

        // false ? Public : Constant
        let expected = second;
        let condition = Boolean::new(Mode::Constant, false);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Constant, second);
        check_ternary("false ? Public : Constant", expected, condition, a, b);

        // false ? Public : Public
        let expected = second;
        let condition = Boolean::new(Mode::Constant, false);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("false ? Public : Public", expected, condition, a, b);

        // false ? Public : Private
        let expected = second;
        let condition = Boolean::new(Mode::Constant, false);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Private, second);
        check_ternary("false ? Public : Private", expected, condition, a, b);

        // false ? Private : Private
        let expected = second;
        let condition = Boolean::new(Mode::Constant, false);
        let a = Field::new(Mode::Private, first);
        let b = Field::new(Mode::Private, second);
        check_ternary("false ? Private : Private", expected, condition, a, b);

        // true ? Constant : Constant
        let expected = first;
        let condition = Boolean::new(Mode::Constant, true);
        let a = Field::new(Mode::Constant, first);
        let b = Field::new(Mode::Constant, second);
        check_ternary("true ? Constant : Constant", expected, condition, a, b);

        // true ? Constant : Public
        let expected = first;
        let condition = Boolean::new(Mode::Constant, true);
        let a = Field::new(Mode::Constant, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("true ? Constant : Public", expected, condition, a, b);

        // true ? Public : Constant
        let expected = first;
        let condition = Boolean::new(Mode::Constant, true);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Constant, second);
        check_ternary("true ? Public : Constant", expected, condition, a, b);

        // true ? Public : Public
        let expected = first;
        let condition = Boolean::new(Mode::Constant, true);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("true ? Public : Public", expected, condition, a, b);

        // true ? Public : Private
        let expected = first;
        let condition = Boolean::new(Mode::Constant, true);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Private, second);
        check_ternary("true ? Public : Private", expected, condition, a, b);

        // true ? Private : Private
        let expected = first;
        let condition = Boolean::new(Mode::Constant, true);
        let a = Field::new(Mode::Private, first);
        let b = Field::new(Mode::Private, second);
        check_ternary("true ? Private : Private", expected, condition, a, b);
    }

    #[test]
    fn test_public_condition_and_constant_inputs() {
        let mut rng = TestRng::default();

        let first = Uniform::rand(&mut rng);
        let second = Uniform::rand(&mut rng);

        // false ? Constant : Constant
        let expected = second;
        let condition = Boolean::new(Mode::Public, false);
        let a = Field::new(Mode::Constant, first);
        let b = Field::new(Mode::Constant, second);
        check_ternary("false ? Constant : Constant", expected, condition, a, b);

        // true ? Constant : Constant
        let expected = first;
        let condition = Boolean::new(Mode::Public, true);
        let a = Field::new(Mode::Constant, first);
        let b = Field::new(Mode::Constant, second);
        check_ternary("true ? Constant : Constant", expected, condition, a, b);
    }

    #[test]
    fn test_public_condition_and_mixed_inputs() {
        let mut rng = TestRng::default();

        let first = Uniform::rand(&mut rng);
        let second = Uniform::rand(&mut rng);

        // false ? Constant : Public
        let expected = second;
        let condition = Boolean::new(Mode::Public, false);
        let a = Field::new(Mode::Constant, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("false ? Constant : Public", expected, condition, a, b);

        // false ? Public : Constant
        let expected = second;
        let condition = Boolean::new(Mode::Public, false);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Constant, second);
        check_ternary("false ? Public : Constant", expected, condition, a, b);

        // true ? Constant : Public
        let expected = first;
        let condition = Boolean::new(Mode::Public, true);
        let a = Field::new(Mode::Constant, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("true ? Constant : Public", expected, condition, a, b);

        // true ? Public : Constant
        let expected = first;
        let condition = Boolean::new(Mode::Public, true);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Constant, second);
        check_ternary("true ? Public : Constant", expected, condition, a, b);
    }

    #[test]
    fn test_private_condition_and_constant_inputs() {
        let mut rng = TestRng::default();

        let first = Uniform::rand(&mut rng);
        let second = Uniform::rand(&mut rng);

        // false ? Constant : Constant
        let expected = second;
        let condition = Boolean::new(Mode::Private, false);
        let a = Field::new(Mode::Constant, first);
        let b = Field::new(Mode::Constant, second);
        check_ternary("false ? Constant : Constant", expected, condition, a, b);

        // true ? Constant : Constant
        let expected = first;
        let condition = Boolean::new(Mode::Private, true);
        let a = Field::new(Mode::Constant, first);
        let b = Field::new(Mode::Constant, second);
        check_ternary("true ? Constant : Constant", expected, condition, a, b);
    }

    #[test]
    fn test_private_condition_and_mixed_inputs() {
        let mut rng = TestRng::default();

        let first = Uniform::rand(&mut rng);
        let second = Uniform::rand(&mut rng);

        // false ? Constant : Public
        let expected = second;
        let condition = Boolean::new(Mode::Private, false);
        let a = Field::new(Mode::Constant, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("false ? Constant : Public", expected, condition, a, b);

        // false ? Public : Constant
        let expected = second;
        let condition = Boolean::new(Mode::Private, false);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Constant, second);
        check_ternary("false ? Public : Constant", expected, condition, a, b);

        // true ? Constant : Public
        let expected = first;
        let condition = Boolean::new(Mode::Private, true);
        let a = Field::new(Mode::Constant, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("true ? Constant : Public", expected, condition, a, b);

        // true ? Public : Constant
        let expected = first;
        let condition = Boolean::new(Mode::Private, true);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Constant, second);
        check_ternary("true ? Public : Constant", expected, condition, a, b);
    }

    #[test]
    fn test_public_condition_and_variable_inputs() {
        let mut rng = TestRng::default();

        let first = Uniform::rand(&mut rng);
        let second = Uniform::rand(&mut rng);

        // false ? Public : Public
        let expected = second;
        let condition = Boolean::new(Mode::Public, false);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("false ? Public : Public", expected, condition, a, b);

        // false ? Public : Private
        let expected = second;
        let condition = Boolean::new(Mode::Public, false);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Private, second);
        check_ternary("false ? Public : Private", expected, condition, a, b);

        // false ? Private : Public
        let expected = second;
        let condition = Boolean::new(Mode::Public, false);
        let a = Field::new(Mode::Private, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("false ? Private : Public", expected, condition, a, b);

        // false ? Private : Private
        let expected = second;
        let condition = Boolean::new(Mode::Public, false);
        let a = Field::new(Mode::Private, first);
        let b = Field::new(Mode::Private, second);
        check_ternary("false ? Private : Private", expected, condition, a, b);

        // true ? Public : Public
        let expected = first;
        let condition = Boolean::new(Mode::Public, true);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("true ? Public : Public", expected, condition, a, b);

        // true ? Public : Private
        let expected = first;
        let condition = Boolean::new(Mode::Public, true);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Private, second);
        check_ternary("true ? Public : Private", expected, condition, a, b);

        // true ? Private : Public
        let expected = first;
        let condition = Boolean::new(Mode::Public, true);
        let a = Field::new(Mode::Private, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("true ? Private : Public", expected, condition, a, b);

        // true ? Private : Private
        let expected = first;
        let condition = Boolean::new(Mode::Public, true);
        let a = Field::new(Mode::Private, first);
        let b = Field::new(Mode::Private, second);
        check_ternary("true ? Private : Private", expected, condition, a, b);
    }

    #[test]
    fn test_private_condition_and_variable_inputs() {
        let mut rng = TestRng::default();

        let first = Uniform::rand(&mut rng);
        let second = Uniform::rand(&mut rng);

        // false ? Public : Public
        let expected = second;
        let condition = Boolean::new(Mode::Private, false);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("false ? Public : Public", expected, condition, a, b);

        // false ? Public : Private
        let expected = second;
        let condition = Boolean::new(Mode::Private, false);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Private, second);
        check_ternary("false ? Public : Private", expected, condition, a, b);

        // false ? Private : Public
        let expected = second;
        let condition = Boolean::new(Mode::Private, false);
        let a = Field::new(Mode::Private, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("false ? Private : Public", expected, condition, a, b);

        // false ? Private : Private
        let expected = second;
        let condition = Boolean::new(Mode::Private, false);
        let a = Field::new(Mode::Private, first);
        let b = Field::new(Mode::Private, second);
        check_ternary("false ? Private : Private", expected, condition, a, b);

        // true ? Public : Public
        let expected = first;
        let condition = Boolean::new(Mode::Private, true);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("true ? Public : Public", expected, condition, a, b);

        // true ? Public : Private
        let expected = first;
        let condition = Boolean::new(Mode::Private, true);
        let a = Field::new(Mode::Public, first);
        let b = Field::new(Mode::Private, second);
        check_ternary("true ? Public : Private", expected, condition, a, b);

        // true ? Private : Public
        let expected = first;
        let condition = Boolean::new(Mode::Private, true);
        let a = Field::new(Mode::Private, first);
        let b = Field::new(Mode::Public, second);
        check_ternary("true ? Private : Public", expected, condition, a, b);

        // true ? Private : Private
        let expected = first;
        let condition = Boolean::new(Mode::Private, true);
        let a = Field::new(Mode::Private, first);
        let b = Field::new(Mode::Private, second);
        check_ternary("true ? Private : Private", expected, condition, a, b);
    }
}
