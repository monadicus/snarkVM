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
    type Output = Self;

    /// Performs the unary `-` operation.
    fn neg(self) -> Self::Output {
        (&self).neg()
    }
}

impl Neg for &Field {
    type Output = Field;

    /// Performs the unary `-` operation.
    fn neg(self) -> Self::Output {
        (-&self.linear_combination).into()
    }
}

impl Metrics<dyn Neg<Output = Field>> for Field {
    type Case = Mode;

    fn count(_case: &Self::Case) -> Count {
        Count::is(0, 0, 0, 0)
    }
}

impl OutputMode<dyn Neg<Output = Field>> for Field {
    type Case = Mode;

    fn output_mode(case: &Self::Case) -> Mode {
        match case {
            Mode::Constant => Mode::Constant,
            _ => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 1_000;

    fn check_neg(name: &str, mode: Mode, rng: &mut TestRng) {
        let check_neg = |given: console::Field| {
            // Compute it's negation.
            let expected = given.neg();
            let candidate = Field::new(mode, given);

            // Check negation.
            Circuit::scope(name, || {
                let result = candidate.neg();
                assert_eq!(expected, result.eject_value());
                assert_count!(Neg(Field) => Field, &mode);
                assert_output_mode!(Neg(Field) => Field, &mode, result);
            });
        };

        for _ in 0..ITERATIONS {
            // Sample a random element.
            let given = Uniform::rand(rng);
            check_neg(given)
        }
        // Check zero case.
        check_neg(console::Field::zero());
        // Check one case.
        check_neg(console::Field::one());
    }

    #[test]
    fn test_neg() {
        let mut rng = TestRng::default();

        check_neg("Constant", Mode::Constant, &mut rng);
        check_neg("Public", Mode::Public, &mut rng);
        check_neg("Private", Mode::Private, &mut rng);
    }

    #[test]
    fn test_zero() {
        let zero = console::Field::zero();

        let candidate = Field::zero();
        assert_eq!(zero, candidate.eject_value());
        assert_eq!(zero, (-&candidate).eject_value());
        assert_eq!(zero, (-(-candidate)).eject_value());

        let candidate = Field::new(Mode::Public, zero);
        assert_eq!(zero, candidate.eject_value());
        assert_eq!(zero, (-&candidate).eject_value());
        assert_eq!(zero, (-(-candidate)).eject_value());

        let candidate = Field::new(Mode::Private, zero);
        assert_eq!(zero, candidate.eject_value());
        assert_eq!(zero, (-&candidate).eject_value());
        assert_eq!(zero, (-(-candidate)).eject_value());
    }

    #[test]
    fn test_one() {
        let one = console::Field::one();

        let candidate = Field::one();
        assert_eq!(one, candidate.eject_value());
        assert_eq!(-one, (-&candidate).eject_value());
        assert_eq!(one, (-(-candidate)).eject_value());

        let candidate = Field::new(Mode::Public, one);
        assert_eq!(one, candidate.eject_value());
        assert_eq!(-one, (-&candidate).eject_value());
        assert_eq!(one, (-(-candidate)).eject_value());

        let candidate = Field::new(Mode::Private, one);
        assert_eq!(one, candidate.eject_value());
        assert_eq!(-one, (-&candidate).eject_value());
        assert_eq!(one, (-(-candidate)).eject_value());
    }
}
