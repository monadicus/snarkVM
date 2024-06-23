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

impl Double for Field {
    type Output = Field;

    fn double(&self) -> Self::Output {
        self + self
    }
}

impl Metrics<dyn Double<Output = Field>> for Field {
    type Case = Mode;

    fn count(_parameter: &Self::Case) -> Count {
        Count::is(0, 0, 0, 0)
    }
}

impl OutputMode<dyn Double<Output = Field>> for Field {
    type Case = Mode;

    fn output_mode(input: &Self::Case) -> Mode {
        match input.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 10_000;

    fn check_double(name: &str, mode: Mode, rng: &mut TestRng) {
        for _ in 0..ITERATIONS {
            // Sample a random element.
            let given = Uniform::rand(rng);
            let candidate = Field::new(mode, given);

            Circuit::scope(name, || {
                let result = candidate.double();
                assert_eq!(given.double(), result.eject_value());
                assert_count!(Double(Field) => Field, &mode);
                assert_output_mode!(Double(Field) => Field, &mode, result);
            });
        }
    }

    #[test]
    fn test_double() {
        let mut rng = TestRng::default();

        check_double("Constant", Mode::Constant, &mut rng);
        check_double("Public", Mode::Public, &mut rng);
        check_double("Private", Mode::Private, &mut rng);
    }

    #[test]
    fn test_0_double() {
        let zero = console::Field::zero();

        let candidate = Field::new(Mode::Public, zero).double();
        assert_eq!(zero, candidate.eject_value());
    }

    #[test]
    fn test_1_double() {
        let one = console::Field::one();
        let two = one + one;

        let candidate = Field::new(Mode::Public, one).double();
        assert_eq!(two, candidate.eject_value());
    }
}
