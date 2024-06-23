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

impl One for Field {
    type Boolean = Boolean;

    fn one() -> Self {
        Circuit::one().into()
    }

    fn is_one(&self) -> Self::Boolean {
        self.is_equal(&Field::one())
    }
}

impl Metrics<dyn One<Boolean = Boolean>> for Field {
    type Case = ();

    fn count(_parameter: &Self::Case) -> Count {
        Count::is(0, 0, 0, 0)
    }
}

impl OutputMode<dyn One<Boolean = Boolean>> for Field {
    type Case = ();

    fn output_mode(_input: &Self::Case) -> Mode {
        Mode::Constant
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    #[test]
    fn test_one() {
        let one = console::Field::one();

        Circuit::scope("One", || {
            assert_scope!(0, 0, 0, 0);
            let candidate = Field::one();
            assert_eq!(one, candidate.eject_value());
            assert_count!(One<Boolean>() => Field, &());
            assert_output_mode!(One<Boolean>() => Field, &(), candidate);
        });
    }

    #[test]
    fn test_is_one() {
        let candidate = Field::one();
        // Should equal 1.
        assert!(candidate.is_one().eject_value());
        // Should not equal 0.
        assert!(!candidate.is_zero().eject_value());
    }
}
