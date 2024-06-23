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

impl FromBoolean for Field {
    type Boolean = Boolean;

    /// Initializes a base field from a boolean.
    fn from_boolean(boolean: &Self::Boolean) -> Self {
        Self::from((**boolean).clone())
    }
}

impl Metrics<dyn FromBoolean<Boolean = Boolean>> for Field {
    type Case = ();

    fn count(_case: &Self::Case) -> Count {
        Count::is(0, 0, 0, 0)
    }
}

impl OutputMode<dyn FromBoolean<Boolean = Boolean>> for Field {
    type Case = Mode;

    fn output_mode(case: &Self::Case) -> Mode {
        *case
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_from_boolean(mode: Mode) {
        for expected in &[true, false] {
            // Inject the boolean.
            let given = Boolean::new(mode, *expected);

            Circuit::scope(format!("{mode} {expected}"), || {
                let candidate = Field::from_boolean(&given);
                match expected {
                    true => {
                        assert_eq!(console::Field::one(), candidate.eject_value())
                    }
                    false => {
                        assert_eq!(console::Field::zero(), candidate.eject_value())
                    }
                }
                assert_count!(FromBoolean(Boolean) => Field, &());
                assert_output_mode!(FromBoolean(Boolean) => Field, &mode, candidate);
            });
        }
    }

    #[test]
    fn test_from_boolean_constant() {
        check_from_boolean(Mode::Constant);
    }

    #[test]
    fn test_from_boolean_public() {
        check_from_boolean(Mode::Public);
    }

    #[test]
    fn test_from_boolean_private() {
        check_from_boolean(Mode::Private);
    }
}
