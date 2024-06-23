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

impl ToField for Group {
    type Field = Field;

    /// Returns the group as a field element.
    fn to_field(&self) -> Self::Field {
        self.to_x_coordinate()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    use console::ToField as ConsoleToField;

    const ITERATIONS: u64 = 100;

    fn check_to_field(mode: Mode) {
        let rng = &mut TestRng::default();

        for i in 0..ITERATIONS {
            // Sample a random element.
            let expected = Uniform::rand(rng);
            let candidate = Group::new(mode, expected);

            Circuit::scope(&format!("{mode} {i}"), || {
                let candidate = candidate.to_field();
                assert_eq!(expected.to_field().unwrap(), candidate.eject_value());
                assert_scope!(0, 0, 0, 0);
            });
        }
    }

    #[test]
    fn test_to_field_constant() {
        check_to_field(Mode::Constant);
    }

    #[test]
    fn test_to_field_public() {
        check_to_field(Mode::Public);
    }

    #[test]
    fn test_to_field_private() {
        check_to_field(Mode::Private);
    }
}
