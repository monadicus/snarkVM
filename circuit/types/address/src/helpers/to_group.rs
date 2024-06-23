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

impl From<Address> for Group {
    /// Returns the affine group element in the address.
    fn from(value: Address) -> Self {
        value.to_group()
    }
}

impl From<&Address> for Group {
    /// Returns the affine group element in the address.
    fn from(value: &Address) -> Self {
        value.to_group()
    }
}

impl ToGroup for Address {
    type Group = Group;
    type Scalar = Scalar;

    /// Returns the affine group element in the address.
    fn to_group(&self) -> Self::Group {
        self.0.clone()
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_to_group(name: &str, expected: console::Group, candidate: &Address) {
        Circuit::scope(name, || {
            // Perform the operation.
            let candidate = candidate.to_group();
            assert_eq!(expected, candidate.eject_value());
            assert_scope!(0, 0, 0, 0);
        });
    }

    #[test]
    fn test_to_group_constant() {
        let expected = console::Address::rand(&mut TestRng::default());
        let candidate = Address::new(Mode::Constant, expected);
        check_to_group("Constant", *expected, &candidate);
    }

    #[test]
    fn test_to_group_public() {
        let expected = console::Address::rand(&mut TestRng::default());
        let candidate = Address::new(Mode::Public, expected);
        check_to_group("Public", *expected, &candidate);
    }

    #[test]
    fn test_to_group_private() {
        let expected = console::Address::rand(&mut TestRng::default());
        let candidate = Address::new(Mode::Private, expected);
        check_to_group("Private", *expected, &candidate);
    }
}
