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

use crate::Aleo;
use console::AleoNetwork;
use snarkvm_circuit_types::{
    environment::{prelude::*, Assignment, Circuit, R1CS},
    Boolean,
    Field,
    Group,
    Scalar,
};

use core::fmt;

type E = Circuit;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct AleoV0;

impl Aleo for AleoV0 {}

impl Environment for AleoV0 {
    type Affine = <E as Environment>::Affine;
    type BaseField = <E as Environment>::BaseField;
    type Network = <E as Environment>::Network;
    type ScalarField = <E as Environment>::ScalarField;

    /// Returns the `zero` constant.
    fn zero() -> LinearCombination<Self::BaseField> {
        Circuit::zero()
    }

    /// Returns the `one` constant.
    fn one() -> LinearCombination<Self::BaseField> {
        Circuit::one()
    }

    /// Returns a new variable of the given mode and value.
    fn new_variable(mode: Mode, value: Self::BaseField) -> Variable<Self::BaseField> {
        E::new_variable(mode, value)
    }

    /// Returns a new witness of the given mode and value.
    fn new_witness<Fn: FnOnce() -> Output::Primitive, Output: Inject>(mode: Mode, logic: Fn) -> Output {
        E::new_witness(mode, logic)
    }

    /// Enters a new scope for the environment.
    fn scope<S: Into<String>, Fn, Output>(name: S, logic: Fn) -> Output
    where
        Fn: FnOnce() -> Output,
    {
        E::scope(name, logic)
    }

    /// Adds one constraint enforcing that `(A * B) == C`.
    fn enforce<Fn, A, B, C>(constraint: Fn)
    where
        Fn: FnOnce() -> (A, B, C),
        A: Into<LinearCombination<Self::BaseField>>,
        B: Into<LinearCombination<Self::BaseField>>,
        C: Into<LinearCombination<Self::BaseField>>,
    {
        Circuit::enforce(constraint)
    }

    /// Returns `true` if all constraints in the environment are satisfied.
    fn is_satisfied() -> bool {
        E::is_satisfied()
    }

    /// Returns `true` if all constraints in the current scope are satisfied.
    fn is_satisfied_in_scope() -> bool {
        E::is_satisfied_in_scope()
    }

    /// Returns the number of constants in the entire circuit.
    fn num_constants() -> u64 {
        E::num_constants()
    }

    /// Returns the number of public variables in the entire circuit.
    fn num_public() -> u64 {
        E::num_public()
    }

    /// Returns the number of private variables in the entire circuit.
    fn num_private() -> u64 {
        E::num_private()
    }

    /// Returns the number of constant, public, and private variables in the entire circuit.
    fn num_variables() -> u64 {
        E::num_variables()
    }

    /// Returns the number of constraints in the entire circuit.
    fn num_constraints() -> u64 {
        E::num_constraints()
    }

    /// Returns the number of nonzeros in the entire circuit.
    fn num_nonzeros() -> (u64, u64, u64) {
        E::num_nonzeros()
    }

    /// Returns the number of constants for the current scope.
    fn num_constants_in_scope() -> u64 {
        E::num_constants_in_scope()
    }

    /// Returns the number of public variables for the current scope.
    fn num_public_in_scope() -> u64 {
        E::num_public_in_scope()
    }

    /// Returns the number of private variables for the current scope.
    fn num_private_in_scope() -> u64 {
        E::num_private_in_scope()
    }

    /// Returns the number of constraints for the current scope.
    fn num_constraints_in_scope() -> u64 {
        E::num_constraints_in_scope()
    }

    /// Returns the number of nonzeros for the current scope.
    fn num_nonzeros_in_scope() -> (u64, u64, u64) {
        E::num_nonzeros_in_scope()
    }

    /// Returns the variable limit for the circuit, if one exists.
    fn get_variable_limit() -> Option<u64> {
        E::get_variable_limit()
    }

    /// Sets the variable limit for the circuit.
    fn set_variable_limit(limit: Option<u64>) {
        E::set_variable_limit(limit)
    }

    /// Returns the constraint limit for the circuit, if one exists.
    fn get_constraint_limit() -> Option<u64> {
        E::get_constraint_limit()
    }

    /// Sets the constraint limit for the circuit.
    fn set_constraint_limit(limit: Option<u64>) {
        E::set_constraint_limit(limit)
    }

    /// Halts the program from further synthesis, evaluation, and execution in the current environment.
    fn halt<S: Into<String>, T>(message: S) -> T {
        Circuit::halt(message)
    }

    /// Returns the R1CS circuit, resetting the circuit.
    fn inject_r1cs(r1cs: R1CS<Self::BaseField>) {
        E::inject_r1cs(r1cs)
    }

    /// Returns the R1CS circuit, resetting the circuit.
    fn eject_r1cs_and_reset() -> R1CS<Self::BaseField> {
        E::eject_r1cs_and_reset()
    }

    /// Returns the R1CS assignment of the circuit, resetting the circuit.
    fn eject_assignment_and_reset() -> Assignment<<Self::Network as console::Environment>::Field> {
        E::eject_assignment_and_reset()
    }

    /// Clears the circuit and initializes an empty environment.
    fn reset() {
        E::reset()
    }
}

impl Display for AleoV0 {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // TODO (howardwu): Find a better way to print the circuit.
        fmt::Display::fmt(&Circuit, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::ConsoleField;
    use snarkvm_circuit_types::Field;

    type CurrentAleo = AleoV0;

    /// Compute 2^EXPONENT - 1, in a purposefully constraint-inefficient manner for testing.
    fn create_example_circuit() -> Field {
        let one = ConsoleField::one();
        let two = one + one;

        const EXPONENT: u64 = 64;

        // Compute 2^EXPONENT - 1, in a purposefully constraint-inefficient manner for testing.
        let mut candidate = Field::new(Mode::Public, one);
        let mut accumulator = Field::new(Mode::Private, two);
        for _ in 0..EXPONENT {
            candidate += &accumulator;
            accumulator *= Field::new(Mode::Private, two);
        }

        assert_eq!((accumulator - Field::one()).eject_value(), candidate.eject_value());
        assert_eq!(2, E::num_public());
        assert_eq!(2 * EXPONENT + 1, E::num_private());
        assert_eq!(EXPONENT, E::num_constraints());
        assert!(E::is_satisfied());

        candidate
    }

    #[test]
    fn test_print_circuit() {
        let circuit = CurrentAleo {};
        let _candidate = create_example_circuit();
        let output = format!("{circuit}");
        println!("{output}");
    }

    #[test]
    fn test_circuit_scope() {
        CurrentAleo::scope("test_circuit_scope", || {
            assert_eq!(0, CurrentAleo::num_constants());
            assert_eq!(1, CurrentAleo::num_public());
            assert_eq!(0, CurrentAleo::num_private());
            assert_eq!(0, CurrentAleo::num_constraints());

            assert_eq!(0, CurrentAleo::num_constants_in_scope());
            assert_eq!(0, CurrentAleo::num_public_in_scope());
            assert_eq!(0, CurrentAleo::num_private_in_scope());
            assert_eq!(0, CurrentAleo::num_constraints_in_scope());
        })
    }
}
