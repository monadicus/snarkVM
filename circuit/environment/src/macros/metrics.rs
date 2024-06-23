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

#[macro_export]
macro_rules! count {
    ($type_:ty, $operation:path, $case:expr) => {
        <$type_ as Metrics<dyn $operation>>::count($case)
    };
}

#[macro_export]
macro_rules! output_mode {
    ($type_:ty, $operation:path, $case:expr) => {
        <$type_ as OutputMode<dyn $operation>>::output_mode($case)
    };
}

/// Asserts the count for a given operation and case, and ensure the circuit is satisfied.
///
/// ## Example
/// ```ignore
/// assert_count!(Add(Field, Field) => Field, &(mode_a, mode_b))
/// ```
#[macro_export]
macro_rules! assert_count {
    ($type_:ty, $operation:path, $case:expr) => {{
        $crate::print_scope!();

        let Count(num_constants, num_public, num_private, num_constraints) = count!($type_, $operation, $case);
        assert!(num_constants.matches($crate::Circuit::num_constants_in_scope()), "(num_constants)");
        assert!(num_public.matches($crate::Circuit::num_public_in_scope()), "(num_public)");
        assert!(num_private.matches($crate::Circuit::num_private_in_scope()), "(num_private)");
        assert!(num_constraints.matches($crate::Circuit::num_constraints_in_scope()), "(num_constraints)");
        assert!($crate::Circuit::is_satisfied_in_scope(), "(is_satisfied_in_scope)");
    }};

    //////////////
    // Standard //
    //////////////

    // Special case: FromBoolean trait deviates from the normal convention.
    (FromBoolean($input:ident) => $output:ident, $case:expr) => {{
        assert_count!($output, FromBoolean<Boolean = $input>, $case)
    }};
    // Empty case (special): Sets a Boolean associated type.
    ($operation:tt<$boolean:ident>() => $output:ident, $case:expr) => {{
        assert_count!($output, $operation<Boolean = $boolean>, $case)
    }};
    // Unary case
    ($operation:tt($input:ident) => $output:ident, $case:expr) => {{
        assert_count!($input, $operation<Output = $output>, $case)
    }};
    // Binary case
    ($operation:tt($input_a:ident, $input_b:ident) => $output:ident, $case:expr) => {{
        assert_count!($input_a, $operation<$input_b, Output = $output>, $case)
    }};
    // Ternary case (special): Hardcoded for a conditional ternary operator.
    // Note: $input_b is not used, as the Ternary trait does not require one.
    ($operation:tt($boolean:ident, $input_a:ident, $input_b:ident) => $output:ident, $case:expr) => {{
        assert_count!($input_a, $operation<Boolean = $boolean, Output = $output>, $case)
    }};

    ////////////
    // Custom //
    ////////////

    // Empty case (special & custom): Sets a Boolean associated type.
    ($operation:tt<$boolean:ident>() => $output:ident<$($parameter:ident),+>, $case:expr) => {{
        assert_count!($output<$($parameter),+>, $operation<Boolean = $boolean>, $case)
    }};
    // Unary case (custom).
    ($operation:tt($input:ident<$($parameter_a:ident),+>) => $output:ident<$($parameter_b:ident),+>, $case:expr) => {{
        assert_count!($input<$($parameter_a),+>, $operation<Output = $output<$($parameter_b),+>>, $case)
    }};
    // Binary case (custom)
    ($operation:tt($input_a:ident<$($parameter_a:ident),+>, $input_b:ident<$($parameter_b:ident),+>) => $output:ident, $case:expr) => {{
        assert_count!($input_a<$($parameter_a),+>, $operation<$input_b<$($parameter_b),+>, Output = $output>, $case)
    }};
    // Binary case (custom)
    ($operation:tt($input_a:ident<$($parameter_a:ident),+>, $input_b:ident<$($parameter_b:ident),+>) => $output:ident<$($parameter_c:ident),+>, $case:expr) => {{
        assert_count!($input_a<$($parameter_a),+>, $operation<$input_b<$($parameter_b),+>, Output = $output<$($parameter_c),+>>, $case)
    }};
    // Ternary case (special & custom): Hardcoded for a conditional ternary operator.
    // Note: $input_b is not used, as the Ternary trait does not require one.
    ($operation:tt($boolean:ident, $input_a:ident<$($parameter_a:ident),+>, $input_b:ident<$($parameter_b:ident),+>) => $output:ident<$($parameter_c:ident),+>, $case:expr) => {{
        assert_count!($input_a<$($parameter_a),+>, $operation<Boolean = $boolean, Output = $output<$($parameter_c),+>>, $case)
    }};
}

/// Asserts the count for a given operation and case, and ensure the circuit is NOT satisfied.
///
/// ## Example
/// ```ignore
/// assert_count_fails!(Add(Field, Field) => Field, &(mode_a, mode_b))
/// ```
#[macro_export]
macro_rules! assert_count_fails {
    ($type_:ty, $operation:path, $case:expr) => {{
        $crate::print_scope!();

        let Count(num_constants, num_public, num_private, num_constraints) = count!($type_, $operation, $case);
        assert!(num_constants.matches(Circuit::num_constants_in_scope()), "(num_constants)");
        assert!(num_public.matches(Circuit::num_public_in_scope()), "(num_public)");
        assert!(num_private.matches(Circuit::num_private_in_scope()), "(num_private)");
        assert!(num_constraints.matches(Circuit::num_constraints_in_scope()), "(num_constraints)");
        assert!(!Circuit::is_satisfied_in_scope(), "(!is_satisfied_in_scope)");
    }};

    //////////////
    // Standard //
    //////////////

    // Special case: FromBoolean trait deviates from the normal convention.
    (FromBoolean($input:ident) => $output:ident, $case:expr) => {{
        assert_count_fails!($output, FromBoolean<Boolean = $input>, $case)
    }};
    // Empty case (special): Sets a Boolean associated type.
    ($operation:tt<$boolean:ident>() => $output:ident, $case:expr) => {{
        assert_count_fails!($output, $operation<Boolean = $boolean>, $case)
    }};
    // Unary case
    ($operation:tt($input:ident) => $output:ident, $case:expr) => {{
        assert_count_fails!($input, $operation<Output = $output>, $case)
    }};
    // Binary case
    ($operation:tt($input_a:ident, $input_b:ident) => $output:ident, $case:expr) => {{
        assert_count_fails!($input_a, $operation<$input_b, Output = $output>, $case)
    }};
    // Ternary case (special): Hardcoded for a conditional ternary operator.
    // Note: $input_b is not used, as the Ternary trait does not require one.
    ($operation:tt($boolean:ident, $input_a:ident, $input_b:ident) => $output:ident, $case:expr) => {{
        assert_count_fails!($input_a, $operation<Boolean = $boolean, Output = $output>, $case)
    }};

    ////////////
    // Custom //
    ////////////

    // Empty case (special & custom): Sets a Boolean associated type.
    ($operation:tt<$boolean:ident>() => $output:ident<$($parameter:ident),+>, $case:expr) => {{
        assert_count_fails!($output<$($parameter),+>, $operation<Boolean = $boolean>, $case)
    }};
    // Unary case (custom).
    ($operation:tt($input:ident<$($parameter_a:ident),+>) => $output:ident<$($parameter_b:ident),+>, $case:expr) => {{
        assert_count_fails!($input<$($parameter_a),+>, $operation<Output = $output<$($parameter_b),+>>, $case)
    }};
    // Binary case (custom)
    ($operation:tt($input_a:ident<$($parameter_a:ident),+>, $input_b:ident<$($parameter_b:ident),+>) => $output:ident, $case:expr) => {{
        assert_count_fails!($input_a<$($parameter_a),+>, $operation<$input_b<$($parameter_b),+>, Output = $output>, $case)
    }};
    // Binary case (custom)
    ($operation:tt($input_a:ident<$($parameter_a:ident),+>, $input_b:ident<$($parameter_b:ident),+>) => $output:ident<$($parameter_c:ident),+>, $case:expr) => {{
        assert_count_fails!($input_a<$($parameter_a),+>, $operation<$input_b<$($parameter_b),+>, Output = $output<$($parameter_c),+>>, $case)
    }};
    // Ternary case (special & custom): Hardcoded for a conditional ternary operator.
    // Note: $input_b is not used, as the Ternary trait does not require one.
    ($operation:tt($boolean:ident, $input_a:ident<$($parameter_a:ident),+>, $input_b:ident<$($parameter_b:ident),+>) => $output:ident<$($parameter_c:ident),+>, $case:expr) => {{
        assert_count_fails!($input_a<$($parameter_a),+>, $operation<Boolean = $boolean, Output = $output<$($parameter_c),+>>, $case)
    }};
}

/// Asserts the output mode for a given operation and case.
///
/// ## Example
/// ```ignore
/// assert_output_mode!(candidate, Add(Field, Field) => Field, &(mode_a, mode_b))
/// ```
#[macro_export]
macro_rules! assert_output_mode {
    ($type_:ty, $operation:path, $case:expr, $candidate:expr) => {{
        let expected_mode = output_mode!($type_, $operation, $case);
        assert_eq!(expected_mode, $candidate.eject_mode());
    }};

    //////////////
    // Standard //
    //////////////

    // Special case: FromBoolean trait deviates from the normal convention.
    (FromBoolean($input:ident) => $output:ident, $case:expr, $candidate:expr) => {{
        assert_output_mode!($output, FromBoolean<Boolean = $input>, $case, $candidate)
    }};
    // Empty case (special): Sets a Boolean associated type.
    ($operation:tt<$boolean:ident>() => $output:ident, $case:expr, $candidate:expr) => {{
        assert_output_mode!($output, $operation<Boolean = $boolean>, $case, $candidate)
    }};
    // Unary case
    ($operation:tt($input:ident) => $output:ident, $case:expr, $candidate:expr) => {{
        assert_output_mode!($input, $operation<Output = $output>, $case, $candidate)
    }};
    // Binary case
    ($operation:tt($input_a:ident, $input_b:ident) => $output:ident, $case:expr, $candidate:expr) => {{
        assert_output_mode!($input_a, $operation<$input_b, Output = $output>, $case, $candidate)
    }};
    // Ternary case (special): Hardcoded for a conditional ternary operator.
    // Note: $input_b is not used, as the Ternary trait does not require one.
    ($operation:tt($boolean:ident, $input_a:ident, $input_b:ident) => $output:ident, $case:expr, $candidate:expr) => {{
        assert_output_mode!($input_a, $operation<Boolean = $boolean, Output = $output>, $case, $candidate)
    }};

    ////////////
    // Custom //
    ////////////

    // Empty case (special & custom): Sets a Boolean associated type.
    ($operation:tt<$boolean:ident>() => $output:ident<$($parameter:ident),+>, $case:expr, $candidate:expr) => {{
        assert_output_mode!($output<$($parameter),+>, $operation<Boolean = $boolean>, $case, $candidate)
    }};
    // Unary case (custom).
    ($operation:tt($input:ident<$($parameter_a:ident),+>) => $output:ident<$($parameter_b:ident),+>, $case:expr, $candidate:expr) => {{
        assert_output_mode!($input<$($parameter_a),+>, $operation<Output = $output<$($parameter_b),+>>, $case, $candidate)
    }};
    // Binary case (custom)
    ($operation:tt($input_a:ident<$($parameter_a:ident),+>, $input_b:ident<$($parameter_b:ident),+>) => $output:ident, $case:expr, $candidate:expr) => {{
        assert_output_mode!($input_a<$($parameter_a),+>, $operation<$input_b<$($parameter_b),+>, Output = $output>, $case, $candidate)
    }};
    // Binary case (custom)
    ($operation:tt($input_a:ident<$($parameter_a:ident),+>, $input_b:ident<$($parameter_b:ident),+>) => $output:ident<$($parameter_c:ident),+>, $case:expr, $candidate:expr) => {{
        assert_output_mode!($input_a<$($parameter_a),+>, $operation<$input_b<$($parameter_b),+>, Output = $output<$($parameter_c),+>>, $case, $candidate)
    }};
    // Ternary case (special & custom): Hardcoded for a conditional ternary operator.
    // Note: $input_b is not used, as the Ternary trait does not require one.
    ($operation:tt($boolean:ident, $input_a:ident<$($parameter_a:ident),+>, $input_b:ident<$($parameter_b:ident),+>) => $output:ident<$($parameter_c:ident),+>, $case:expr, $candidate:expr) => {{
        assert_output_mode!($input_a<$($parameter_a),+>, $operation<Boolean = $boolean, Output = $output<$($parameter_c),+>>, $case, $candidate)
    }};
}
