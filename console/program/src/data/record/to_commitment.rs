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

impl Record<Plaintext> {
    /// Returns the record commitment.
    pub fn to_commitment(&self, program_id: &ProgramID, record_name: &Identifier) -> Result<Field> {
        // Construct the input as `(program_id || record_name || record)`.
        let input = to_bits_le![program_id, record_name, self];
        // Compute the BHP hash of the program record.
        AleoNetwork::hash_bhp1024(&input)
    }
}

impl Record<Ciphertext> {
    /// Returns the record commitment.
    pub fn to_commitment(&self, _program_id: &ProgramID, _record_name: &Identifier) -> Result<Field> {
        bail!("Illegal operation: Record::to_commitment() cannot be invoked on the `Ciphertext` variant.")
    }
}
