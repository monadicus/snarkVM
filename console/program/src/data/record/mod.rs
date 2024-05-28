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

mod entry;
pub use entry::Entry;

mod helpers;
pub use helpers::Owner;

mod bytes;
mod decrypt;
mod encrypt;
mod equal;
mod find;
mod is_owner;
mod num_randomizers;
mod parse_ciphertext;
mod parse_plaintext;
mod serial_number;
mod serialize;
mod tag;
mod to_bits;
mod to_commitment;
mod to_fields;

use crate::{Access, Ciphertext, Identifier, Literal, Plaintext, ProgramID};
use snarkvm_console_account::{Address, PrivateKey, ViewKey};
use snarkvm_console_network::prelude::*;
use snarkvm_console_types::{Boolean, Field, Group, Scalar};

use indexmap::IndexMap;

/// A value stored in program record.
#[derive(Clone)]
pub struct Record<Private: Visibility> {
    /// The owner of the program record.
    owner: Owner<Private>,
    /// The program data.
    data: IndexMap<Identifier, Entry<Private>>,
    /// The nonce of the program record.
    nonce: Group,
}

impl<Private: Visibility> Record<Private> {
    /// Initializes a new record plaintext.
    pub fn from_plaintext(
        owner: Owner<Plaintext>,
        data: IndexMap<Identifier, Entry<Plaintext>>,
        nonce: Group,
    ) -> Result<Record<Plaintext>> {
        let reserved = [Identifier::from_str("owner")?];
        // Ensure the members has no duplicate names.
        ensure!(!has_duplicates(data.keys().chain(reserved.iter())), "Found a duplicate entry name in a record");
        // Ensure the number of entries is within the maximum limit.
        ensure!(data.len() <= AleoNetwork::MAX_DATA_ENTRIES, "Found a record that exceeds size ({})", data.len());
        // Return the record.
        Ok(Record { owner, data, nonce })
    }

    /// Initializes a new record ciphertext.
    pub fn from_ciphertext(
        owner: Owner<Ciphertext>,
        data: IndexMap<Identifier, Entry<Ciphertext>>,
        nonce: Group,
    ) -> Result<Record<Ciphertext>> {
        let reserved = [Identifier::from_str("owner")?];
        // Ensure the members has no duplicate names.
        ensure!(!has_duplicates(data.keys().chain(reserved.iter())), "Found a duplicate entry name in a record");
        // Ensure the number of entries is within the maximum limit.
        ensure!(data.len() <= AleoNetwork::MAX_DATA_ENTRIES, "Found a record that exceeds size ({})", data.len());
        // Return the record.
        Ok(Record { owner, data, nonce })
    }
}

impl<Private: Visibility> Record<Private> {
    /// Returns the owner of the program record.
    pub const fn owner(&self) -> &Owner<Private> {
        &self.owner
    }

    /// Returns the program data.
    pub const fn data(&self) -> &IndexMap<Identifier, Entry<Private>> {
        &self.data
    }

    /// Returns the nonce of the program record.
    pub const fn nonce(&self) -> &Group {
        &self.nonce
    }
}

impl<Private: Visibility> Record<Private> {
    /// Returns the owner of the program record, and consumes `self`.
    pub fn into_owner(self) -> Owner<Private> {
        self.owner
    }

    /// Returns the program data, and consumes `self`.
    pub fn into_data(self) -> IndexMap<Identifier, Entry<Private>> {
        self.data
    }

    /// Returns the nonce of the program record, and consumes `self`.
    pub fn into_nonce(self) -> Group {
        self.nonce
    }
}
