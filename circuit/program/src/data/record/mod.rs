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

#[cfg(test)]
use snarkvm_circuit_types::environment::assert_scope;

mod entry;
pub use entry::Entry;

mod helpers;
pub use helpers::Owner;

mod decrypt;
mod encrypt;
mod equal;
mod find;
mod num_randomizers;
mod serial_number;
mod tag;
mod to_bits;
mod to_commitment;
mod to_fields;

use crate::{Access, Ciphertext, Identifier, Plaintext, ProgramID, Visibility};
use snarkvm_circuit_account::{PrivateKey, ViewKey};
use snarkvm_circuit_network::Aleo;
use snarkvm_circuit_types::{
    environment::{prelude::*, Circuit},
    Boolean,
    Field,
    Group,
    Scalar,
    U32,
};

#[derive(Clone)]
pub struct Record<Private: Visibility> {
    /// The owner of the program record.
    owner: Owner<Private>,
    /// The program data.
    data: IndexMap<Identifier, Entry<Private>>,
    /// The nonce of the program record.
    nonce: Group,
}

#[cfg(console)]
impl Inject for Record<Plaintext> {
    type Primitive = console::Record<console::Plaintext>;

    /// Initializes a plaintext record from a primitive.
    fn new(_: Mode, record: Self::Primitive) -> Self {
        Self {
            owner: Owner::new(Mode::Private, record.owner().clone()),
            data: Inject::new(Mode::Private, record.data().clone()),
            nonce: Group::new(Mode::Private, *record.nonce()),
        }
    }
}

#[cfg(console)]
impl Inject for Record<Ciphertext> {
    type Primitive = console::Record<console::Ciphertext>;

    /// Initializes a ciphertext record from a primitive.
    fn new(_: Mode, record: Self::Primitive) -> Self {
        Self {
            owner: Owner::new(Mode::Private, record.owner().clone()),
            data: Inject::new(Mode::Private, record.data().clone()),
            nonce: Group::new(Mode::Private, *record.nonce()),
        }
    }
}

#[cfg(console)]
impl<Private: Visibility> Record<Private> {
    /// Initializes a new record plaintext.
    pub fn from_plaintext(
        owner: Owner<Plaintext>,
        data: IndexMap<Identifier, Entry<Plaintext>>,
        nonce: Group,
    ) -> Result<Record<Plaintext>> {
        // Ensure the members has no duplicate names.
        ensure!(!has_duplicates(data.iter().map(|(name, ..)| name)), "A duplicate entry name was found in a record");
        // Ensure the number of entries is within the maximum limit.
        ensure!(
            data.len() <= console::AleoNetwork::MAX_DATA_ENTRIES,
            "Found a record that exceeds size ({})",
            data.len()
        );
        // Return the record.
        Ok(Record { owner, data, nonce })
    }

    /// Initializes a new record ciphertext.
    pub fn from_ciphertext(
        owner: Owner<Ciphertext>,
        data: IndexMap<Identifier, Entry<Ciphertext>>,
        nonce: Group,
    ) -> Result<Record<Ciphertext>> {
        // Ensure the members has no duplicate names.
        ensure!(!has_duplicates(data.iter().map(|(name, ..)| name)), "A duplicate entry name was found in a record");
        // Ensure the number of entries is within the maximum limit.
        ensure!(
            data.len() <= console::AleoNetwork::MAX_DATA_ENTRIES,
            "Found a record that exceeds size ({})",
            data.len()
        );
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

#[cfg(console)]
impl Eject for Record<Plaintext> {
    type Primitive = console::Record<console::Plaintext>;

    /// Ejects the mode of the record.
    fn eject_mode(&self) -> Mode {
        let owner = match &self.owner {
            Owner::Public(owner) => match owner.eject_mode() == Mode::Public {
                true => Mode::Public,
                false => Circuit::halt("Record::<Plaintext>::eject_mode: 'owner' is not public."),
            },
            Owner::Private(plaintext) => match plaintext.eject_mode() == Mode::Private {
                true => Mode::Private,
                false => Circuit::halt("Record::<Plaintext>::eject_mode: 'owner' is not private."),
            },
        };

        let data = self.data.iter().map(|(_, entry)| entry.eject_mode()).collect::<Vec<_>>().eject_mode();
        let nonce = self.nonce.eject_mode();

        Mode::combine(owner, [data, nonce])
    }

    /// Ejects the record.
    fn eject_value(&self) -> Self::Primitive {
        let owner = match &self.owner {
            Owner::Public(owner) => console::Owner::Public(owner.eject_value()),
            Owner::Private(plaintext) => console::Owner::Private(plaintext.eject_value()),
        };

        match Self::Primitive::from_plaintext(
            owner,
            self.data.iter().map(|(identifier, entry)| (identifier, entry).eject_value()).collect::<IndexMap<_, _>>(),
            self.nonce.eject_value(),
        ) {
            Ok(record) => record,
            Err(error) => Circuit::halt(format!("Record::<Plaintext>::eject_value: {error}")),
        }
    }
}

#[cfg(console)]
impl Eject for Record<Ciphertext> {
    type Primitive = console::Record<console::Ciphertext>;

    /// Ejects the mode of the record.
    fn eject_mode(&self) -> Mode {
        let owner = match &self.owner {
            Owner::Public(owner) => match owner.eject_mode() == Mode::Public {
                true => Mode::Public,
                false => Circuit::halt("Record::<Ciphertext>::eject_mode: 'owner' is not public."),
            },
            Owner::Private(plaintext) => match plaintext.eject_mode() == Mode::Private {
                true => Mode::Private,
                false => Circuit::halt("Record::<Ciphertext>::eject_mode: 'owner' is not private."),
            },
        };

        let data = self.data.iter().map(|(_, entry)| entry.eject_mode()).collect::<Vec<_>>().eject_mode();
        let nonce = self.nonce.eject_mode();

        Mode::combine(owner, [data, nonce])
    }

    /// Ejects the record.
    fn eject_value(&self) -> Self::Primitive {
        let owner = match &self.owner {
            Owner::Public(owner) => console::Owner::Public(owner.eject_value()),
            Owner::Private(plaintext) => console::Owner::Private(plaintext.eject_value()),
        };

        match Self::Primitive::from_ciphertext(
            owner,
            self.data.iter().map(|(identifier, entry)| (identifier, entry).eject_value()).collect::<IndexMap<_, _>>(),
            self.nonce.eject_value(),
        ) {
            Ok(record) => record,
            Err(error) => Circuit::halt(format!("Record::<Ciphertext>::eject_value: {error}")),
        }
    }
}

#[cfg(console)]
impl<Private: Visibility> TypeName for Record<Private> {
    fn type_name() -> &'static str {
        "record"
    }
}
