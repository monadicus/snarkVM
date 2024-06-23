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

mod decrypt;
mod equal;
mod from_bits;
mod from_fields;
mod num_randomizers;
mod size_in_fields;
mod to_bits;
mod to_fields;

use crate::{Plaintext, Visibility};
use snarkvm_circuit_network::{Aleo, AleoV0};
use snarkvm_circuit_types::{
    environment::{prelude::*, Circuit},
    Boolean,
    Field,
};

use core::ops::Deref;

#[derive(Clone)]
pub struct Ciphertext(Vec<Field>);

#[cfg(console)]
impl Inject for Ciphertext {
    type Primitive = console::Ciphertext;

    /// Initializes a new ciphertext circuit from a primitive.
    fn new(mode: Mode, ciphertext: Self::Primitive) -> Self {
        // Ensure the number of field elements does not exceed the maximum allowed size.
        match (*ciphertext).len() <= AleoV0::MAX_DATA_SIZE_IN_FIELDS as usize {
            true => Self(Inject::new(mode, (*ciphertext).to_vec())),
            false => Circuit::halt("Ciphertext exceeds maximum allowed size"),
        }
    }
}

#[cfg(console)]
impl Eject for Ciphertext {
    type Primitive = console::Ciphertext;

    /// Ejects the mode of the ciphertext.
    fn eject_mode(&self) -> Mode {
        self.0.eject_mode()
    }

    /// Ejects the ciphertext.
    fn eject_value(&self) -> Self::Primitive {
        match console::FromFields::from_fields(&self.0.eject_value()) {
            Ok(ciphertext) => ciphertext,
            Err(error) => Circuit::halt(format!("Failed to eject ciphertext: {error}")),
        }
    }
}

impl Deref for Ciphertext {
    type Target = [Field];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
