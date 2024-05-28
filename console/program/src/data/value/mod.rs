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

mod bytes;
mod equal;
mod find;
mod parse;
mod serialize;
mod to_bits;
mod to_fields;

use crate::{Access, Argument, Entry, Future, Literal, Plaintext, Record};
use snarkvm_console_types::prelude::*;

#[derive(Clone)]
pub enum Value {
    /// A plaintext value.
    Plaintext(Plaintext),
    /// A record value.
    Record(Record<Plaintext>),
    /// A future.
    Future(Future),
}

impl From<Literal> for Value {
    /// Initializes the value from a literal.
    fn from(literal: Literal) -> Self {
        Self::Plaintext(Plaintext::from(literal))
    }
}

impl From<&Literal> for Value {
    /// Initializes the value from a literal.
    fn from(literal: &Literal) -> Self {
        Self::from(Plaintext::from(literal))
    }
}

impl From<Plaintext> for Value {
    /// Initializes the value from a plaintext.
    fn from(plaintext: Plaintext) -> Self {
        Self::Plaintext(plaintext)
    }
}

impl From<&Plaintext> for Value {
    /// Initializes the value from a plaintext.
    fn from(plaintext: &Plaintext) -> Self {
        Self::from(plaintext.clone())
    }
}

impl From<Record<Plaintext>> for Value {
    /// Initializes the value from a record.
    fn from(record: Record<Plaintext>) -> Self {
        Self::Record(record)
    }
}

impl From<&Record<Plaintext>> for Value {
    /// Initializes the value from a record.
    fn from(record: &Record<Plaintext>) -> Self {
        Self::from(record.clone())
    }
}

impl From<Future> for Value {
    /// Initializes the value from a future.
    fn from(future: Future) -> Self {
        Self::Future(future)
    }
}

impl From<&Future> for Value {
    /// Initializes the value from a future.
    fn from(future: &Future) -> Self {
        Self::from(future.clone())
    }
}

impl From<Argument> for Value {
    /// Initializes the value from an argument.
    fn from(argument: Argument) -> Self {
        match argument {
            Argument::Plaintext(plaintext) => Self::Plaintext(plaintext),
            Argument::Future(future) => Self::Future(future),
        }
    }
}

impl From<&Argument> for Value {
    /// Initializes the value from an argument.
    fn from(argument: &Argument) -> Self {
        Self::from(argument.clone())
    }
}

impl From<&Value> for Value {
    /// Returns a clone of the value.
    fn from(value: &Value) -> Self {
        value.clone()
    }
}

impl TryFrom<Result<Value>> for Value {
    type Error = Error;

    /// Initializes a value from a result.
    fn try_from(value: Result<Value>) -> Result<Self> {
        value
    }
}

impl TryFrom<String> for Value {
    type Error = Error;

    /// Initializes a value from a string.
    fn try_from(value: String) -> Result<Self> {
        Self::from_str(&value)
    }
}

impl TryFrom<&String> for Value {
    type Error = Error;

    /// Initializes a value from a string.
    fn try_from(value: &String) -> Result<Self> {
        Self::from_str(value)
    }
}

impl TryFrom<&str> for Value {
    type Error = Error;

    /// Initializes a value from a string.
    fn try_from(value: &str) -> Result<Self> {
        Self::from_str(value)
    }
}
