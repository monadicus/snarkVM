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

#[cfg(feature = "view_key")]
impl TryFrom<ViewKey> for GraphKey {
    type Error = Error;

    /// Derives the account graph key from an account view key.
    fn try_from(view_key: ViewKey) -> Result<Self, Self::Error> {
        Self::try_from(&view_key)
    }
}

#[cfg(feature = "view_key")]
impl TryFrom<&ViewKey> for GraphKey {
    type Error = Error;

    /// Derives the account graph key from an account view key.
    fn try_from(view_key: &ViewKey) -> Result<Self, Self::Error> {
        // Compute sk_tag := Hash(view_key || ctr).
        let sk_tag = AleoNetwork::hash_psd4(&[AleoNetwork::graph_key_domain(), view_key.to_field()?, Field::zero()])?;
        // Output the graph key.
        Self::try_from(sk_tag)
    }
}

impl TryFrom<Field> for GraphKey {
    type Error = Error;

    /// Derives the account graph key from `sk_tag`.
    fn try_from(sk_tag: Field) -> Result<Self> {
        // Output the graph key.
        Ok(Self { sk_tag })
    }
}

impl TryFrom<&Field> for GraphKey {
    type Error = Error;

    /// Derives the account graph key from `sk_tag`.
    fn try_from(sk_tag: &Field) -> Result<Self> {
        Self::try_from(*sk_tag)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PrivateKey;

    const ITERATIONS: u64 = 1000;

    #[test]
    fn test_try_from() -> Result<()> {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a new graph key.
            let private_key = PrivateKey::new(&mut rng)?;
            let view_key = ViewKey::try_from(private_key)?;
            let candidate = GraphKey::try_from(view_key)?;

            // Check that graph key is derived correctly from `sk_tag`.
            assert_eq!(candidate, GraphKey::try_from(candidate.sk_tag())?);
        }
        Ok(())
    }
}
