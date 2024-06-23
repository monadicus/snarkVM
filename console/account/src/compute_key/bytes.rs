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

impl FromBytes for ComputeKey {
    /// Reads an account compute key from a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let pk_sig = Group::from_x_coordinate(Field::new(ConsoleField::read_le(&mut reader)?))
            .map_err(|e| error(format!("{e}")))?;
        let pr_sig = Group::from_x_coordinate(Field::new(ConsoleField::read_le(&mut reader)?))
            .map_err(|e| error(format!("{e}")))?;
        Self::try_from((pk_sig, pr_sig)).map_err(|e| error(format!("{e}")))
    }
}

impl ToBytes for ComputeKey {
    /// Writes an account compute key to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.pk_sig.to_x_coordinate().write_le(&mut writer)?;
        self.pr_sig.to_x_coordinate().write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ITERATIONS: u64 = 1000;

    #[test]
    fn test_bytes() -> Result<()> {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a new compute key.
            let private_key = PrivateKey::new(&mut rng)?;
            let expected = ComputeKey::try_from(private_key)?;

            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le()?;
            assert_eq!(expected, ComputeKey::read_le(&expected_bytes[..])?);
            assert!(ComputeKey::read_le(&expected_bytes[1..]).is_err());
        }
        Ok(())
    }
}
