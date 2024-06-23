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

impl FromBytes for Field {
    /// Reads the field from a buffer.
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self::new(FromBytes::read_le(&mut reader)?))
    }
}

impl ToBytes for Field {
    /// Writes the field to a buffer.
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.field.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ITERATIONS: u64 = 10_000;

    #[test]
    fn test_bytes() -> Result<()> {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a new field.
            let expected = Field::new(Uniform::rand(&mut rng));

            // Check the byte representation.
            let expected_bytes = expected.to_bytes_le()?;
            assert_eq!(expected, Field::read_le(&expected_bytes[..])?);
            assert!(Field::read_le(&expected_bytes[1..]).is_err());
        }
        Ok(())
    }
}
