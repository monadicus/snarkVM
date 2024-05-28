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

use snarkvm_utilities::DeserializeExt;

impl Serialize for ProgramOwner {
    /// Serializes the program owner into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => {
                let mut owner = serializer.serialize_struct("ProgramOwner", 2)?;
                owner.serialize_field("address", &self.address)?;
                owner.serialize_field("signature", &self.signature)?;
                owner.end()
            }
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de> Deserialize<'de> for ProgramOwner {
    /// Deserializes the owner from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => {
                // Parse the program owner from a string into a value.
                let mut owner = serde_json::Value::deserialize(deserializer)?;

                // Recover the program owner.
                let owner = Self::from(
                    // Retrieve the address.
                    DeserializeExt::take_from_value::<D>(&mut owner, "address")?,
                    // Retrieve the signature.
                    DeserializeExt::take_from_value::<D>(&mut owner, "signature")?,
                );

                Ok(owner)
            }
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "program owner"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serde_json() -> Result<()> {
        // Sample the program owner.
        let expected = test_helpers::sample_program_owner();

        // Serialize
        let expected_string = &expected.to_string();
        let candidate_string = serde_json::to_string(&expected)?;
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        // Deserialize
        assert_eq!(expected, ProgramOwner::from_str(expected_string)?);
        assert_eq!(expected, serde_json::from_str(&candidate_string)?);

        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        // Sample the program owner.
        let expected = test_helpers::sample_program_owner();

        // Serialize
        let expected_bytes = expected.to_bytes_le()?;
        let expected_bytes_with_size_encoding = bincode::serialize(&expected)?;
        assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

        // Deserialize
        assert_eq!(expected, ProgramOwner::read_le(&expected_bytes[..])?);
        assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..])?);

        Ok(())
    }
}
