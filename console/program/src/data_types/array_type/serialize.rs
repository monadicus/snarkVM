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

impl Serialize for ArrayType {
    /// Serializes the array type into string or bytes.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match serializer.is_human_readable() {
            true => serializer.collect_str(self),
            false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        }
    }
}

impl<'de> Deserialize<'de> for ArrayType {
    /// Deserializes the array type from a string or bytes.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match deserializer.is_human_readable() {
            true => FromStr::from_str(&String::deserialize(deserializer)?).map_err(de::Error::custom),
            false => FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "array type"),
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use snarkvm_console_network::MainnetV0;

    /// Add test cases here to be checked for serialization.
    pub(crate) const TEST_CASES: &[&str] = &[
        "[boolean; 31u32]",
        "[field; 32u32]",
        "[group; 32u32]",
        "[scalar; 32u32]",
        "[u8; 1u32]",
        "[u16; 1u32]",
        "[u32; 1u32]",
        "[u64; 1u32]",
        "[u128; 1u32]",
        "[i8; 1u32]",
        "[i16; 1u32]",
        "[i32; 1u32]",
        "[i64; 1u32]",
        "[i128; 1u32]",
        "[signature; 1u32]",
        "[foo; 4u32]",
        "[bar; 4u32]",
        "[[u8; 1u32]; 2u32]",
        "[[[u8; 1u32]; 2u32]; 3u32]",
        "[[[[u8; 1u32]; 2u32]; 3u32]; 4u32]",
        "[[[[[u8; 1u32]; 2u32]; 3u32]; 4u32]; 5u32]",
        "[[[[[[u8; 1u32]; 2u32]; 3u32]; 4u32]; 5u32]; 6u32]",
        "[[[[[[[u8; 1u32]; 2u32]; 3u32]; 4u32]; 5u32]; 6u32]; 7u32]",
        "[[[[[[[[u8; 1u32]; 2u32]; 3u32]; 4u32]; 5u32]; 6u32]; 7u32]; 8u32]",
    ];

    fn check_serde_json<
        T: Serialize + for<'a> Deserialize<'a> + Debug + Display + PartialEq + Eq + FromStr + ToBytes + FromBytes,
    >(
        expected: T,
    ) {
        // Serialize
        let expected_string = &expected.to_string();
        let candidate_string = serde_json::to_string(&expected).unwrap();
        assert_eq!(expected_string, serde_json::Value::from_str(&candidate_string).unwrap().as_str().unwrap());

        // Deserialize
        assert_eq!(expected, T::from_str(expected_string).unwrap_or_else(|_| panic!("FromStr: {expected_string}")));
        assert_eq!(expected, serde_json::from_str(&candidate_string).unwrap());
    }

    fn check_bincode<
        T: Serialize + for<'a> Deserialize<'a> + Debug + Display + PartialEq + Eq + FromStr + ToBytes + FromBytes,
    >(
        expected: T,
    ) {
        // Serialize
        let expected_bytes = expected.to_bytes_le().unwrap();
        let expected_bytes_with_size_encoding = bincode::serialize(&expected).unwrap();
        assert_eq!(&expected_bytes[..], &expected_bytes_with_size_encoding[8..]);

        // Deserialize
        assert_eq!(expected, T::read_le(&expected_bytes[..]).unwrap());
        assert_eq!(expected, bincode::deserialize(&expected_bytes_with_size_encoding[..]).unwrap());
    }

    #[test]
    fn test_serde_json() {
        for case in TEST_CASES.iter() {
            check_serde_json(ArrayType::<MainnetV0>::from_str(case).unwrap());
        }
    }

    #[test]
    fn test_bincode() {
        for case in TEST_CASES.iter() {
            check_bincode(ArrayType::<MainnetV0>::from_str(case).unwrap());
        }
    }
}
