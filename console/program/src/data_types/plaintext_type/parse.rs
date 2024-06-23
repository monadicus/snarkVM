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

impl Parser for PlaintextType {
    /// Parses a string into a plaintext type.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse to determine the plaintext type (order matters).
        alt((
            map(ArrayType::parse, Self::Array),
            map(Identifier::parse, Self::Struct),
            map(LiteralType::parse, Self::Literal),
        ))(string)
    }
}

impl FromStr for PlaintextType {
    type Err = Error;

    /// Returns a plaintext type from a string literal.
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl Debug for PlaintextType {
    /// Prints the plaintext type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for PlaintextType {
    /// Prints the plaintext type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            // Prints the literal, i.e. field
            Self::Literal(literal) => Display::fmt(literal, f),
            // Prints the struct, i.e. signature
            Self::Struct(struct_) => Display::fmt(struct_, f),
            // Prints the array type, i.e. [field; 2u32]
            Self::Array(array) => Display::fmt(array, f),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::MainnetV0;

    type CurrentNetwork = MainnetV0;

    #[test]
    fn test_parse() -> Result<()> {
        assert_eq!(PlaintextType::parse("field"), Ok(("", PlaintextType::Literal(LiteralType::Field))));
        assert_eq!(PlaintextType::parse("signature"), Ok(("", PlaintextType::Literal(LiteralType::Signature))));
        assert_eq!(PlaintextType::parse("foo"), Ok(("", PlaintextType::Struct(Identifier::from_str("foo")?))));
        assert_eq!(
            PlaintextType::parse("u8jdsklaj"),
            Ok(("", PlaintextType::Struct(Identifier::from_str("u8jdsklaj")?)))
        );
        assert_eq!(
            PlaintextType::parse("[field; 1u32]"),
            Ok(("", PlaintextType::Array(ArrayType::from_str("[field; 1u32]")?)))
        );
        Ok(())
    }

    #[test]
    fn test_parse_fails() -> Result<()> {
        // Literal type must not contain visibility.
        assert_eq!(Ok((".constant", PlaintextType::from_str("field")?)), PlaintextType::parse("field.constant"));
        assert_eq!(Ok((".public", PlaintextType::from_str("field")?)), PlaintextType::parse("field.public"));
        assert_eq!(Ok((".private", PlaintextType::from_str("field")?)), PlaintextType::parse("field.private"));

        // Struct type must not contain visibility.
        assert_eq!(Ok((".constant", Identifier::from_str("foo")?)), Identifier::parse("foo.constant"));
        assert_eq!(Ok((".public", Identifier::from_str("foo")?)), Identifier::parse("foo.public"));
        assert_eq!(Ok((".private", Identifier::from_str("foo")?)), Identifier::parse("foo.private"));

        // Array type must not contain visibility.
        assert_eq!(
            Ok((".constant", PlaintextType::from_str("[field; 1u32]")?)),
            PlaintextType::parse("[field; 1u32].constant")
        );
        assert_eq!(
            Ok((".public", PlaintextType::from_str("[field; 1u32]")?)),
            PlaintextType::parse("[field; 1u32].public")
        );
        assert_eq!(
            Ok((".private", PlaintextType::from_str("[field; 1u32]")?)),
            PlaintextType::parse("[field; 1u32].private")
        );

        // Must be non-empty.
        assert!(PlaintextType::parse("").is_err());
        assert!(PlaintextType::parse("{}").is_err());

        // Invalid characters.
        assert!(PlaintextType::parse("_").is_err());
        assert!(PlaintextType::parse("__").is_err());
        assert!(PlaintextType::parse("___").is_err());
        assert!(PlaintextType::parse("-").is_err());
        assert!(PlaintextType::parse("--").is_err());
        assert!(PlaintextType::parse("---").is_err());
        assert!(PlaintextType::parse("*").is_err());
        assert!(PlaintextType::parse("**").is_err());
        assert!(PlaintextType::parse("***").is_err());

        // Must not start with a number.
        assert!(PlaintextType::parse("1").is_err());
        assert!(PlaintextType::parse("2").is_err());
        assert!(PlaintextType::parse("3").is_err());
        assert!(PlaintextType::parse("1foo").is_err());
        assert!(PlaintextType::parse("12").is_err());
        assert!(PlaintextType::parse("111").is_err());

        // Struct types must fit within the data capacity of a base field element.
        let struct_ = PlaintextType::parse("foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy");
        assert!(struct_.is_err());

        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        assert_eq!(PlaintextType::Literal(LiteralType::Boolean).to_string(), "boolean");
        assert_eq!(PlaintextType::Literal(LiteralType::Field).to_string(), "field");
        assert_eq!(PlaintextType::Literal(LiteralType::Signature).to_string(), "signature");
        assert_eq!(PlaintextType::Struct(Identifier::from_str("foo")?).to_string(), "foo");
        assert_eq!(PlaintextType::Struct(Identifier::from_str("bar")?).to_string(), "bar");
        assert_eq!(PlaintextType::Array(ArrayType::from_str("[field; 8u32]")?).to_string(), "[field; 8u32]");
        Ok(())
    }
}
