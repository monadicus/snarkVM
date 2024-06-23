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

impl Parser for ValueType {
    /// Parses the string into a value type.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the mode from the string.
        // Note that the order of the parsers matters.
        alt((
            map(pair(PlaintextType::parse, tag(".constant")), |(plaintext_type, _)| Self::Constant(plaintext_type)),
            map(pair(PlaintextType::parse, tag(".public")), |(plaintext_type, _)| Self::Public(plaintext_type)),
            map(pair(PlaintextType::parse, tag(".private")), |(plaintext_type, _)| Self::Private(plaintext_type)),
            map(pair(Identifier::parse, tag(".record")), |(identifier, _)| Self::Record(identifier)),
            map(pair(Locator::parse, tag(".record")), |(locator, _)| Self::ExternalRecord(locator)),
            map(pair(Locator::parse, tag(".future")), |(locator, _)| Self::Future(locator)),
        ))(string)
    }
}

impl FromStr for ValueType {
    type Err = Error;

    /// Returns the value type from a string literal.
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

impl Debug for ValueType {
    /// Prints the value type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for ValueType {
    /// Prints the value type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Constant(plaintext_type) => write!(f, "{plaintext_type}.constant"),
            Self::Public(plaintext_type) => write!(f, "{plaintext_type}.public"),
            Self::Private(plaintext_type) => write!(f, "{plaintext_type}.private"),
            Self::Record(identifier) => write!(f, "{identifier}.record"),
            Self::ExternalRecord(locator) => write!(f, "{locator}.record"),
            Self::Future(locator) => write!(f, "{locator}.future"),
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
        // Literal type.
        assert_eq!(Ok(("", ValueType::from_str("field.constant")?)), ValueType::parse("field.constant"));
        assert_eq!(Ok(("", ValueType::from_str("field.public")?)), ValueType::parse("field.public"));
        assert_eq!(Ok(("", ValueType::from_str("field.private")?)), ValueType::parse("field.private"));

        // Struct type.
        assert_eq!(Ok(("", ValueType::from_str("signature.constant")?)), ValueType::parse("signature.constant"));
        assert_eq!(Ok(("", ValueType::from_str("signature.public")?)), ValueType::parse("signature.public"));
        assert_eq!(Ok(("", ValueType::from_str("signature.private")?)), ValueType::parse("signature.private"));
        assert_eq!(Ok(("", ValueType::from_str("i8abc.constant")?)), ValueType::parse("i8abc.constant"));

        // Record type.
        assert_eq!(Ok(("", ValueType::from_str("token.record")?)), ValueType::parse("token.record"));
        assert_eq!(ValueType::Record(Identifier::from_str("message")?), ValueType::parse("message.record")?.1);

        // ExternalRecord type.
        assert_eq!(
            Ok(("", ValueType::from_str("howard.aleo/message.record")?)),
            ValueType::parse("howard.aleo/message.record")
        );
        assert_eq!(
            ValueType::ExternalRecord(Locator::from_str("howard.aleo/message")?),
            ValueType::parse("howard.aleo/message.record")?.1
        );

        // Future type.
        assert_eq!(
            Ok(("", ValueType::from_str("credits.aleo/mint_public.future")?)),
            ValueType::parse("credits.aleo/mint_public.future")
        );
        assert_eq!(
            ValueType::Future(Locator::from_str("credits.aleo/mint_public")?),
            ValueType::parse("credits.aleo/mint_public.future")?.1
        );

        Ok(())
    }

    #[test]
    fn test_parse_fails() -> Result<()> {
        // Literal type must contain visibility.
        assert!(ValueType::parse("field").is_err());
        // Struct type must contain visibility.
        assert!(ValueType::parse("signature").is_err());
        // Record type must contain record keyword.
        assert!(ValueType::parse("token").is_err());

        // Must be non-empty.
        assert!(ValueType::parse("").is_err());

        // Invalid characters.
        assert!(ValueType::parse("{}").is_err());
        assert!(ValueType::parse("_").is_err());
        assert!(ValueType::parse("__").is_err());
        assert!(ValueType::parse("___").is_err());
        assert!(ValueType::parse("-").is_err());
        assert!(ValueType::parse("--").is_err());
        assert!(ValueType::parse("---").is_err());
        assert!(ValueType::parse("*").is_err());
        assert!(ValueType::parse("**").is_err());
        assert!(ValueType::parse("***").is_err());

        // Must not start with a number.
        assert!(ValueType::parse("1").is_err());
        assert!(ValueType::parse("2").is_err());
        assert!(ValueType::parse("3").is_err());
        assert!(ValueType::parse("1foo").is_err());
        assert!(ValueType::parse("12").is_err());
        assert!(ValueType::parse("111").is_err());

        // Must fit within the data capacity of a base field element.
        let struct_ = ValueType::parse("foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy.private");
        assert!(struct_.is_err());

        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        assert_eq!(ValueType::from_str("field.constant")?.to_string(), "field.constant");
        assert_eq!(ValueType::from_str("field.public")?.to_string(), "field.public");
        assert_eq!(ValueType::from_str("field.private")?.to_string(), "field.private");

        assert_eq!(ValueType::from_str("signature.constant")?.to_string(), "signature.constant");
        assert_eq!(ValueType::from_str("signature.public")?.to_string(), "signature.public");
        assert_eq!(ValueType::from_str("signature.private")?.to_string(), "signature.private");

        assert_eq!(ValueType::from_str("token.record")?.to_string(), "token.record");

        assert_eq!(ValueType::from_str("howard.aleo/message.record")?.to_string(), "howard.aleo/message.record");

        Ok(())
    }
}
