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

impl Parser for Literal {
    /// Parses a string into a literal.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        alt((
            map(Address::parse, Self::Address),
            map(Boolean::parse, Self::Boolean),
            map(Field::parse, Self::Field),
            map(Group::parse, Self::Group),
            map(I8::parse, Self::I8),
            map(I16::parse, Self::I16),
            map(I32::parse, Self::I32),
            map(I64::parse, Self::I64),
            map(I128::parse, Self::I128),
            map(U8::parse, Self::U8),
            map(U16::parse, Self::U16),
            map(U32::parse, Self::U32),
            map(U64::parse, Self::U64),
            map(U128::parse, Self::U128),
            map(Scalar::parse, Self::Scalar),
            map(Signature::parse, |literal| Self::Signature(Box::new(literal))),
            map(StringType::parse, Self::String),
            // This allows users to implicitly declare program IDs as literals.
            map_res(ProgramID::parse, |program_id| Ok::<Self, Error>(Self::Address(program_id.to_address()?))),
        ))(string)
    }
}

impl FromStr for Literal {
    type Err = Error;

    /// Parses a string into a literal.
    #[inline]
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

impl Debug for Literal {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Address(literal) => Display::fmt(literal, f),
            Self::Boolean(literal) => Display::fmt(literal, f),
            Self::Field(literal) => Display::fmt(literal, f),
            Self::Group(literal) => Display::fmt(literal, f),
            Self::I8(literal) => Display::fmt(literal, f),
            Self::I16(literal) => Display::fmt(literal, f),
            Self::I32(literal) => Display::fmt(literal, f),
            Self::I64(literal) => Display::fmt(literal, f),
            Self::I128(literal) => Display::fmt(literal, f),
            Self::U8(literal) => Display::fmt(literal, f),
            Self::U16(literal) => Display::fmt(literal, f),
            Self::U32(literal) => Display::fmt(literal, f),
            Self::U64(literal) => Display::fmt(literal, f),
            Self::U128(literal) => Display::fmt(literal, f),
            Self::Scalar(literal) => Display::fmt(literal, f),
            Self::Signature(literal) => Display::fmt(literal, f),
            Self::String(literal) => Display::fmt(literal, f),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_program_id() -> Result<()> {
        let (remainder, candidate) = Literal::parse("credits.aleo")?;
        assert!(matches!(candidate, Literal::Address(_)));
        assert_eq!(candidate.to_string(), "aleo1lqmly7ez2k48ajf5hs92ulphaqr05qm4n8qwzj8v0yprmasgpqgsez59gg");
        assert_eq!("", remainder);

        let result = Literal::parse("credits.ale");
        assert!(result.is_err());

        let result = Literal::parse("credits.aleo1");
        assert!(result.is_err());

        Ok(())
    }
}
