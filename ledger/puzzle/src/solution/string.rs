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

impl FromStr for Solution {
    type Err = Error;

    /// Initializes the solution from a JSON-string.
    fn from_str(solution: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(solution)?)
    }
}

impl Debug for Solution {
    /// Prints the solution as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Display for Solution {
    /// Displays the solution as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(ser::Error::custom)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::account::PrivateKey;

    #[test]
    fn test_string() -> Result<()> {
        let mut rng = TestRng::default();
        let private_key = PrivateKey::new(&mut rng)?;
        let address = Address::try_from(private_key)?;

        // Sample a new solution.
        let partial_solution = PartialSolution::new(rng.gen(), address, u64::rand(&mut rng)).unwrap();
        let target = u64::rand(&mut rng);
        let expected = Solution::new(partial_solution, target);

        // Check the string representation.
        let candidate = expected.to_string();
        assert_eq!(expected, Solution::from_str(&candidate)?);

        Ok(())
    }
}
