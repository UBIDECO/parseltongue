// Parseltongue: Framework for declarative domain-specific languages
//
// SPDX-License-Identifier: Apache-2.0
//
// Designed in 2021-2025 by Dr Maxim Orlovsky <orlovsky@ubideco.org>
// Written in 2024-2025 by Dr Maxim Orlovsky <orlovsky@ubideco.org>
//
// Copyright (C) 2021-2025 Laboratories for Ubiquitous Deterministic Computing (UBIDECO),
//                         Institute for Distributed and Cognitive Systems (InDCS), Switzerland.
// Copyright (C) 2021-2025 Dr Maxim Orlovsky.
// All rights under the above copyrights are reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
// in compliance with the License. You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
// or implied. See the License for the specific language governing permissions and limitations under
// the License.

use core::fmt::{self, Debug, Display, Formatter};

pub const OPENING_MULTILINE_COMMENT: &str = "{-";
pub const CLOSING_MULTILINE_COMMENT: &str = "-}";

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Brackets {
    Round,
    Square,
    Curvy,
}

impl Display for Brackets {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Brackets::Round => f.write_str("parenthesis"),
            Brackets::Square => f.write_str("square brackets"),
            Brackets::Curvy => f.write_str("braces"),
        }
    }
}

impl Brackets {
    pub const OPENING_BRACKETS: [char; 3] = ['(', '[', '{'];
    pub const CLOSING_BRACKETS: [char; 3] = [')', ']', '}'];

    pub const fn opening_bracket(self) -> char {
        match self {
            Brackets::Round => '(',
            Brackets::Square => '[',
            Brackets::Curvy => '{',
        }
    }

    pub const fn closing_bracket(self) -> char {
        match self {
            Brackets::Round => ')',
            Brackets::Square => ']',
            Brackets::Curvy => '}',
        }
    }

    pub fn detect_opening(s: &str) -> Option<Self> {
        if s.starts_with(Self::Round.opening_bracket()) {
            Some(Self::Round)
        } else if s.starts_with(Self::Square.opening_bracket()) {
            Some(Self::Square)
        } else if s.starts_with(Self::Curvy.opening_bracket()) {
            Some(Self::Curvy)
        } else {
            None
        }
    }

    pub fn detect_closing(s: &str) -> Option<Self> {
        if s.starts_with(Self::Round.closing_bracket()) {
            Some(Self::Round)
        } else if s.starts_with(Self::Square.closing_bracket()) {
            Some(Self::Square)
        } else if s.starts_with(Self::Curvy.closing_bracket()) {
            Some(Self::Curvy)
        } else {
            None
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Quotes {
    Single,
    Double,
    TripleDouble,
    Back,
    TripleBack,
}

impl Display for Quotes {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Quotes::Single => f.write_str("single quotes"),
            Quotes::Double => f.write_str("double quotes"),
            Quotes::TripleDouble => f.write_str("triple quotes"),
            Quotes::Back => f.write_str("backquotes"),
            Quotes::TripleBack => f.write_str("triple backquotes"),
        }
    }
}

impl Quotes {
    pub const QUOTES: [char; 3] = ['"', '\'', '`'];

    pub const fn len(&self) -> usize {
        match self {
            Quotes::Single => 1,
            Quotes::Double => 1,
            Quotes::TripleDouble => 3,
            Quotes::Back => 1,
            Quotes::TripleBack => 3,
        }
    }

    pub const fn quotes_str(&self) -> &'static str {
        match self {
            Quotes::Single => "'",
            Quotes::Double => "\"",
            Quotes::TripleDouble => r#"""""#,
            Quotes::Back => "`",
            Quotes::TripleBack => "```",
        }
    }

    pub fn detect(s: &str) -> Option<Self> {
        if s.starts_with(Self::TripleDouble.quotes_str()) {
            Some(Self::TripleDouble)
        } else if s.starts_with(Self::TripleBack.quotes_str()) {
            Some(Self::TripleBack)
        } else if s.starts_with(Self::Single.quotes_str()) {
            Some(Self::Single)
        } else if s.starts_with(Self::Double.quotes_str()) {
            Some(Self::Double)
        } else if s.starts_with(Self::Back.quotes_str()) {
            Some(Self::Back)
        } else {
            None
        }
    }
}
