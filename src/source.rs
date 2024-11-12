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

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt::{self, Debug, Display, Formatter};

use crate::LexerError;

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Default)]
pub struct Loc {
    pub offset: usize, // Needed to compute the total length in spans
    pub line: usize,
    pub col: usize,
}

impl Ord for Loc {
    fn cmp(&self, other: &Self) -> Ordering {
        let ord = self.offset.cmp(&other.offset);
        match ord {
            Ordering::Less => {
                debug_assert!(self.line < other.line || self.col < other.col);
            }
            Ordering::Equal => {
                debug_assert_eq!(self.line, other.line);
                debug_assert_eq!(self.col, other.col);
            }
            Ordering::Greater => {
                debug_assert!(self.line > other.line || self.col > other.col);
            }
        }
        ord
    }
}

impl PartialOrd for Loc {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}

impl Display for Loc {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line + 1, self.col + 1)
    }
}

impl Loc {
    pub const fn span(self, end: Loc) -> Span { Span { start: self, end } }
    pub const fn line_span(self, len: usize) -> Span {
        let mut end = self;
        end.col += len;
        end.offset += len;
        Span { start: self, end }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Default)]
pub struct Span {
    pub start: Loc,
    pub end: Loc,
}

impl Ord for Span {
    fn cmp(&self, other: &Self) -> Ordering { self.start.cmp(&other.start) }
}

impl PartialOrd for Span {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}

impl Display for Span {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl Span {
    pub fn len(&self) -> usize { self.end.offset - self.start.offset }
    pub fn lines(&self) -> usize { self.end.line - self.start.line }
    pub fn is_empty(&self) -> bool { self.start.offset == self.end.offset }

    pub fn extend(&mut self, other: Span) {
        // debug_assert_eq!(self.end.offset + 1, other.start.offset);
        self.end = other.end;
    }
}

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct Source<'src> {
    pub file: Option<&'src str>,
    pub raw: &'src str,
    pub lines: Vec<&'src str>,
}

impl<'src> From<&'src str> for Source<'src> {
    fn from(raw: &'src str) -> Self {
        assert!(raw.find('\r').is_none(), "source string must not contain caret return characters");
        Source {
            file: None,
            raw,
            lines: raw.split('\n').map(|s| s.trim_end_matches('\r')).collect(),
        }
    }
}

impl<'src> Source<'src> {
    pub fn span(&self, span: Span) -> &'src str { &self.raw[span.start.offset..span.end.offset] }

    pub fn fmt_span(&self, f: Formatter<'_>, span: Span) { todo!() }

    pub fn line_after(&self, loc: Loc) -> &'src str {
        if self.lines.is_empty() {
            self.raw
        } else if loc.line >= self.lines.len() {
            ""
        } else {
            &self.lines[loc.line][loc.col..]
        }
    }

    pub fn eof(&self) -> Loc {
        Loc {
            offset: self.raw.len(),
            line: self.lines.len() - 1,
            col: self.lines.last().copied().map(str::len).unwrap_or_default(),
        }
    }
}
#[derive(Clone, Eq, PartialEq)]
pub struct UnparsedSource<'src> {
    pub source: &'src Source<'src>,
    pub error: LexerError,
}

impl<'s> Debug for UnparsedSource<'s> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "Error: {}", self.error)?;
        let err_loc = self.error.error_loc().unwrap_or(Loc {
            line: self.source.lines.len(),
            col: 0,
            offset: self.source.raw.len(),
        });
        writeln!(f, "      --> line {}, column {}", err_loc.line + 1, err_loc.col + 1)?;

        if err_loc.line > 0 {
            writeln!(f, "{: >6} | {}", err_loc.line, self.source.lines[err_loc.line - 1])?;
        }
        if err_loc.line >= self.source.lines.len() {
            writeln!(f, "{: >6} | EOF", err_loc.line + 1)?;
        } else {
            writeln!(f, "{: >6} | {}", err_loc.line + 1, self.source.lines[err_loc.line])?;
        }
        let pos = err_loc.col + 1;
        writeln!(f, "       |{: >pos$}^", "")?;
        match &self.error {
            LexerError::MismatchedBrackets(block, _, brackets) => writeln!(
                f,
                "       |{: >pos$}{brackets} closing which doesn't correspond to {block}",
                ""
            )?,
            LexerError::UnmatchedComment(_) => writeln!(
                f,
                "       |{: >pos$}closed multiline comment block which was not opened before",
                ""
            )?,
            LexerError::UnmatchedBrackets(_, brackets) => writeln!(
                f,
                "       |{: >pos$}{brackets} closing which doesn't have a corresponding opening \
                 bracket",
                ""
            )?,
            LexerError::UnclosedBrackets(block) => writeln!(
                f,
                "       |{: >pos$}at the end of the file {} remains unclosed",
                "", block.ty
            )?,
            LexerError::UnclosedComment(_) => writeln!(
                f,
                "       |{: >pos$}at the end of the file multiline comment block remains unclosed",
                ""
            )?,
            LexerError::UnclosedQuotes(block) => writeln!(
                f,
                "       |{: >pos$}at the end of the file {} remains unclosed",
                "", block.ty
            )?,
        }

        if let Some(start) = self.error.block_start() {
            writeln!(f)?;
            writeln!(f, "      --> the relevant {start}")?;
            writeln!(f, "{: >6} | {}", start.begin.line + 1, self.source.lines[start.begin.line])?;
            writeln!(f, "       |{: >pos$} ^", "", pos = start.begin.col)?;
            writeln!(
                f,
                "       |{: >pos$} the {} block was originally defined here",
                "",
                start.ty,
                pos = start.begin.col
            )?;
        }

        Ok(())
    }
}

impl<'src> Display for UnparsedSource<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result { Debug::fmt(self, f) }
}
