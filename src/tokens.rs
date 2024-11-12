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

use crate::{Source, Span};

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Ident<'src> {
    pub code: &'src str,
    pub span: Span,
}

impl<'src> Debug for Ident<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result { todo!() }
}

impl<'src> Display for Ident<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result { f.write_str(self.code) }
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Token<'src> {
    pub code: &'src str,
    pub span: Span,
}

impl<'src> Debug for Token<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result { todo!() }
}

impl<'src> Display for Token<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result { f.write_str(self.code) }
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Section<'src> {
    pub code: &'src str,
    pub span: Span,
}

impl<'src> Debug for Section<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result { todo!() }
}

impl<'src> Display for Section<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result { f.write_str(self.code) }
}

impl<'src> Source<'src> {
    pub fn section(&self, span: Span) -> Section<'src> { Section { code: self.span(span), span } }
}

impl<'src> Section<'src> {
    pub fn pop_ident(&mut self) -> Option<Ident<'src>> {
        if self.code.trim().is_empty() {
            return None;
        }
        *self = self.trim();
        let end = self
            .code
            .find(|c: char| c.is_ascii_whitespace())
            .unwrap_or(self.span.end.offset);
        let term = &self.code[..end];
        self.code = &self.code[end..];
        let mut span = self.span;
        self.span.start.offset += end;
        self.span.start.col += end;
        span.end.offset = span.start.offset + end;
        span.end.col = span.start.col + end;
        Some(Ident { code: term, span })
    }

    // TODO: Use `core::str::Pattern` when stabilized
    pub fn pop_token(&mut self, pattern: &str) -> Option<Token<'src>> {
        let Some(code) = self.code.strip_prefix(pattern) else {
            return None;
        };

        let prev = self.code.as_ptr() as usize;
        let new = code.as_ptr() as usize;
        let len = new - prev;
        let cut = &self.code[..len];
        assert!(!cut.contains('\n'), "`pop_token` pattern must not contain newlines");
        let span = self.span.start.line_span(len);
        self.code = code;
        self.span.start = span.end;

        Some(Token { code: cut, span })
    }

    pub fn trim(&self) -> Section<'src> {
        let mut term = *self;
        let orig_start = term.code.as_ptr() as usize;
        let orig_end = term.code[term.code.len() - 1..].as_ptr() as usize;

        // 1, Skip empty start lines
        for line in self.code.lines() {
            if !line.trim().is_empty() {
                break;
            }
            term.span.start.line += 1;
            term.span.start.col = 0;
        }
        // 2. Skip empty ending
        for line in self.code.lines().rev() {
            if !line.trim().is_empty() {
                break;
            }
            term.span.end.line -= 1;
            term.span.end.col = line.len();
        }
        let start = term.code.as_ptr() as usize;
        let end = term.code[term.code.len() - 1..].as_ptr() as usize;
        term.code = term.code.trim();

        term.span.start.offset += term.code.as_ptr() as usize - orig_start;
        term.span.start.col += term.code.as_ptr() as usize - start;

        term.span.start.offset -= orig_end - term.code[term.code.len() - 1..].as_ptr() as usize;
        term.span.start.col -= end - term.code[term.code.len() - 1..].as_ptr() as usize;

        term
    }

    pub fn is_empty(&self) -> bool { self.code.trim().is_empty() }
}
