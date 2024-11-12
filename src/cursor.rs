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

use crate::{Loc, Source};

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug)]
pub struct Cursor<'src> {
    pub source: &'src Source<'src>,
    pub cursor: Loc,
    pub limit: Loc,
}

impl<'src> Cursor<'src> {
    pub fn new(source: &'src Source<'src>) -> Self {
        Cursor { cursor: Default::default(), limit: source.eof(), source }
    }

    pub fn peek_char_this_line(&self) -> Option<char> { self.line_remainder().chars().next() }

    pub fn line_remainder(&self) -> &'src str { self.source.line_after(self.cursor) }

    #[must_use]
    pub fn is_finished(&self) -> bool {
        debug_assert!(self.cursor.offset <= self.source.raw.len());
        if !self.source.lines.is_empty() {
            debug_assert!(self.cursor.col <= self.source.lines[self.cursor.line].len());
        }
        debug_assert!(self.cursor.line <= self.limit.line);
        if self.cursor.offset == self.limit.offset {
            debug_assert!(self.cursor.line == self.limit.line);
            debug_assert!(self.cursor.col == self.limit.col);
            true
        } else {
            false
        }
    }

    #[must_use]
    pub fn is_last_line(&self) -> bool { self.cursor.line == self.limit.line }

    pub fn skip_line(&mut self) -> bool {
        if self.is_last_line() {
            return false;
        }
        self.cursor.line += 1;
        self.cursor.col = 0;
        let pos = self.source.lines[self.cursor.line].as_ptr() as usize;
        self.cursor.offset = pos - self.source.raw.as_ptr() as usize;
        !self.is_finished()
    }

    pub fn skip_char(&mut self) -> bool {
        if self.is_finished() || self.line_remainder().is_empty() {
            return false;
        }
        self.cursor.col += 1;
        self.cursor.offset += 1;
        true
    }

    #[must_use]
    pub fn skip_char_or_line(&mut self) -> bool {
        if self.is_finished() {
            return false;
        }
        if self.skip_char() {
            return true;
        }
        while self.skip_line() {
            if !self.line_remainder().is_empty() {
                return true;
            }
        }
        true
    }

    pub fn skip_whitespace_in_line(&mut self) {
        let line = self.line_remainder();
        if line.is_empty() {
            return;
        }
        let pos = line.as_ptr() as usize;
        let offset = line.trim_start().as_ptr() as usize - pos;
        if offset != 0 {
            self.cursor.col += offset;
            self.cursor.offset += offset;
        }
    }

    pub fn skip_whitespace(&mut self) {
        while !self.is_finished() {
            let line = self.line_remainder();
            if line.is_empty() {
                self.skip_line();
                continue;
            }
            let pos = line.as_ptr() as usize;
            let offset = line.trim_start().as_ptr() as usize - pos;
            if offset == 0 {
                break;
            }
            self.cursor.col += offset;
            self.cursor.offset += offset;
        }
    }

    pub fn seek_in_line(&mut self, offset: usize) -> bool {
        debug_assert!(offset <= self.line_remainder().len());
        self.cursor.col += offset;
        self.cursor.offset += offset;
        !self.is_finished()
    }

    pub fn seek(&mut self, mut offset: usize) {
        debug_assert!(self.cursor.offset + offset <= self.limit.offset);
        while !self.is_finished() && offset > self.line_remainder().len() {
            offset -= self.line_remainder().len() + 1;
            self.skip_line();
        }
        if self.is_finished() {
            assert_eq!(offset, 0);
        }
        self.cursor.col += offset;
        self.cursor.offset += offset;
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn test_cursor(text: &str) {
        let src = Source::from(text);
        let mut cursor = Cursor::new(&src);
        let mut loc = Loc::default();
        assert_eq!(cursor.limit.line, text.chars().filter(|c| *c == '\n').count());
        while !cursor.is_finished() {
            loc.col += 1;
            while loc.offset < text.len() && text.as_bytes()[loc.offset] == b'\n' {
                assert_eq!(cursor.line_remainder(), "");
                assert_eq!(cursor.peek_char_this_line(), None);
                loc.col = 0;
                loc.line += 1;
                loc.offset += 1;
            }
            if loc.col != 0 {
                loc.offset += 1;
            }

            let exists = cursor.skip_char_or_line();
            assert!(exists);
            assert_eq!(cursor.cursor, loc);
        }
        assert_eq!(cursor.cursor.offset, text.len());
        assert_eq!(cursor.skip_char_or_line(), false);
        assert_eq!(cursor.line_remainder(), "");
        assert_eq!(cursor.peek_char_this_line(), None);
    }

    #[test]
    fn empty() {
        let src = Source::from("");
        let mut cursor = Cursor::new(&src);
        assert!(cursor.is_last_line());
        assert!(cursor.is_finished());
        assert_eq!(cursor.line_remainder(), "");
        assert_eq!(cursor.peek_char_this_line(), None);
        assert_eq!(cursor.skip_char_or_line(), false);
        assert!(cursor.is_last_line());
        assert!(cursor.is_finished());
    }

    #[test]
    fn whitespace() {
        test_cursor(" ");
        test_cursor("\n");
        test_cursor("\n\n");
        test_cursor("\n\n\n\n\n\n\n\n\n\n");
    }

    #[test]
    fn next_char_or_line() {
        test_cursor("A");
        test_cursor("AB");
        test_cursor("\nA");
        test_cursor("\n\nA");
        test_cursor("A\nB");
        test_cursor("A\nB\n");
        test_cursor("\nA\nB\n");
    }

    #[test]
    fn text() {
        test_cursor(
            r#"
        In Rust, you can use a raw string literal to include newline characters
        and indent lines of the literal at a fixed column. Here's an example:

        In the code above, the variable s is a raw string literal. It starts
        with r#", ends with #", and includes newline characters. Its lines are
        also intended from the start of the line. When printing s, you'll get a
        multi-line string with the same format as it appears in the raw string
        literal.


        Please note that each line's indentation is preserved in the string.
        If you want to remove the indentation, you might want to postprocess the
        string accordingly. However, Rust currently does not support that out of
        the box like Python's textwrap.dedent function.
        "#,
        );
    }

    #[test]
    fn skip_whitespace() {
        for text in ["", " ", "  ", "     ", "\n", "\n\n", "\n\n\n\n", " \n \n\t\n  \t   \n"] {
            let src = Source::from(text);
            let mut cursor = Cursor::new(&src);
            cursor.skip_whitespace();
            assert!(cursor.is_finished());
        }
    }

    #[test]
    fn seek() {
        for text in [" ", "  ", "     ", "\n", "\n\n", "\n\n\n\n", " \n \n\t\n  \t   \n"] {
            let src = Source::from(text);
            let mut cursor = Cursor::new(&src);
            cursor.seek(text.len() - 1);
            assert!(!cursor.is_finished());
            assert_eq!(cursor.cursor.offset, text.len() - 1);
            cursor.seek(1);
            assert_eq!(cursor.cursor.offset, text.len());
            assert!(cursor.is_finished());
        }
    }
}
