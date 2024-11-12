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
use core::fmt::{self, Debug, Formatter};

use crate::{Brackets, Lexeme, Lexer, LexerError, Quotes, Source, Span};

#[derive(Clone, Default)]
pub struct Node<'src> {
    pub term: &'src str,
    pub ident: usize,
    pub span: Span,
    pub children: Vec<Node<'src>>,
}

impl<'src> Debug for Node<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let width = f.width().unwrap_or(0) + 1;
        writeln!(f, "{:><count$} Term spanning {}", "", self.span, count = width)?;
        for (no, line) in self.term.lines().enumerate() {
            writeln!(f, "{: >6} | {line}", no + self.span.start.line + 1)?;
        }
        for node in &self.children {
            writeln!(f, "{node:width$?}")?;
        }
        Ok(())
    }
}

pub fn preparse<'src>(source: &Source<'src>) -> Result<Node<'src>, ParseError> {
    let lexemes = Lexer::parse(source).map_err(|e| e.error)?;

    fn non_continuation(c: char) -> bool {
        c.is_alphanumeric()
            || Brackets::CLOSING_BRACKETS.contains(&c)
            || Quotes::QUOTES.contains(&c)
    }

    let mut stack = Vec::<Node>::new();
    let mut curr = Node::default();
    for lexeme in lexemes {
        if lexeme.span.start.col == 0 && curr.term.trim().ends_with(non_continuation) {
            let term = source.span(lexeme.span);
            let new_ident = term.len() - term.trim_start().len();
            let node = Node { term, ident: new_ident, span: lexeme.span, children: vec![] };

            // Pop parents unless we get the same or larger ident
            while new_ident <= curr.ident && !stack.is_empty() {
                let mut parent = stack.pop().unwrap();
                // - add prev_parent to parent children
                parent.children.push(curr);
                curr = parent;
            }
            if new_ident < curr.ident {
                return Err(ParseError::InvalidIdent(lexeme));
            }
            stack.push(curr);
            curr = node;
        } else {
            curr.span.extend(lexeme.span);
            curr.term = source.span(curr.span);
        }
    }

    while let Some(mut parent) = stack.pop() {
        if !curr.term.trim().is_empty() || !curr.children.is_empty() {
            parent.children.push(curr);
        }
        curr = parent;
    }

    Ok(curr)
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum ParseError {
    Lexer(LexerError),
    InvalidIdent(Lexeme),
}

impl From<LexerError> for ParseError {
    fn from(err: LexerError) -> Self { ParseError::Lexer(err) }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn example() {
        const CODE: &str = r#"---- Two-dimensional coordinate
data Coord2D: x U64,
              y U64

---- Array of coordinates
data Array: $LEN U8 =>
    [Coord2D ^ $LEN]

data Matrix: $LEN U8 => [
    Array $LEN ^ $LEN
]

---- Cartesian multiplication of two arrays
infx `*`: $LEN U8 => a Array $LEN, b Array $LEN -> Matrix $LEN
    [a |> {- for each a -}
       [b |> {- and for each b -}
           (a.x *! b.x, a.y *! b.y)
       ] -- end of b loop
    ] -- end of a loop

fx helloWorld
    {-
        This is just a dumb program
    -}
    printLn """
    Hello, World!
    """
"#;

        let source = Source::from(CODE);
        let module = preparse(&source).unwrap();

        println!("{module:?}");
    }
}
