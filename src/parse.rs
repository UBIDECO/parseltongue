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

use core::fmt::{self, Debug, Formatter};

#[derive(Clone, Eq, PartialEq)]
pub struct ParseError<'s> {
    pub program: &'s str,
    pub line: usize,
    pub pos: usize,
    pub case: ParseErrorCase,
}

impl<'s> Debug for ParseError<'s> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "Error: {}", self.case)?;

        let mut lines = self.program.lines();
        if self.line > 0 {
            let prev_line = lines.nth(self.line - 1).unwrap();
            writeln!(f, "{: >6} | {prev_line}", self.line)?;
        }

        let line = lines.next().unwrap();
        let pos = self.pos + 8;
        writeln!(f, "{: >6} | {line}", self.line + 1)?;
        writeln!(f, "{: >pos$} ^", "")?;

        match &self.case {
            ParseErrorCase::UnmatchedBrackets(bracket) => writeln!(f, "{: >pos$} unmatched closing {}", "", bracket),
            ParseErrorCase::UnclosedBrackets(brackets) => {
                writeln!(f, "{: >pos$} {} were opened here", "", brackets)
            }
            ParseErrorCase::UnclosedComment => writeln!(f, "{: >pos$} multiline comment starts here", ""),
            ParseErrorCase::UnclosedQuotes(quotes) => writeln!(f, "{: >pos$} {} starts here", "", quotes),
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum ParseErrorCase {
    #[display("closing {0} without opening them first")]
    UnmatchedBrackets(Brackets),
    #[display("{0} are not closed")]
    UnclosedBrackets(Brackets),
    #[display("multiline comment block is not closed")]
    UnclosedComment,
    #[display("{0} are not closed")]
    UnclosedQuotes(Quotes),
}

impl ParseErrorCase {
    pub fn inside<'s>(self, s: &'s str, line: usize, pos: usize) -> ParseError<'s> {
        ParseError { program: s, case: self, line, pos }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Display)]
pub enum Brackets {
    #[display("parenthesis")]
    Round,
    #[display("brackets")]
    Square,
    #[display("braces")]
    Curvy,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Display)]
pub enum Quotes {
    #[display("single quotes")]
    Single,
    #[display("double quotes")]
    Double,
    #[display("triple quotes")]
    TripleDouble,
    #[display("backquotes")]
    Back,
    #[display("triple backquotes")]
    TripleBack,
}

impl Quotes {
    pub fn len(&self) -> usize {
        match self {
            Quotes::Single => 1,
            Quotes::Double => 1,
            Quotes::TripleDouble => 3,
            Quotes::Back => 1,
            Quotes::TripleBack => 3,
        }
    }

    pub fn close_pat(&self) -> &'static str {
        match self {
            Quotes::Single => "'",
            Quotes::Double => "\"",
            Quotes::TripleDouble => r#"""""#,
            Quotes::Back => "`",
            Quotes::TripleBack => "```",
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
struct Parse1<'s>(Vec<MultiBlock<'s>>);

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum MultiBlock<'s> {
    Commented(&'s str),
    Quoted(Quotes, &'s str),
    Bracketed(Brackets, &'s str),
    Line(&'s str),
}

impl<'s> Parse1<'s> {
    pub fn parse(s: &'s str) -> Result<Self, ParseError<'s>> {
        let orig = s;

        enum State {
            Base(usize, Vec<Brackets>),
            Comment(usize, usize),
            String(usize, Quotes),
        }

        let mut state = State::Base(0, vec![]);
        let mut start = 0usize;
        let mut blocks = vec![];

        for (line, mut s) in s.lines().enumerate() {
            let line_off = s.as_ptr() as usize - orig.as_ptr() as usize;
            loop {
                s = s.trim_start();
                if s.is_empty() {
                    break;
                }
                let pos = s.as_ptr() as usize - orig.as_ptr() as usize;

                match &mut state {
                    State::Base(_, brackets) => {
                        if s.is_empty() {
                            let block = &orig[start..pos];
                            if !block.is_empty() {
                                blocks.extend(block.split("\n").map(MultiBlock::Line));
                            }
                            break;
                        }

                        if s.starts_with("{-") {
                            start = pos;
                            state = State::Comment(line, 0);
                            s = &s[1..];
                        } else if s.starts_with('(') {
                            brackets.push(Brackets::Round);
                        } else if s.starts_with('[') {
                            brackets.push(Brackets::Square);
                        } else if s.starts_with('{') {
                            brackets.push(Brackets::Curvy);
                        } else if s.starts_with(')') {
                            let b = Brackets::Round;
                            let prev = brackets
                                .pop()
                                .ok_or(ParseErrorCase::UnmatchedBrackets(b).inside(orig, line, pos - line_off))?;
                            if prev != b {
                                return Err(ParseErrorCase::UnmatchedBrackets(b).inside(orig, line, pos - line_off));
                            }
                            if brackets.is_empty() {
                                blocks.push(MultiBlock::Bracketed(b, &orig[start..pos]));
                                start = pos;
                                state = State::Base(line, vec![]);
                            }
                        } else if s.starts_with(']') {
                            let b = Brackets::Square;
                            let prev = brackets
                                .pop()
                                .ok_or(ParseErrorCase::UnmatchedBrackets(b).inside(orig, line, pos - line_off))?;
                            if prev != b {
                                return Err(ParseErrorCase::UnmatchedBrackets(b).inside(orig, line, pos - line_off));
                            }
                            if brackets.is_empty() {
                                blocks.push(MultiBlock::Bracketed(b, &orig[start..pos]));
                                start = pos;
                                state = State::Base(line, vec![]);
                            }
                        } else if s.starts_with('}') {
                            let b = Brackets::Curvy;
                            let prev = brackets
                                .pop()
                                .ok_or(ParseErrorCase::UnmatchedBrackets(b).inside(orig, line, pos - line_off))?;
                            if prev != b {
                                return Err(ParseErrorCase::UnmatchedBrackets(b).inside(orig, line, pos - line_off));
                            }
                            if brackets.is_empty() {
                                blocks.push(MultiBlock::Bracketed(b, &orig[start..pos]));
                                start = pos;
                                state = State::Base(line, vec![]);
                            }
                        } else if s.starts_with(r#"""""#) {
                            start = pos;
                            state = State::String(line, Quotes::TripleDouble);
                            s = &s[2..];
                        } else if s.starts_with("```") {
                            start = pos;
                            state = State::String(line, Quotes::TripleBack);
                            s = &s[2..];
                        } else if s.starts_with('\'') {
                            start = pos;
                            state = State::String(line, Quotes::Single);
                        } else if s.starts_with('"') {
                            start = pos;
                            state = State::String(line, Quotes::Double);
                        } else if s.starts_with('`') {
                            start = pos;
                            state = State::String(line, Quotes::Back);
                        }
                    }
                    State::Comment(_, depth) => {
                        if s.starts_with("{-") {
                            *depth += 1;
                            s = &s[1..];
                        } else if s.starts_with("-}") {
                            if *depth == 0 {
                                blocks.push(MultiBlock::Commented(&orig[start..pos]));
                                start = pos;
                                state = State::Base(line, vec![])
                            } else {
                                *depth -= 1;
                            }
                            s = &s[1..];
                        }
                    }
                    State::String(_, quotes) => {
                        if s.starts_with(quotes.close_pat()) {
                            blocks.push(MultiBlock::Quoted(*quotes, &orig[start..pos]));
                            start = pos;
                            s = &s[quotes.len() - 1..];
                            state = State::Base(line, vec![]);
                        }
                    }
                }
                s = &s[1..];
            }
        }

        match state {
            State::Base(line, brackets) => {
                if !brackets.is_empty() {
                    return Err(
                        ParseErrorCase::UnclosedBrackets(brackets.first().unwrap().clone()).inside(orig, line, start)
                    );
                }
            }
            State::Comment(line, _) => {
                return Err(ParseErrorCase::UnclosedComment.inside(orig, line, start));
            }
            State::String(line, quotes) => {
                return Err(ParseErrorCase::UnclosedQuotes(quotes).inside(orig, line, start));
            }
        }

        Ok(Self(blocks))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test() {
        const CODE: &str = include_str!("../test-data/correct.ptg");
        let res = Parse1::parse(CODE).unwrap();

        assert_eq!(
            &res.0[0],
            &MultiBlock::Commented(
                r#"{- Some multi-line comment
  with {- nested comments -}
  even {- multiline
   nested {- many times
   -}
  "-} including quoted
-}"#
            )
        );

        assert_eq!(&res.0[1], &MultiBlock::Line(r#"decl name: some"#));

        assert_eq!(
            &res.0[2],
            &MultiBlock::Bracketed(
                Brackets::Square,
                r#"(brackets many-level { nested }
    "and quited '"
  )"#
            )
        );

        assert_eq!(
            &res.0[3],
            &MultiBlock::Quoted(
                Quotes::TripleBack,
                r#"back-quoted part
 with unclosed brackets {
 and wrong quotes ""#
            )
        );
    }
}
