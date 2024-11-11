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
use alloc::vec;
#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use core::fmt::{self, Debug, Display, Formatter};

use crate::{
    Brackets, Cursor, Loc, Quotes, Source, Span, CLOSING_MULTILINE_COMMENT,
    OPENING_MULTILINE_COMMENT,
};

impl Brackets {
    pub fn start(self, loc: impl Into<Loc>) -> LexStart {
        LexStart { ty: LexTy::Brackets(self), begin: loc.into() }
    }
}

impl Quotes {
    pub fn start(self, loc: impl Into<Loc>) -> LexStart {
        LexStart { ty: LexTy::Quotes(self), begin: loc.into() }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum LexTy {
    Code,
    Brackets(Brackets),
    Quotes(Quotes),
    Comment,
}

impl Display for LexTy {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            LexTy::Code => f.write_str("code block"),
            LexTy::Brackets(brackets) => write!(f, "{brackets} block"),
            LexTy::Quotes(quotes) => write!(f, "{quotes} block"),
            LexTy::Comment => f.write_str("multiline comment block"),
        }
    }
}

impl LexTy {
    pub fn start(self, loc: impl Into<Loc>) -> LexStart { LexStart { ty: self, begin: loc.into() } }

    pub fn delim_len(&self) -> usize {
        match self {
            LexTy::Code => 0,
            LexTy::Brackets(_) => 1,
            LexTy::Quotes(quotes) => quotes.len(),
            LexTy::Comment => 2,
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct LexStart {
    pub ty: LexTy,
    pub begin: Loc,
}

impl Display for LexStart {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} defined in {}", self.ty, self.begin)
    }
}

impl LexStart {
    pub const fn end(self, end: Loc) -> Lexeme {
        Lexeme { ty: self.ty, span: self.begin.span(end) }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Lexeme {
    pub ty: LexTy,
    pub span: Span,
}

pub struct Lexer<'src>(Cursor<'src>);

impl<'src> Lexer<'src> {
    pub fn parse(source: Source<'src>) -> Result<Vec<Lexeme>, UnparsedSource<'src>> {
        let mut parser = Lexer(Cursor::new(source.clone()));
        parser
            .parse_blocks()
            .map_err(|error| UnparsedSource { source, error })
    }

    pub fn parse_comments(&mut self) -> Result<Lexeme, LexerError> {
        let block = LexTy::Comment.start(self.0.cursor);
        let exists = self.0.skip_whitespace_in_line();
        debug_assert!(exists);
        debug_assert!(self.line().starts_with(OPENING_MULTILINE_COMMENT));
        self.0.seek_in_line(2);
        let mut depth = 0usize;
        loop {
            if self.line().starts_with(CLOSING_MULTILINE_COMMENT) {
                if depth == 0 {
                    return Ok(self.end(block));
                } else {
                    depth -= 1;
                }
            } else if self.line().starts_with(OPENING_MULTILINE_COMMENT) {
                depth += 1;
            }
            self.shift_or_fail(block)?;
        }
    }

    pub fn parse_quotes(&mut self, quotes: Quotes) -> Result<Lexeme, LexerError> {
        let block = quotes.start(self.0.cursor);
        let exists = self.0.skip_whitespace_in_line();
        debug_assert!(exists);
        debug_assert!(self.line().starts_with(quotes.quotes_str()));
        self.0.seek_in_line(quotes.len());
        loop {
            if let Some(col_end) = self.line().find(quotes.quotes_str()) {
                let line = self.line();
                self.0.seek_in_line(col_end);
                // Ignore if backslash is used
                if col_end == 0 || line.as_bytes()[col_end - 1] != b'\\' {
                    return Ok(self.end(block));
                }
            }
            self.shift_or_fail(block)?;
        }
    }

    pub fn parse_brackets(&mut self, brackets: Brackets) -> Result<Lexeme, LexerError> {
        let block = brackets.start(self.0.cursor);
        let exists = self.0.skip_whitespace_in_line();
        debug_assert!(exists);
        debug_assert!(self.line().starts_with(brackets.opening_bracket()));
        self.0.seek_in_line(1);
        loop {
            self.0.skip_whitespace_in_line();
            if let Some(closing_bracket) = Brackets::detect_closing(self.line()) {
                return if closing_bracket != brackets {
                    Err(LexerError::MismatchedBrackets(block, self.0.cursor, closing_bracket))
                } else {
                    Ok(self.end(block))
                };
            }
            if self.parse_std_block()?.is_none() {
                self.shift_or_fail(block)?;
            }
        }
    }

    pub fn parse_default(&mut self) -> Result<Lexeme, LexerError> {
        let block = LexTy::Code.start(self.0.cursor);
        self.0.skip_whitespace_in_line();
        self.0.skip_char();
        while !self.line().is_empty() {
            if self.parse_std_block()?.is_none() {
                self.0.skip_char();
            }
        }
        Ok(self.end(block))
    }

    pub fn parse_std_block(&mut self) -> Result<Option<Lexeme>, LexerError> {
        let line = self.line().trim_start();
        let block = if line.starts_with(OPENING_MULTILINE_COMMENT) {
            self.parse_comments()?
        } else if line.starts_with(CLOSING_MULTILINE_COMMENT) {
            return Err(LexerError::UnmatchedComment(self.0.cursor));
        } else if let Some(quotes) = Quotes::detect(line) {
            self.parse_quotes(quotes)?
        } else if let Some(brackets) = Brackets::detect_opening(line) {
            self.parse_brackets(brackets)?
        } else if let Some(closing_bracket) = Brackets::detect_closing(line) {
            return Err(LexerError::UnmatchedBrackets(self.0.cursor, closing_bracket));
        } else {
            return Ok(None);
        };
        Ok(Some(block))
    }

    fn parse_blocks(&mut self) -> Result<Vec<Lexeme>, LexerError> {
        let mut blocks = vec![];
        while !self.0.is_finished() {
            if let Some(block) = self.parse_std_block()? {
                blocks.push(block);
            } else {
                let block = self.parse_default()?;
                if !self.0.source.span(block.span).is_empty() {
                    blocks.push(block);
                }
                self.0.skip_line();
            }
        }
        Ok(blocks)
    }

    fn end(&mut self, block: LexStart) -> Lexeme {
        self.0.seek_in_line(block.ty.delim_len());
        self.0.skip_whitespace_in_line();
        block.end(self.0.cursor)
    }

    fn shift_or_fail(&mut self, block: LexStart) -> Result<(), LexerError> {
        if !self.0.skip_char_or_line() {
            return Err(LexerError::from(block));
        }
        Ok(())
    }

    #[inline]
    fn line(&self) -> &'src str { self.0.line_remainder() }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum LexerError {
    MismatchedBrackets(LexStart, Loc, Brackets),
    UnmatchedComment(Loc),
    UnmatchedBrackets(Loc, Brackets),
    UnclosedBrackets(LexStart),
    UnclosedComment(LexStart),
    UnclosedQuotes(LexStart),
}

impl Display for LexerError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            LexerError::MismatchedBrackets(block, _, brackets) => {
                write!(f, "mismatched {brackets} when {} closing was expected", block.ty)
            }
            LexerError::UnmatchedComment(_) => write!(f, "unexpected end of comment"),
            LexerError::UnmatchedBrackets(_, brackets) => {
                write!(f, "closing {brackets} without opening them first")
            }
            LexerError::UnclosedBrackets(block) => write!(f, "{block} is not closed"),
            LexerError::UnclosedComment(_) => write!(f, "multiline comment block is not closed"),
            LexerError::UnclosedQuotes(block) => write!(f, "{block} is not closed"),
        }
    }
}

// TODO: Activate once MSRV >= 1.81
// impl core::error::Error for ParseError {}
#[cfg(feature = "std")]
impl std::error::Error for LexerError {}

impl From<LexStart> for LexerError {
    fn from(block: LexStart) -> Self {
        match block.ty {
            LexTy::Code => unreachable!(),
            LexTy::Brackets(_) => Self::UnclosedBrackets(block),
            LexTy::Quotes(_) => Self::UnclosedQuotes(block),
            LexTy::Comment => Self::UnclosedComment(block),
        }
    }
}

impl LexerError {
    pub fn block_start(&self) -> Option<LexStart> {
        match self {
            LexerError::MismatchedBrackets(block, _, _)
            | LexerError::UnclosedBrackets(block)
            | LexerError::UnclosedComment(block)
            | LexerError::UnclosedQuotes(block) => Some(*block),
            LexerError::UnmatchedComment(_) | LexerError::UnmatchedBrackets(_, _) => None,
        }
    }

    pub fn error_loc(&self) -> Option<Loc> {
        match self {
            LexerError::UnclosedComment(_)
            | LexerError::UnclosedBrackets(_)
            | LexerError::UnclosedQuotes(_) => None,
            LexerError::MismatchedBrackets(_, loc, _)
            | LexerError::UnmatchedComment(loc)
            | LexerError::UnmatchedBrackets(loc, _) => Some(*loc),
        }
    }
}

#[derive(Clone, Eq, PartialEq)]
pub struct UnparsedSource<'src> {
    pub source: Source<'src>,
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

#[cfg(test)]
mod test {
    use super::*;

    fn parse(code: &str) -> (Source, Vec<Lexeme>) {
        let source = Source::from(code);
        match Lexer::parse(source.clone()) {
            Err(err) => {
                eprintln!("{err}");
                panic!("Test case has failed");
            }
            Ok(parsed) => {
                println!("{parsed:#?}");
                (source, parsed)
            }
        }
    }

    fn test_block(code: &str, ty: LexTy) {
        let (source, lexemes) = parse(code);
        assert_eq!(lexemes.len(), 1);
        assert_eq!(lexemes[0].ty, ty);
        assert_eq!(code.trim_start_matches('\n'), source.span(lexemes[0].span));
    }

    fn test_blocks<const LEN: usize>(code: &str, ty: [LexTy; LEN], src: [&str; LEN]) {
        let (source, lexemes) = parse(code);
        assert_eq!(lexemes.len(), LEN);
        for i in 0..LEN {
            assert_eq!(lexemes[i].ty, ty[i]);
            assert_eq!(src[i], source.span(lexemes[i].span));
        }
    }

    #[test]
    fn empty() {
        assert!(parse("").1.is_empty());
        for code in [" ", "\t", " \t ", "\n", "\n \n"] {
            parse(code);
        }
    }

    #[test]
    #[should_panic]
    fn cr() {
        assert!(parse("").1.is_empty());
        for code in ["\r", "\n\r", "\r\n", "\n \t \n    \r"] {
            assert!(!parse(code).1.is_empty())
        }
    }

    #[test]
    fn comment() {
        test_block("{- some comment -}", LexTy::Comment);
        test_block("  {- some comment -}  ", LexTy::Comment);
        test_block("\t  {- some comment -}  ", LexTy::Comment);
        test_block("\t  {- some \n \n comment -}  ", LexTy::Comment);
        test_block("{- some {- nested -} comment -}", LexTy::Comment);
        test_block("{- some \n {- nested -} \n comment -}", LexTy::Comment);
        test_block("{- some \n {- nested \n multi -} \n comment -}", LexTy::Comment);
        test_block(
            "{- some \n {- nested {- second level -} \n multi -} \n comment -}",
            LexTy::Comment,
        );
    }

    #[test]
    fn two_comments() {
        test_blocks(
            "{- first comment -} {- second comment -}",
            [LexTy::Comment, LexTy::Comment],
            ["{- first comment -} ", "{- second comment -}"],
        );
        test_blocks(
            "{- first comment -} \n\t{- second comment -} \t",
            [LexTy::Comment, LexTy::Comment],
            ["{- first comment -} ", "\t{- second comment -} \t"],
        );
        test_blocks(
            "{- first {- first nested -} comment -} {-{-second nested-} second comment -}",
            [LexTy::Comment, LexTy::Comment],
            ["{- first {- first nested -} comment -} ", "{-{-second nested-} second comment -}"],
        );
    }

    #[test]
    fn quotes() {
        test_block(r#""double-quoted string""#, LexTy::Quotes(Quotes::Double));
        test_block(r#"'single-quoted string'"#, LexTy::Quotes(Quotes::Single));
        test_block(r#"`backquoted string`"#, LexTy::Quotes(Quotes::Back));
        test_block(r#"```tripple-backquoted string```"#, LexTy::Quotes(Quotes::TripleBack));
        test_block(r#""""tripple-quoted string""""#, LexTy::Quotes(Quotes::TripleDouble));
    }

    #[test]
    fn mixed_quotes() {
        test_block(r#""double-quoted ' ` string""#, LexTy::Quotes(Quotes::Double));
        test_block(r#"'single-quoted " ` string'"#, LexTy::Quotes(Quotes::Single));
        test_block(r#"`backquoted " ' string`"#, LexTy::Quotes(Quotes::Back));
        test_block(r#"```tripple-backquoted " ' ` string```"#, LexTy::Quotes(Quotes::TripleBack));
        test_block(r#""""tripple-quoted " ' ` string""""#, LexTy::Quotes(Quotes::TripleDouble));
    }

    #[test]
    fn multiline_quotes() {
        test_block(r#""double-quoted\n string""#, LexTy::Quotes(Quotes::Double));
        test_block(r#"'single-quoted\n string'"#, LexTy::Quotes(Quotes::Single));
        test_block(r#"`backquoted\n string`"#, LexTy::Quotes(Quotes::Back));
        test_block(r#"```tripple-backquoted\n string```"#, LexTy::Quotes(Quotes::TripleBack));
        test_block(r#""""tripple-quoted\n string""""#, LexTy::Quotes(Quotes::TripleDouble));
    }

    #[test]
    fn backslashed_quote() {
        test_block(r#" "quoted string \" with backslash" "#, LexTy::Quotes(Quotes::Double));
        test_block(r#" 'quoted string \' with backslash' "#, LexTy::Quotes(Quotes::Single));
        test_block(r#" `quoted string \` with backslash` "#, LexTy::Quotes(Quotes::Back));
        test_block(
            r#" ```tripple-backquoted string \``` with backslash``` "#,
            LexTy::Quotes(Quotes::TripleBack),
        );
        test_block(
            r#" """tripple-quoted string \""" with backslash""" "#,
            LexTy::Quotes(Quotes::TripleDouble),
        );
    }

    #[test]
    fn brackets_empty() {
        test_block("()", LexTy::Brackets(Brackets::Round));
        test_block("[]", LexTy::Brackets(Brackets::Square));
        test_block("\t{\t}\t", LexTy::Brackets(Brackets::Curvy));
    }

    #[test]
    fn brackets() {
        test_block("( round brackets )", LexTy::Brackets(Brackets::Round));
        test_block("[square brackets]", LexTy::Brackets(Brackets::Square));
        test_block("\t{curly brackets\t}\t", LexTy::Brackets(Brackets::Curvy));
    }

    #[test]
    fn multiline_brackets() {
        test_block("( round \n brackets )", LexTy::Brackets(Brackets::Round));
        test_block("[square\nbrackets]", LexTy::Brackets(Brackets::Square));
        test_block("\n{curly\nbrackets\n}\t", LexTy::Brackets(Brackets::Curvy));
    }

    #[test]
    fn nested_brackets() {
        test_block("(round [square inner] brackets)", LexTy::Brackets(Brackets::Round));
        test_block("(round [square with {} postfix] brackets)", LexTy::Brackets(Brackets::Round));
        test_block("(round [square with {}] brackets)", LexTy::Brackets(Brackets::Round));
        test_block("[square () [{}, (())] brackets]", LexTy::Brackets(Brackets::Square));
    }

    #[test]
    fn multi_nested() {
        const CODE: &str = include_str!("../test-data/multi_nested.ptg");
        test_blocks(CODE, [LexTy::Comment, LexTy::Code, LexTy::Quotes(Quotes::TripleBack)], [
            r#"{- Some multi-line comment
  with {- nested comments -}
  even {- multiline
   nested {- many times
   -}
  "-} including quoted
-}"#,
            r#"decl name: some [
  (brackets many-level { nested }
    "and quoted '"
  )
]"#,
            r#"```back-quoted part
 with unclosed brackets {
 and wrong quotes "
```"#,
        ]);
    }
}
