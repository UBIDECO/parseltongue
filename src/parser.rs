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
use core::str::Lines;

pub const OPENING_MULTILINE_COMMENT: &str = "{-";
pub const CLOSING_MULTILINE_COMMENT: &str = "-}";

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash, Debug, Default)]
pub struct Loc {
    pub line: usize,
    pub col: usize,
}

impl Display for Loc {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line + 1, self.col + 1)
    }
}

impl From<(usize, usize)> for Loc {
    fn from((line, col): (usize, usize)) -> Self { Loc { line, col } }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Display)]
pub enum Brackets {
    #[display("parenthesis")]
    Round,
    #[display("square brackets")]
    Square,
    #[display("braces")]
    Curvy,
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

    pub fn start(self, loc: impl Into<Loc>) -> BlockStart {
        BlockStart { ty: BlockTy::Brackets(self), begin: loc.into() }
    }
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

    pub fn start(self, loc: impl Into<Loc>) -> BlockStart {
        BlockStart { ty: BlockTy::Quotes(self), begin: loc.into() }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Display)]
pub enum BlockTy {
    #[display("code block")]
    Code,
    #[display("{0} block")]
    Brackets(Brackets),
    #[display("{0} block")]
    Quotes(Quotes),
    #[display("multiline comment block")]
    Comment,
}

impl BlockTy {
    pub fn start(self, loc: impl Into<Loc>) -> BlockStart {
        BlockStart { ty: self, begin: loc.into() }
    }

    pub fn len(&self) -> usize {
        match self {
            BlockTy::Code => 0,
            BlockTy::Brackets(_) => 1,
            BlockTy::Quotes(quotes) => quotes.len(),
            BlockTy::Comment => 2,
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Display)]
#[display("{ty} was defined in {begin}")]
pub struct BlockStart {
    pub ty: BlockTy,
    pub begin: Loc,
}

impl BlockStart {
    pub const fn end(self, line: usize, col: usize) -> Block {
        Block { ty: self.ty, begin: self.begin, end: Loc { line, col } }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Block {
    pub ty: BlockTy,
    // TODO: Consider replacing with Range
    pub begin: Loc,
    pub end: Loc,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct ParsedSource<'src> {
    pub source: &'src str,
    pub lines: Vec<&'src str>,
    pub blocks: Vec<Block>,
}

impl<'src> ParsedSource<'src> {
    pub fn parse(source: &'src str) -> Result<Self, UnparsedSource<'src>> {
        let lines = source.lines().collect();
        match Parser::parse(source) {
            Err(error) => Err(UnparsedSource { lines, error }),
            Ok(blocks) => Ok(Self { source, lines, blocks }),
        }
    }

    pub fn get(&self, index: usize) -> Option<(BlockTy, &str)> {
        let block = self.blocks.get(index)?;
        let start = self.lines[block.begin.line].as_ptr() as usize + block.begin.col
            - self.source.as_ptr() as usize;
        let end = self.lines[block.end.line].as_ptr() as usize + block.end.col
            - self.source.as_ptr() as usize;
        Some((block.ty, &self.source[start..end]))
    }
}

pub struct Parser<'src>
where Self: 'src
{
    lines: Lines<'src>,
    curr_line: &'src str,
    curr_loc: Loc,
}

impl<'src> Parser<'src> {
    pub fn parse(code: &'src str) -> Result<Vec<Block>, ParseError> {
        let mut lines = code.lines();
        let Some(curr_line) = lines.next() else {
            return Ok(vec![]);
        };
        let mut parser = Parser { lines, curr_line, curr_loc: Loc::default() };
        parser.parse_blocks()
    }

    pub fn parse_comments(&mut self) -> Result<Block, ParseError> {
        debug_assert!(self.curr_line.starts_with(OPENING_MULTILINE_COMMENT));
        let block = BlockTy::Comment.start(self.curr_loc);
        let mut depth = 0usize;
        self.shift_col(2);
        loop {
            if self.curr_line.starts_with(CLOSING_MULTILINE_COMMENT) {
                if depth == 0 {
                    return Ok(self.end(block));
                } else {
                    depth -= 1;
                }
            } else if self.curr_line.starts_with(OPENING_MULTILINE_COMMENT) {
                depth += 1;
            }
            self.shift_or_fail(block)?;
        }
    }

    pub fn parse_quotes(&mut self, quotes: Quotes) -> Result<Block, ParseError> {
        debug_assert!(self.curr_line.starts_with(quotes.quotes_str()));
        let block = quotes.start(self.curr_loc);
        self.shift_col(quotes.len());
        loop {
            if let Some(col_end) = self.curr_line.find(quotes.quotes_str()) {
                self.shift_col(col_end);
                return Ok(self.end(block));
            }
            self.shift_or_fail(block)?;
        }
    }

    pub fn parse_brackets(&mut self, brackets: Brackets) -> Result<Block, ParseError> {
        debug_assert!(self.curr_line.starts_with(brackets.opening_bracket()));
        let block = brackets.start(self.curr_loc);
        self.shift_col(1);
        loop {
            if let Some(closing_bracket) = Brackets::detect_closing(self.curr_line) {
                if closing_bracket != brackets {
                    return Err(ParseError::MismatchedBrackets(
                        block,
                        self.curr_loc,
                        closing_bracket,
                    ));
                } else {
                    return Ok(self.end(block));
                }
            }
            self.shift_or_fail(block)?;
            self.parse_custom_block()?;
        }
    }

    pub fn parse_custom_block(&mut self) -> Result<Option<Block>, ParseError> {
        let block = if self.curr_line.starts_with(OPENING_MULTILINE_COMMENT) {
            self.parse_comments()?
        } else if self.curr_line.starts_with(CLOSING_MULTILINE_COMMENT) {
            return Err(ParseError::UnmatchedComment(self.curr_loc));
        } else if let Some(quotes) = Quotes::detect(self.curr_line) {
            self.parse_quotes(quotes)?
        } else if let Some(brackets) = Brackets::detect_opening(self.curr_line) {
            self.parse_brackets(brackets)?
        } else {
            return Ok(None);
        };
        Ok(Some(block))
    }

    fn parse_blocks(&mut self) -> Result<Vec<Block>, ParseError> {
        let mut blocks = vec![];
        while self.skip_whitespace().is_some() {
            if let Some(block) = self.parse_custom_block()? {
                blocks.push(block);
            } else if let Some(closing_bracket) = Brackets::detect_closing(self.curr_line) {
                return Err(ParseError::UnmatchedBrackets(self.curr_loc, closing_bracket));
            } else {
                let end = self.curr_loc.col + self.curr_line.len();
                let block = BlockTy::Code
                    .start(self.curr_loc)
                    .end(self.curr_loc.line, end);
                blocks.push(block);

                let Some(next_line) = self.lines.next() else {
                    return Ok(blocks);
                };
                self.curr_line = next_line;
                self.curr_loc.line += 1;
                self.curr_loc.col = 0;
            }
        }
        Ok(blocks)
    }

    fn end(&mut self, block: BlockStart) -> Block {
        self.shift_col(block.ty.len());
        block.end(self.curr_loc.line, self.curr_loc.col)
    }

    #[must_use]
    fn skip_whitespace(&mut self) -> Option<()> {
        loop {
            let start = self.curr_line.as_ptr() as usize;
            let trimmed = self.curr_line.trim_start();

            if trimmed.is_empty() {
                self.shift_line()?;
                continue;
            }

            let new = trimmed.as_ptr() as usize;
            self.curr_line = trimmed;
            self.curr_loc.col += new - start;
            return Some(());
        }
    }

    fn shift_or_fail(&mut self, block: BlockStart) -> Result<(), ParseError> {
        if self.curr_line.is_empty() {
            self.shift_line().ok_or(ParseError::from(block))?;
        } else {
            self.curr_line = &self.curr_line[1..];
            self.curr_loc.col += 1;
        }
        self.skip_whitespace().ok_or(ParseError::from(block))?;
        Ok(())
    }

    #[must_use]
    fn shift_line(&mut self) -> Option<()> {
        self.curr_line = &self.lines.next()?;
        self.curr_loc.line += 1;
        self.curr_loc.col = 0;
        Some(())
    }

    fn shift_col(&mut self, offset: usize) {
        self.curr_line = &self.curr_line[offset..];
        self.curr_loc.col += offset;
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum ParseError {
    #[display("mismatched {2} at {1} when {0} was expected")]
    MismatchedBrackets(BlockStart, Loc, Brackets),
    #[display("unexpected end of comment")]
    UnmatchedComment(Loc),
    #[display("closing {1} in {0} without opening them first")]
    UnmatchedBrackets(Loc, Brackets),

    #[display("{0} is not closed")]
    UnclosedBrackets(BlockStart),
    #[display("multiline comment block is not closed")]
    UnclosedComment(BlockStart),
    #[display("{0} is not closed")]
    UnclosedQuotes(BlockStart),
}

impl From<BlockStart> for ParseError {
    fn from(block: BlockStart) -> Self {
        match block.ty {
            BlockTy::Code => unreachable!(),
            BlockTy::Brackets(_) => Self::UnclosedBrackets(block),
            BlockTy::Quotes(_) => Self::UnclosedQuotes(block),
            BlockTy::Comment => Self::UnclosedComment(block),
        }
    }
}

impl ParseError {
    pub fn block_start(&self) -> Option<BlockStart> {
        match self {
            ParseError::MismatchedBrackets(block, _, _)
            | ParseError::UnclosedBrackets(block)
            | ParseError::UnclosedComment(block)
            | ParseError::UnclosedQuotes(block) => Some(*block),
            ParseError::UnmatchedComment(_) | ParseError::UnmatchedBrackets(_, _) => None,
        }
    }

    pub fn error_loc(&self) -> Option<Loc> {
        match self {
            ParseError::UnclosedComment(_)
            | ParseError::UnclosedBrackets(_)
            | ParseError::UnclosedQuotes(_) => None,
            ParseError::MismatchedBrackets(_, loc, _)
            | ParseError::UnmatchedComment(loc)
            | ParseError::UnmatchedBrackets(loc, _) => Some(*loc),
        }
    }
}

#[derive(Clone, Eq, PartialEq)]
pub struct UnparsedSource<'src> {
    pub lines: Vec<&'src str>,
    pub error: ParseError,
}

impl<'s> Debug for UnparsedSource<'s> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "Error: {}", self.error)?;
        let err_loc = self
            .error
            .error_loc()
            .unwrap_or(Loc { line: self.lines.len(), col: 0 });
        writeln!(f, "      --> line {}, column {}", err_loc.line + 1, err_loc.col + 1)?;

        if err_loc.line > 0 {
            writeln!(f, "{: >6} | {}", err_loc.line, self.lines[err_loc.line - 1])?;
        }
        if err_loc.line >= self.lines.len() {
            writeln!(f, "{: >6} | EOF", err_loc.line + 1)?;
        } else {
            writeln!(f, "{: >6} | {}", err_loc.line + 1, self.lines[err_loc.line])?;
        }
        let pos = err_loc.col + 1;
        writeln!(f, "       |{: >pos$}^", "")?;
        match &self.error {
            ParseError::MismatchedBrackets(block, _, brackets) => writeln!(
                f,
                "       |{: >pos$}{brackets} closing which doesn't correspond to {block}",
                ""
            )?,
            ParseError::UnmatchedComment(_) => writeln!(
                f,
                "       |{: >pos$}closed multiline comment block which was not opened before",
                ""
            )?,
            ParseError::UnmatchedBrackets(_, brackets) => writeln!(
                f,
                "       |{: >pos$}{brackets} closing which doesn't have a corresponding opening \
                 bracket",
                ""
            )?,
            ParseError::UnclosedBrackets(block) => writeln!(
                f,
                "       |{: >pos$}at the end of the file {} remains unclosed",
                "", block.ty
            )?,
            ParseError::UnclosedComment(_) => writeln!(
                f,
                "       |{: >pos$}at the end of the file multiline comment block remains unclosed",
                ""
            )?,
            ParseError::UnclosedQuotes(block) => writeln!(
                f,
                "       |{: >pos$}at the end of the file {} remains unclosed",
                "", block.ty
            )?,
        }

        if let Some(start) = self.error.block_start() {
            writeln!(f)?;
            writeln!(f, "      --> the relevant {start}")?;
            writeln!(f, "{: >6} | {}", start.begin.line + 1, self.lines[start.begin.line])?;
            writeln!(f, "       |{: >pos$} ^", "", pos = start.begin.col)?;
            writeln!(
                f,
                "       |{: >pos$} the block was originally defined here",
                "",
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

    fn parse(code: &str) -> ParsedSource {
        match ParsedSource::parse(code) {
            Err(err) => {
                eprintln!("{err}");
                panic!("Test case has failed");
            }
            Ok(parsed) => parsed,
        }
    }

    fn test_block(code: &str, ty: BlockTy) {
        let parsed = parse(code);
        assert_eq!(parsed.blocks.len(), 1);
        assert_eq!(parsed.blocks[0].ty, ty);
        assert_eq!(code.trim(), parsed.get(0).unwrap().1);
    }

    fn test_blocks<const LEN: usize>(code: &str, ty: [BlockTy; LEN], src: [&str; LEN]) {
        let parsed = parse(code);
        assert_eq!(parsed.blocks.len(), LEN);
        for i in 0..LEN {
            assert_eq!(parsed.blocks[i].ty, ty[i]);
            assert_eq!(parsed.get(i).unwrap().1, src[i]);
        }
    }

    #[test]
    fn empty() {
        for code in ["", " ", "\t", " \t ", "\n", "\n \n", "\r", "\n\r", "\r\n", "\n \t \n    \r"] {
            assert!(parse(code).blocks.is_empty())
        }
    }

    #[test]
    fn comment() {
        test_block("{- some comment -}", BlockTy::Comment);
        test_block("  {- some comment -}  ", BlockTy::Comment);
        test_block("\t  {- some comment -}  ", BlockTy::Comment);
        test_block("\t  {- some \n \n comment -}  ", BlockTy::Comment);
        test_block("{- some {- nested -} comment -}", BlockTy::Comment);
        test_block("{- some \n {- nested -} \n comment -}", BlockTy::Comment);
        test_block("{- some \n {- nested \n multi -} \n comment -}", BlockTy::Comment);
        test_block(
            "{- some \n {- nested {- second level -} \n multi -} \n comment -}",
            BlockTy::Comment,
        );
    }

    #[test]
    fn two_comments() {
        test_blocks(
            "{- first comment -} {- second comment -}",
            [BlockTy::Comment, BlockTy::Comment],
            ["{- first comment -}", "{- second comment -}"],
        );
        test_blocks(
            "{- first comment -} \n\t{- second comment -} \t",
            [BlockTy::Comment, BlockTy::Comment],
            ["{- first comment -}", "{- second comment -}"],
        );
        test_blocks(
            "{- first {- first nested -} comment -} {-{-second nested-} second comment -}",
            [BlockTy::Comment, BlockTy::Comment],
            ["{- first {- first nested -} comment -}", "{-{-second nested-} second comment -}"],
        );
    }

    #[test]
    fn multi_nested() {
        const CODE: &str = include_str!("../test-data/multi_nested.ptg");
        let src = ParsedSource::parse(CODE).unwrap();

        assert_eq!(
            src.get(0).unwrap(),
            (
                BlockTy::Comment,
                r#"{- Some multi-line comment
  with {- nested comments -}
  even {- multiline
   nested {- many times
   -}
  "-} including quoted
-}"#
            )
        );

        assert_eq!(src.get(1).unwrap(), (BlockTy::Code, r#"decl name: some"#));

        assert_eq!(
            src.get(2).unwrap(),
            (
                BlockTy::Brackets(Brackets::Square),
                r#"(brackets many-level { nested }
    "and quited '"
  )"#
            )
        );

        assert_eq!(
            src.get(3).unwrap(),
            (
                BlockTy::Quotes(Quotes::TripleBack),
                r#"back-quoted part
 with unclosed brackets {
 and wrong quotes ""#
            )
        );
    }
}
