// Parseltongue: Framework for declarative domain-specific languages
//
// SPDX-License-Identifier: Apache-2.0
//
// Designed in 2021-2026 by Dr Maxim Orlovsky <orlovsky@ubideco.org>
// Written in 2024-2026 by Dr Maxim Orlovsky <orlovsky@ubideco.org>
//
// Copyright (C) 2021-2026 Laboratories for Ubiquitous Deterministic Computing (UBIDECO),
//                         Institute for Distributed and Cognitive Systems (InDCS), Switzerland.
// Copyright (C) 2021-2026 Dr Maxim Orlovsky.
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

//! Lexer recognizes regular language of Parseltongue and creates token stream.

pub struct Lexeme<'src> {
    src: &'src str,
    // TODO: Use Span and Loc
    begin: usize,
    end: usize,
}

pub enum Token<'src> {
    Identifier(Lexeme<'src>),
    Punct(Lexeme<'src>),
    Attribute(AttrToken<'src>),
    Comment(CommentToken<'src>),
}

pub struct AttrToken<'src> {
    symbol: Lexeme<'src>,
    ident: Lexeme<'src>,
}

pub struct CommentToken<'src> {
    open: Lexeme<'src>,
    content: Lexeme<'src>,
    close: Option<Lexeme<'src>>,
}
