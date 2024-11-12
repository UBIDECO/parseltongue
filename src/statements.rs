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
use core::fmt::{self, Debug, Display, Formatter};

use crate::{Ident, LexTy, Lexeme, Section, Source, Span};

#[derive(Clone, Eq, PartialEq)]
pub struct Module<'src> {
    pub name: Option<&'src str>,
    pub declarations: Vec<Decl<'src>>,
}

impl<'src> Debug for Module<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "-- Module {}", self.name.unwrap_or("<unnamed>"))?;
        for decl in &self.declarations {
            Debug::fmt(decl, f)?;
        }
        Ok(())
    }
}

impl<'src> Display for Module<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for decl in &self.declarations {
            Display::fmt(decl, f)?;
        }
        Ok(())
    }
}

#[derive(Clone, Eq, PartialEq)]
pub enum Statement<'src> {
    Decl(Decl<'src>),
    Expr(Section<'src>),
}

impl<'src> Debug for Statement<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Decl(decl) => {
                writeln!(f, "-- Declaration spanning {}", decl.span())?;
                Debug::fmt(decl, f)
            }
            Statement::Expr(expr) => {
                writeln!(f, "-- Expression spanning {}", expr.span)?;
                Debug::fmt(expr, f)
            }
        }
    }
}

impl<'src> Display for Statement<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Decl(decl) => Display::fmt(decl, f),
            Statement::Expr(expr) => Display::fmt(expr, f),
        }
    }
}

impl<'src> Statement<'src> {
    pub fn parse(source: &'src Source, lexeme: Lexeme) -> Self {
        let term = source.section(lexeme.span);
        match lexeme.ty {
            LexTy::Code => Decl::parse(term)
                .map(Self::Decl)
                .unwrap_or(Self::Expr(term)),
            LexTy::Brackets(_) => Self::Expr(term),
            LexTy::Quotes(_) => Self::Expr(term),
            LexTy::Comment => unreachable!(),
        }
    }

    pub fn span(&self) -> Span {
        match self {
            Statement::Decl(decl) => decl.span(),
            Statement::Expr(expr) => expr.span,
        }
    }
}

#[derive(Clone, Eq, PartialEq)]
pub struct Decl<'src> {
    pub decl: Ident<'src>,
    pub name: Ident<'src>,
    pub params: Option<Section<'src>>,
    pub body: Vec<Statement<'src>>,
}

impl<'src> Debug for Decl<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result { todo!() }
}

impl<'src> Display for Decl<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.decl, self.name)?;
        if let Some(params) = self.params {
            write!(f, ": {params}")?;
        }
        writeln!(f)?;
        for body in &self.body {
            Display::fmt(body, f)?;
        }
        Ok(())
    }
}

impl<'src> Decl<'src> {
    pub fn parse(mut section: Section<'src>) -> Option<Self> {
        let decl = section.pop_ident()?;
        let name = section.pop_ident()?;
        let params = if section.pop_token(":").is_some() {
            if section.is_empty() {
                return None;
            }
            None
        } else {
            Some(section.trim())
        };
        Some(Decl { decl, name, params, body: vec![] })
    }

    pub fn span(&self) -> Span {
        let mut span = self.decl.span;
        span.extend(self.name.span);
        if let Some(params) = self.params {
            span.extend(params.span);
        }
        if let Some(body) = self.body.last() {
            span.extend(body.span());
        }
        span
    }
}
