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

#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct Module<'src> {
    pub source: &'src str,
    pub lines: Vec<&'src str>,
    pub decls: Vec<Decl<'src>>,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Statement<'src> {
    Decl(Decl<'src>),
    Expr(&'src str),
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Decl<'src> {
    pub decl: &'src str,
    pub name: &'src str,
    pub params: Vec<&'src str>,
    pub body: Vec<Statement<'src>>,
}
