# Parseltongue: framework for declarative domain-specific languages

![Build](https://github.com/UBIDECO/parseltongue/workflows/Build/badge.svg)
![Tests](https://github.com/UBIDECO/parseltongue/workflows/Tests/badge.svg)
[![codecov](https://codecov.io/gh/UBIDECO/parseltongue/branch/master/graph/badge.svg)](https://codecov.io/gh/UBIDECO/parseltongue)

[![crates.io](https://img.shields.io/crates/v/parseltongue)](https://crates.io/crates/parseltongue)
[![Docs](https://docs.rs/parseltongue/badge.svg)](https://docs.rs/parseltongue)
[![License](https://img.shields.io/crates/l/parseltongue)](./LICENSE)

## What is it

**Parseltongue** is a framework for creating declarative-style domain-specific programming and
markup languages. This repository provides a rust implementation of the parser, which can be used
as a dependency in domain-specific languages made with Parseltongue.

## Syntax

The language is indentation-based.

Comments: single-line comments `--` and multi-line from `{-` to `-}`; following `-}` there must be
no content in the line other than whitespace or other comment. Multiline comments can be nested, but
brackets and quotes within the quotes are ignored (thus, `-}` inside a quote, will terminate a
multi-line comment).

All language *statements* span at least one or more lines and are either *declarations* or
*expressions*.

Declarations have a form of `decl name: params`, followed by a body starting the newline with an
increased indent, and lasting until the indentation is omitted. The parameters and the body of a
declaration may be empty.

Declaration verb, name, and colon `:` symbol must be always put on the same line. If the last
non-whitespace symbol in a declaration line is comma (`,`), than it is assumed that the next
non-empty line contains the continuation of the declaration parameters, no matter the indentation
(indentation is omitted). Also, parser takes into account the use of brackets and quotes, and keep
parsing lines as parameters as long as all brackets and quote counters are down to zero.
Thus, parameters may span multiple lines, as long as each one of them is terminated with a comma,
or there are non-closed brackets or quotes.

Parseltongue parser recognizes the following types of brackets:

- parenthesis `(`, `)`;
- square brackets `[`, `]`;
- braces`{`, `}`.

Parseltongue parser recognizes the following types of quotations:

- single-quotes `'`,
- double-quotes `"`,
- triple double-quotes `"""`
- single backqoutes `` ` ``,
- triple backquotes ` ``` `

Parser counts quotes and keeps all whitespace and newline characters within them (thus, all types of
quotes can be multi-line). The parser takes into account only external quotes and doesn't count any
quotes which are used inside. The parser also will skip a closing quote if it is follows a backslash
character `\`.

All lines which are not parsed as a declaration or a part of a declaration are considered to be
expressions. Expressions are opaque for the Parseltongue parser and are forwarded as is (including
internal whitespacing) to the DSL language parser. Each independent line is treated as a separate
expression, unless there are non-closed brackets, quotes or a line ends with comma (`,`).

## Known languages

List of languages made with Parseltongue (potentially incomplete):

- [Vesper]: structured markup language to define schema-less data;
- [Strict types]: declarative language for defining generalized algebraic data types;
- [STON]: Strict-typed object notation;
- [Cation]: functional general-purpose programming language made with category theory in mind;
- [StingerJet]: language for defining deterministic Bitcoin wallet descriptors;
- [Contractum]: language for writing smart contracts.

## License

    Designed in 2021-2025 by Dr Maxim Orlovsky <orlovsky@ubideco.org>
    Written in 2024-2025 by Dr Maxim Orlovsky <orlovsky@ubideco.org>
    
    Copyright (C) 2021-2025 Laboratories for Ubiquitous Deterministic Computing (UBIDECO),
                            Institute for Distributed and Cognitive Systems (InDCS), Switzerland.
    Copyright (C) 2021-2025 Dr Maxim Orlovsky.
    All rights under the above copyrights are reserved.

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
in compliance with the License. You may obtain a copy of the License at
<http://www.apache.org/licenses/LICENSE-2.0>.

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License.

[Vesper]: https://github.com/UBIDECO/vesper

[Strict types]: https://strict-types.org

[STON]: https://strict-types.org/STON

[Cation]: https://cation-lang.org

[Contractum]: https://contractum.org

[StingerJet]: https://lnp-bp.org/StingerJet
