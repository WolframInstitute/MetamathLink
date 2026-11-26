---
Template: Symbol
Name: MetamathImport
Context: WolframInstitute`MetamathLink`
Paclet: WolframInstitute/MetamathLink
URI: WolframInstitute/MetamathLink/ref/MetamathImport
Keywords: [Metamath, set.mm, import, read, verify, parse, database, demo0, metamath-knife]
SeeAlso: [MetamathDatabase, MetamathVerify, MetamathToTypeTheory]
RelatedGuides: [MetamathLink]
RelatedTutorials: [MetamathInTypeTheory]
---

## Usage

<code>[MetamathImport]()[[File]()[*path*]]</code> reads the Metamath database in the file *path*, every proof verified and every statement parsed by MetamathLink's library, and gives a [MetamathDatabase]().

<code>[MetamathImport]()[[File]()["*database*.wxf"]]</code> reads a database MetamathLink saved.

<code>[MetamathImport]()[*object*]</code> reads the MetamathObject that the function resource MetamathImport gives.

## Details & Options

- MetamathLink's library is a Rust library on metamath-rs, the library of metamath-knife, the fastest Metamath verifier: it reads the database, verifies every proof, and parses every statement with the grammar of the database's syntax axioms. All of set.mm is read, verified and parsed in about 2 s.
- A statement the library's grammar does not parse, as in a database whose grammar is ambiguous where its parser looks ahead, is parsed by MetamathLink's own parser when its parse tree is asked for.
- A database that does not verify gives `Failure["InvalidDatabase", ...]`, with the verifier's diagnostics under `"Diagnostics"`.
- On a platform for which MetamathLink has no library, the file is read by the function resource MetamathImport, which needs the network, and is not verified.
- MetamathImport of MetamathLink is not the function resource of the same name, which gives a MetamathObject; MetamathImport takes one.

## Basic Examples

demo0, the example database of the Metamath book:

```wl
demo = MetamathImport[File[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "demo0.mm"}]]]
```

<!-- => MetamathDatabase summary box: Theorems: 1, Axioms: 7 -->

Its theorems:

```wl
Information[demo, "Theorems"]
```

<!-- => {"th1"} -->

The statement of th1:

```wl
demo["th1"]
```

<!-- => <|"Kind" -> "Theorem", "Label" -> "th1", "Typecode" -> "|-", "Symbols" -> {"t", "=", "t"}, "Disjoint" -> {}, "Floating" -> {{"tt", "term", "t"}}, "Essential" -> {}, "Proof" -> {...}|> -->

## Scope

set.mm's propositional calculus:

```wl
propositional = MetamathImport[File[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "setmm-propositional.mm"}]]]
```

<!-- => MetamathDatabase summary box -->

Its typecodes, in the order the database declares them:

```wl
Information[propositional, "Typecodes"]
```

<!-- => {"wff", "|-", "setvar", "class"} -->

---

A database MetamathLink saved, the statements of set.mm that 2 + 2 = 4 needs, with their parse trees:

```wl
arithmetic = MetamathImport[File[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "setmm-2p2e4.wxf"}]]]
```

<!-- => MetamathDatabase summary box -->

```wl
arithmetic["2p2e4", "ParseTree"]
```

<!-- => Tree["wceq", {Tree["co", {...}], Tree["c4", {}]}] -->

## Possible Issues

A database whose proof does not verify is refused, with the verifier's diagnostics:

```wl
broken = FileNameJoin[{$TemporaryDirectory, "broken-demo0.mm"}];
Export[broken, StringReplace[ReadString[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "demo0.mm"}]], "th1 $p |- t = t" -> "th1 $p |- t = r"], "Text"];
MetamathImport[File[broken]]
```

<!-- => Failure["InvalidDatabase", ...]: does not verify, 1 error -->
