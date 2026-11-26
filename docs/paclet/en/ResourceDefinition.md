---
Template: Paclet
ResourceType: Paclet
Name: WolframInstitute/MetamathLink
Context: WolframInstitute`MetamathLink`
Paclet: WolframInstitute/MetamathLink
Description: Metamath databases in the TypeTheory proof engine: set.mm's theorems checked by TypeTheory's kernel over a model of ZFC
ContributedBy: Nik Murzin
Keywords: [Metamath, set.mm, ZFC, set theory, type theory, proof translation, proof checking, formal mathematics]
MainGuide: Documentation/English/Guides/MetamathLink.nb
License: MIT
WolframVersion: 15.0+
Categories: [Higher Mathematical Computation, Symbolic & Numeric Computation]
Sources: ["Norman Megill, David A. Wheeler, *Metamath: A Computer Language for Mathematical Proofs*, Lulu Press, 2019", "Peter Aczel, *The Type Theoretic Interpretation of Constructive Set Theory*, Logic Colloquium '77, 1978", "Mario Carneiro, *Models for Metamath*, CICM 2016"]
SourceControlURL: https://github.com/WolframInstitute/MetamathLink
Links: ["[MetamathLink on GitHub](https://github.com/WolframInstitute/MetamathLink)", "[MetamathImport of the Wolfram Function Repository, which reads a Metamath database into a MetamathObject](https://resources.wolframcloud.com/FunctionRepository/resources/MetamathImport)", "[TypeTheory, the proof engine whose kernel checks every proof](https://www.wolframcloud.com/obj/wolframinstitute/TypeTheory)", "[The Metamath home page and set.mm](https://us.metamath.org)"]
---

## Details & Options

- [MetamathToTypeTheory]() imports a Metamath database into a [TypeTheoryEnvironment](): each statement becomes a statement of type theory, each proof a proof term, and TypeTheory's kernel checks every one again. Neither Metamath's checker nor the translation is trusted.
- [MetamathImport]() reads a database into a [MetamathDatabase]() with MetamathLink's library, a Rust library on metamath-rs, the library of metamath-knife: every proof verified and every statement parsed, all of set.mm in about 2 s. [MetamathVerify]() verifies a database alone. Both take the MetamathObject of [MetamathImport](https://resources.wolframcloud.com/FunctionRepository/resources/MetamathImport) of the Wolfram Function Repository, as [MetamathToTypeTheory]() does.
- The **axiomatic** semantics takes any database: wff is Prop, every other typecode a declared type, every syntax axiom a declared constant and every logical axiom an axiom of the environment.
- The **ZFC** semantics takes set.mm over <code>[TypeTheoryEnvironment]()["ZFC"]</code>, Aczel's model of ZFC: every axiom of set.mm is a theorem there, so an imported theorem rests on the prelude's propositional extensionality, quotient soundness and choice, or less.
- Statements are in higher-order abstract syntax: a setvar variable is a bound variable of type `"Set"`, a wff or class variable a function of the setvar variables it may depend on.

## Usage

[MetamathImport]() reads a database, verified and parsed, into a [MetamathDatabase](); [MetamathVerify]() verifies one; [MetamathToTypeTheory]() imports a database, all of it, through a label, or the statements some theorems need.

## Basic Examples

MetamathToTypeTheory gives environments of TypeTheory, whose functions take them:

```wl
Needs["WolframInstitute`TypeTheory`"]
```

demo0, the example of the Metamath book, read and verified:

```wl
database = MetamathImport[File[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "demo0.mm"}]]]
```

<!-- => MetamathDatabase summary box: Theorems: 1, Axioms: 7 -->

In the axiomatic semantics:

```wl
demo = MetamathToTypeTheory[File[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "demo0.mm"}]]]
```

<!-- => TypeTheoryEnvironment summary box: 284 constants -->

Its theorem th1, t = t for every term t:

```wl
TypeTheoryType[TypeTheoryTerm["th1", demo]]
```

<!-- => ∀_{t∶term} weq[t, t] -->
