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
Links: ["[MetamathLink on GitHub](https://github.com/WolframInstitute/MetamathLink)", "[TypeTheory, the proof engine whose kernel checks every proof](https://www.wolframcloud.com/obj/wolframinstitute/TypeTheory)", "[The Metamath home page and set.mm](https://us.metamath.org)"]
---

## Details & Options

- [MetamathToTypeTheory]() imports a Metamath database into a [TypeTheoryEnvironment](): each statement becomes a statement of type theory, each proof a proof term, and TypeTheory's kernel checks every one again. Neither Metamath's checker nor the translation is trusted.
- It reads a database with the function resource MetamathImport, parses its statements with a grammar built from its syntax axioms, and decodes its compressed proofs itself.
- The **axiomatic** semantics takes any database: wff is Prop, every other typecode a declared type, every syntax axiom a declared constant and every logical axiom an axiom of the environment.
- The **ZFC** semantics takes set.mm over <code>[TypeTheoryEnvironment]()["ZFC"]</code>, Aczel's model of ZFC: every axiom of set.mm is a theorem there, so an imported theorem rests on the prelude's propositional extensionality, quotient soundness and choice, or less.
- Statements are in higher-order abstract syntax: a setvar variable is a bound variable of type `"Set"`, a wff or class variable a function of the setvar variables it may depend on.

## Usage

[MetamathToTypeTheory]() imports a database, all of it, through a label, or the statements some theorems need.

## Basic Examples

demo0, the example of the Metamath book, in the axiomatic semantics:

```wl
demo = MetamathToTypeTheory[File[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "demo0.mm"}]]]
```

<!-- => TypeTheoryEnvironment summary box -->

Its theorem th1, t = t for every term t:

```wl
TypeTheoryType[TypeTheoryTerm["th1", demo]]
```

<!-- => ∀_{t∶term} weq[t, t] -->
