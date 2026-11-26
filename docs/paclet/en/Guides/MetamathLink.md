---
Template: Guide
Name: MetamathLink
Title: MetamathLink
Context: WolframInstitute`MetamathLink`
Paclet: WolframInstitute/MetamathLink
URI: WolframInstitute/MetamathLink/guide/MetamathLink
Description: Metamath databases in the TypeTheory proof engine, every proof checked again by TypeTheory's kernel.
Keywords: [Metamath, set.mm, ZFC, set theory, type theory, proof translation, proof checking]
RelatedTutorials: [MetamathInTypeTheory]
Links: ["[TypeTheory, the proof engine whose kernel checks every proof](https://www.wolframcloud.com/obj/wolframinstitute/TypeTheory)", "[MetamathImport of the Wolfram Function Repository](https://resources.wolframcloud.com/FunctionRepository/resources/MetamathImport)", "[MetamathLink on GitHub](https://github.com/WolframInstitute/MetamathLink)"]
---

## Abstract

<code>WolframInstitute\`MetamathLink\`</code> brings Metamath databases into TypeTheory, a proof engine for the Calculus of Inductive Constructions written in the Wolfram Language. A Metamath database is a list of axioms and theorems whose proofs are sequences of substitutions; [MetamathImport]() reads one with MetamathLink's library, a Rust library on metamath-knife's, which verifies every proof and parses every statement, and [MetamathToTypeTheory]() translates each statement into a statement of type theory and each proof into a proof term, and TypeTheory's kernel checks every one again, so that neither Metamath's checker nor the translation is trusted. set.mm, Metamath's database of ZFC, goes into <code>[TypeTheoryEnvironment]()["ZFC"]</code>, a model of ZFC in which every axiom of set.mm is a theorem: its 2 + 2 = 4 rests on the prelude's three axioms alone.

## Functions

### Metamath databases

- [MetamathImport]() reads a database into a [MetamathDatabase](), every proof verified and every statement parsed by MetamathLink's library
- [MetamathDatabase]() a database: its statements, parse trees, proofs and the cones of its theorems
- [MetamathVerify]() verifies every proof of a database, as metamath-knife does
- [MetamathImport](https://resources.wolframcloud.com/FunctionRepository/resources/MetamathImport) of the Wolfram Function Repository reads a database into a MetamathObject, which [MetamathImport]() and [MetamathToTypeTheory]() take

### Into TypeTheory

- [MetamathToTypeTheory]() imports a Metamath database, or what some of its theorems need, into a [TypeTheoryEnvironment](), every proof checked again by TypeTheory's kernel

### In TypeTheory

- [TypeTheoryEnvironment]() the environment of the imported statements, an extension of the prelude or of the ZFC environment
- [TypeTheoryAxiomClosure]() the axioms an imported theorem rests on
- [TypeTheoryCheck]() checks every constant of an environment again
