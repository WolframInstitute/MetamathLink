---
Template: Symbol
Name: MetamathVerify
Context: WolframInstitute`MetamathLink`
Paclet: WolframInstitute/MetamathLink
URI: WolframInstitute/MetamathLink/ref/MetamathVerify
Keywords: [Metamath, verify, verifier, proof checking, metamath-knife, set.mm, Success, Failure]
SeeAlso: [MetamathImport, MetamathDatabase, MetamathToTypeTheory]
RelatedGuides: [MetamathLink]
RelatedTutorials: [MetamathInTypeTheory]
---

## Usage

<code>[MetamathVerify]()[[File]()[*path*]]</code> verifies every proof of the Metamath database in the file *path* with MetamathLink's library, and gives a [Success]() or a [Failure]().

<code>[MetamathVerify]()[*database*]</code> verifies the file the [MetamathDatabase]() *database* was read from.

## Details & Options

- The library verifies as metamath-knife does, the fastest Metamath verifier, on metamath-rs, its library: every proof, the scopes and the distinct variable conditions. All of set.mm is verified in about 1 s.
- A database that verifies gives `Success["Verified", ...]`, whose `"Axioms"`, `"Theorems"` and `"Hypotheses"` are the numbers of each. One that does not gives `Failure["InvalidDatabase", ...]`, whose `"Diagnostics"` are the verifier's first errors as text.
- MetamathVerify reads nothing into the kernel: it gives no statements. [MetamathImport]() verifies the same way and gives the database.
- MetamathVerify checks a database as Metamath does, by substitution. [MetamathToTypeTheory]() checks its proofs again in TypeTheory's kernel, as proofs of type theory.

## Basic Examples

demo0, the example database of the Metamath book:

```wl
MetamathVerify[File[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "demo0.mm"}]]]
```

<!-- => Success["Verified", ...]: demo0.mm verifies: 1 theorems from 7 axioms -->

## Scope

set.mm's propositional calculus, and the number of its theorems:

```wl
MetamathVerify[File[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "setmm-propositional.mm"}]]]["Theorems"]
```

<!-- => the number of its theorems -->

---

A [MetamathDatabase]() is verified from its file:

```wl
MetamathVerify[MetamathImport[File[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "demo0.mm"}]]]]
```

<!-- => Success["Verified", ...] -->

## Possible Issues

A proof that does not prove its statement fails, with the verifier's diagnostic:

```wl
broken = FileNameJoin[{$TemporaryDirectory, "broken-demo0.mm"}];
Export[broken, StringReplace[ReadString[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "demo0.mm"}]], "th1 $p |- t = t" -> "th1 $p |- t = r"], "Text"];
MetamathVerify[File[broken]]
```

<!-- => Failure["InvalidDatabase", ...] -->

```wl
MetamathVerify[File[broken]]["Diagnostics"]
```

<!-- => {"error: ... th1 ..."} -->
