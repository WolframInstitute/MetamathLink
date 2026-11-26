---
Template: Symbol
Name: MetamathDatabase
Context: WolframInstitute`MetamathLink`
Paclet: WolframInstitute/MetamathLink
URI: WolframInstitute/MetamathLink/ref/MetamathDatabase
Keywords: [Metamath, database, statement, parse tree, proof, normal proof, cone, set.mm]
SeeAlso: [MetamathImport, MetamathVerify, MetamathToTypeTheory, Tree]
RelatedGuides: [MetamathLink]
RelatedTutorials: [MetamathInTypeTheory]
---

## Usage

<code>[MetamathDatabase]()[...]</code> is a Metamath database that [MetamathImport]() read.

<code>*database*[*label*]</code> gives the statement *label*.

<code>*database*[*label*, "ParseTree"]</code> gives the parse tree of the formula of the statement *label* as a [Tree]().

<code>*database*[*label*, "Proof"]</code> gives the proof of the theorem *label* as Metamath's normal proof.

<code>*database*[{*label1*, *label2*, ...}, "Cone"]</code> gives the statements the assertions *labeli* need, in the order of the database.

## Details & Options

- A statement is an association: its `"Kind"`, `"Axiom"`, `"Theorem"`, `"Floating"` or `"Essential"`; its `"Label"`, `"Typecode"` and `"Symbols"`; for an assertion its mandatory floating hypotheses `{label, typecode, variable}`, essential hypotheses and disjoint variables `{variable, variable}`, and for a theorem its proof as the file has it.
- A parse tree has a syntax axiom at each node, over its arguments in the order of the axiom's floating hypotheses, and a variable at each leaf.
- Metamath's normal proof is the labels of the proof in order, each applying the statement it names to the steps before it: a step a compressed proof saves and uses again is written out again.
- The cone of some assertions is what their import into TypeTheory takes: the assertions their proofs apply, the syntax of every statement with the axiom that defines it, and for an axiom ax-NAME an earlier theorem axNAME that proves it.
- [Information]()`[`*database*`, `*property*`]` gives these properties:

| property | |
|---|---|
| `"Axioms"` | the labels of the axioms, syntax axioms included |
| `"Theorems"` | the labels of the theorems |
| `"Hypotheses"` | the labels of the floating and essential hypotheses |
| `"Typecodes"` | the typecodes, in the order the database declares them |
| `"Source"` | the file the database was read from |

- [Keys]() gives every label in the order of the database, [Length]() their number, and [Normal]() the statements by label.

## Basic Examples

```wl
demo = MetamathImport[File[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "demo0.mm"}]]]
```

<!-- => MetamathDatabase summary box: Theorems: 1, Axioms: 7 -->

The parse tree of th1, t = t:

```wl
demo["th1", "ParseTree"]
```

<!-- => Tree["weq", {Tree["t", None], Tree["t", None]}] -->

Its proof:

```wl
demo["th1", "Proof"]
```

<!-- => {"tt", "tze", "tpl", "tt", "weq", ..., "a1", "mp", "mp"} -->

What its import takes:

```wl
demo["th1", "Cone"]
```

<!-- => {"tt", "tr", "ts", "wp", "wq", "tze", "tpl", "weq", "wim", "a1", "a2", "mp", "th1"}: syntax, axioms and th1 -->

## Scope

set.mm's propositional calculus:

```wl
propositional = MetamathImport[File[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "setmm-propositional.mm"}]]]
```

<!-- => MetamathDatabase summary box -->

Its statements and theorems:

```wl
{Length[propositional], Length[Information[propositional, "Theorems"]]}
```

<!-- => {3223, ...} -->

The parse tree of pm2.43, (φ → (φ → ψ)) → (φ → ψ):

```wl
propositional["pm2.43", "ParseTree"]
```

<!-- => Tree["wi", {Tree["wi", {Tree["ph", None], Tree["wi", {...}]}], Tree["wi", {...}]}] -->

Its compressed proof, written out as a normal proof:

```wl
propositional["pm2.43", "Proof"]
```

<!-- => {"wph", "wps", ...}: ending in its last step -->

## Properties & Relations

The labels of the database are its keys, and its statements its values:

```wl
Take[Keys[propositional], 5]
```

<!-- => {"wph", "wps", "wch", "wth", "wta"} -->

[MetamathToTypeTheory]() imports the cone of a label:

```wl
MetamathToTypeTheory[demo, "th1"]
```

<!-- => TypeTheoryEnvironment summary box -->

## Possible Issues

An axiom has no proof:

```wl
demo["a1", "Proof"]
```

<!-- => Failure["NoProof", ...] -->
