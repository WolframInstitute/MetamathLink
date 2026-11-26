---
Template: TechNote
Name: MetamathInTypeTheory
Title: Metamath in TypeTheory
Context: WolframInstitute`MetamathLink`
Paclet: WolframInstitute/MetamathLink
URI: WolframInstitute/MetamathLink/tutorial/MetamathInTypeTheory
Keywords: [Metamath, set.mm, demo0, MetamathImport, ZFC, higher-order abstract syntax, distinct variables, bundled theorems, variants, proof checking, axiom closure]
RelatedGuides: [MetamathLink]
---

A Metamath database is a list of statements: constants and variables, the syntax that builds formulas, axioms, and theorems whose proofs apply earlier statements by substitution. Its checker knows nothing of logic; the axioms carry it all. [MetamathToTypeTheory]() reads a database as statements of type theory instead, so that TypeTheory's kernel, which knows what a proposition and a proof are, checks every proof again. This tutorial imports demo0, the first example of the Metamath book, then the propositional calculus of set.mm, Metamath's database of ZFC, and then what set.mm's proof of 2 + 2 = 4 needs, all of it, down to its construction of the complex numbers.

MetamathToTypeTheory gives environments of TypeTheory, whose functions take them, and the databases this tutorial reads
are saved with the paclet:

```wl
Needs["WolframInstitute`TypeTheory`"]
data = FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data"}];
```

## A Database of Its Own Axioms

demo0 declares terms and formulas of its own, two axioms about equality and addition, and modus ponens. [MetamathImport]() reads it, MetamathLink's library verifying every proof as Metamath's verifiers do:

```wl
database = MetamathImport[File[FileNameJoin[{data, "demo0.mm"}]]]
```

<!-- => MetamathDatabase summary box: Theorems: 1, Axioms: 7 -->

Its theorem th1 says that t = t; its formula is a tree of the syntax axioms of demo0:

```wl
database["th1", "ParseTree"]
```

<!-- => Tree["weq", {Tree["t", None], Tree["t", None]}] -->

[MetamathToTypeTheory]() reads the database as statements of type theory, and TypeTheory's kernel checks every proof again:

```wl
demo = MetamathToTypeTheory[database]
```

<!-- => TypeTheoryEnvironment summary box: 284 constants -->

In the axiomatic semantics its typecode `term` is a type of its own, its syntax `t = r` a constant `weq` and its formulas propositions. The theorem th1 says that every term equals itself:

```wl
TypeTheoryType[TypeTheoryTerm["th1", demo]]
```

<!-- => ∀_{t∶term} weq[t, t] -->

Its proof is checked by TypeTheory's kernel from demo0's axioms, and from nothing else:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["th1", demo]]
```

<!-- => <|"term" -> "Signature", "weq" -> "Signature", "mp" -> "Proposition", "tpl" -> "Signature", "tze" -> "Signature", "a2" -> "Proposition", "wim" -> "Signature", "a1" -> "Proposition"|> -->

## The Propositional Calculus of set.mm

set.mm's propositional calculus goes into the ZFC semantics, where its connectives are TypeTheory's own: `->` is [Implies](), `-.` is [Not](), and a wff variable is a proposition.

```wl
propositional = MetamathToTypeTheory[File[FileNameJoin[{data, "setmm-propositional.mm"}]], "Through" -> "pm2.18"]
```

<!-- => TypeTheoryEnvironment summary box: 498 constants -->

set.mm's axioms are theorems of the environment it extends. `ax-1`, `ax-2` and `ax-mp` are intuitionistic, so a theorem that uses only them rests on no axiom:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["mpd", propositional]]
```

<!-- => <||> -->

`ax-3` is contraposition, which needs classical logic; pm2.18, Clavius' law, rests on the prelude's three axioms through it:

```wl
TypeTheoryType[TypeTheoryTerm["pm2.18", propositional]]
```

<!-- => ∀_{φ∶Prop} (¬ φ ⇒ φ) ⇒ φ -->

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["pm2.18", propositional]]
```

<!-- => <|"choice" -> "Signature", "quotientSoundness" -> "Proposition", "propositionalExtensionality" -> "Proposition"|> -->

## Quantifiers and Variables

set.mm's variables x, y, z range over sets, and a formula variable φ may mention any of them unless a distinct-variable condition, `$d x φ`, says it does not. In type theory a setvar is a bound variable of type `"Set"`, and φ is a function of the setvar variables it may mention: ax-gen, from φ infer ∀x φ, becomes a statement about every predicate φ of one set.

This part imports what 2 + 2 = 4 needs, from the statements of set.mm saved with the paclet: 3403 of them, and it takes under a minute.

```wl
arithmetic = MetamathToTypeTheory[File[FileNameJoin[{data, "setmm-2p2e4.wxf"}]], "Cone" -> "2p2e4"]
```

<!-- => TypeTheoryEnvironment summary box: 3801 constants -->

The generalization rule; its conclusion is closed over x like every statement, by a binder its body does not use, which
shows as an arrow from `"Set"`:

```wl
TypeTheoryType[TypeTheoryTerm["ax-gen", arithmetic]]
```

<!-- => ∀_{φ∶Set → Prop} (∀_{x∶Set} φ[x]) ⇒ Set → ∀_{x∶Set} φ[x] -->

In set.mm `x = y` is equality of the classes of x and y, and `x e. y` membership of classes: ax-7 is the transitivity of equality.

```wl
TypeTheoryType[TypeTheoryTerm["ax-7", arithmetic]]
```

<!-- => ∀_{x∶Set} ∀_{y∶Set} ∀_{z∶Set} setClass[x] == setClass[y] ⇒ setClass[x] == setClass[z] ⇒ setClass[y] == setClass[z] -->

Where no `$d` keeps two setvar variables apart, set.mm may apply an assertion with the same variable for both. In type theory that instance is another statement, a variant, which MetamathLink proves from the assertion's own proof with the variables merged. equid, x = x, applies ax7v1 so:

```wl
Select[Information[arithmetic, "Constants"], StringQ[#] && StringMatchQ[#, __ ~~ "{" ~~ __ ~~ ":=" ~~ __ ~~ "}"] &]
```

<!-- => {"ax-7{z:=y}", "ax7v{z:=y}", "ax7v1{z:=y}", "ax-7{z:=x}", ..., "wsb{t:=x}", ..., "df-clab{y:=x}", ...}: about 70 -->

## 2 + 2 = 4

set.mm's 2 + 2 = 4 is a statement about classes, the numbers and the operation `+` being classes built from sets:

```wl
TypeTheoryType[TypeTheoryTerm["2p2e4", arithmetic]]
```

<!-- => co[c2, c2, caddc] == c4 -->

set.mm states the axioms of the complex numbers as axioms after proving each from its construction of them; MetamathLink proves each axiom by that theorem. So 2 + 2 = 4 rests on no axiom of set.mm, only on the prelude's:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["2p2e4", arithmetic]]
```

<!-- => <|"propositionalExtensionality" -> "Proposition", "choice" -> "Signature", "quotientSoundness" -> "Proposition"|> -->

The environment can be saved in TypeTheory's Format 3, which reads its declarations lazily when it is opened:

```wl
Export[FileNameJoin[{$TemporaryDirectory, "2p2e4.tte"}], arithmetic]
```

<!-- => File[".../2p2e4.tte"] -->
