---
Template: Symbol
Name: MetamathToTypeTheory
Context: WolframInstitute`MetamathLink`
Paclet: WolframInstitute/MetamathLink
URI: WolframInstitute/MetamathLink/ref/MetamathToTypeTheory
Keywords: [Metamath, set.mm, import, translation, proof checking, ZFC, demo0, axiom closure]
SeeAlso: [TypeTheoryEnvironment, TypeTheoryAxiomClosure, TypeTheoryCheck, TypeTheoryType]
RelatedGuides: [MetamathLink]
RelatedTutorials: [MetamathInTypeTheory]
---

## Usage

<code>[MetamathToTypeTheory]()[[File]()[*path*]]</code> imports the Metamath database in the file *path* into a [TypeTheoryEnvironment](), every proof checked again by TypeTheory's kernel.

<code>[MetamathToTypeTheory]()[*object*]</code> imports the MetamathObject that the function resource MetamathImport gives.

<code>[MetamathToTypeTheory]()[[File]()["*database*.wxf"]]</code> imports a database MetamathLink saved, with no network.

## Details & Options

- Each statement of the database, in order, becomes a declaration: a syntax axiom with a meaning in the semantics adds nothing, a defining axiom adds a definition and a theorem proved by reflexivity, an axiom is proved as the semantics proves it, and a theorem is proved by the translation of its proof. TypeTheory's kernel checks each one as it is added.
- Statements are in higher-order abstract syntax. A setvar variable is a bound variable; a wff or class variable is a parameter, a function of the setvar variables it may depend on, those it has no `$d` with. Each hypothesis and the conclusion are closed over the setvar variables, so `ax-gen`, from φ infer ∀x φ, is <code>[ForAll]()[{φ}, [Implies]()[[ForAll]()[{x}, φ[x]], [ForAll]()[{x}, [ForAll]()[{x}, φ[x]]]]]</code>.
- An assertion with no `$d` between two setvar variables may be applied with the same variable for both. That instance is another statement in higher-order abstract syntax, its variant, named <code>*label*{*z*:=*y*}</code>: a theorem's variant is proved by its own proof with the variables merged, a defining axiom's by reflexivity, and an axiom's by the semantics.
- MetamathToTypeTheory takes these options:

| option | default | |
|---|---|---|
| `"Semantics"` | [Automatic]() | `"Axiomatic"` or `"ZFC"`; [Automatic]() is `"ZFC"` for a database with set.mm's setvar typecode |
| `"Through"` | [All]() | the last statement to import |
| `"Cone"` | [None]() | a label or a list of labels: import only what they need |
| `"UnprovedAxioms"` | `"Fail"` | `"Assume"` declares an axiom the semantics does not prove as an axiom of the environment |
| [Method]() | `"Core"` | `"Core"` gives TypeTheory's kernel its own form of terms; `"Surface"` elaborates surface syntax first |

- In the axiomatic semantics wff is Prop, every other typecode a declared type, every syntax axiom a declared constant and every logical axiom an axiom of the environment.
- In the ZFC semantics the database is set.mm over <code>[TypeTheoryEnvironment]()["ZFC"]</code>, Aczel's model of ZFC, extended with set.mm's axioms as theorems under their labels: setvar is `"Set"`, class is `"Class"`, and the primitive syntax denotes the connectives, the quantifiers and the class vocabulary of the model. An axiom `ax-NAME` that set.mm proves first as a theorem `axNAME`, as it does the axioms of the complex numbers, is proved by it.
- An import that fails gives a [Failure]() with the label of the statement, as a translation that does not check, `"KernelRejected"`, or a proof that does not prove its statement, `"ProofMismatch"`.

## Basic Examples

demo0, the example database of the Metamath book, in the axiomatic semantics:

```wl
demo = MetamathToTypeTheory[File[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "demo0.mm"}]]]
```

<!-- => TypeTheoryEnvironment summary box -->

The statement of th1, t = t for every term t:

```wl
TypeTheoryType[TypeTheoryTerm["th1", demo]]
```

<!-- => ∀_{t∶term} weq[t, t] -->

It rests on demo0's own axioms:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["th1", demo]]
```

<!-- => closure -->

## Scope

set.mm's propositional calculus through a label, in the ZFC semantics:

```wl
propositional = MetamathToTypeTheory[File[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "setmm-propositional.mm"}]], "Through" -> "pm2.43"]
```

<!-- => TypeTheoryEnvironment summary box -->

set.mm's wff variables are propositions:

```wl
TypeTheoryType[TypeTheoryTerm["pm2.43", propositional]]
```

<!-- => ∀_{φ∶Prop} ∀_{ψ∶Prop} (φ ⇒ φ ⇒ ψ) ⇒ φ ⇒ ψ -->

A theorem whose proof uses only the intuitionistic axioms rests on no axiom:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["mpd", propositional]]
```

<!-- => <||> -->

---

Only what 2 + 2 = 4 needs, from the statements of set.mm saved with the paclet:

```wl
arithmetic = MetamathToTypeTheory[File[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "setmm-2p2e4.wxf"}]], "Cone" -> "2p2e4"]
```

<!-- => TypeTheoryEnvironment summary box -->

```wl
TypeTheoryType[TypeTheoryTerm["2p2e4", arithmetic]]
```

<!-- => co[c2, c2, caddc] == c4 -->

It rests on the prelude's three axioms:

```wl
TypeTheoryAxiomClosure[TypeTheoryTerm["2p2e4", arithmetic]]
```

<!-- => <|propositionalExtensionality, choice, quotientSoundness|> -->

## Possible Issues

A proof that does not prove its statement stops the import at that statement:

```wl
MetamathToTypeTheory[ResourceFunction["MetamathImport"][StringReplace[ReadString[FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Data", "demo0.mm"}]], "th1 $p |- t = t" -> "th1 $p |- t = r"]]]
```

<!-- => Failure["ProofMismatch", ...] -->
