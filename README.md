# MetamathLink

Metamath databases in [TypeTheory](https://github.com/WolframInstitute/TypeTheory), a proof engine for the Calculus of
Inductive Constructions in pure Wolfram Language. `MetamathToTypeTheory` reads a database with
`ResourceFunction["MetamathImport"]`, translates each statement into a statement of type theory and each proof into a proof
term, and TypeTheory's kernel checks every one again: Metamath's checker is not trusted, nor is this translation.

```wl
PacletDirectoryLoad["MetamathLink"]
Needs["WolframInstitute`TypeTheory`"]
Needs["WolframInstitute`MetamathLink`"]

env = MetamathToTypeTheory[File["MetamathLink/Data/demo0.mm"]]
TypeTheoryType[TypeTheoryTerm["th1", env]]               (* ∀ t : term, weq[t, t] *)
TypeTheoryAxiomClosure[TypeTheoryTerm["th1", env]]       (* demo0's own axioms *)
Export["demo0.tte", env]                                 (* TypeTheory's Format 3 *)
```

## Two semantics

- **Axiomatic**, any database: `wff` is `Prop`, every other typecode a declared type, every syntax axiom a declared
  constant and every logical axiom an axiom of the environment (`demo0.mm`).
- **ZFC**, set.mm over `TypeTheoryEnvironment["ZFC"]`, Aczel's model of ZFC in TypeTheory's library, with set.mm's axioms
  proved over it under their labels (`SetmmLibrary.wl`): `setvar` is `"Set"`,
  `class` is `"Class"`, `wff` is `Prop`. The primitive syntax denotes the connectives (native `Implies`, `And`, `Or`,
  `Equivalent`, `ForAll`, `Exists`) and the class vocabulary of the model (`"setClass"`, `"classElement"`,
  `"classAbstraction"`, `==`); every other syntax axiom is defined by its `df-` axiom, which becomes a theorem by
  reflexivity; every axiom is a theorem: of the library under its label (`ax-mp` ... `ax-ac`), or set.mm's own theorem
  `axNAME` for `ax-NAME` when set.mm proves it first (the complex numbers, `ax-inf2`). The axiom closure of an imported
  theorem is the prelude's propositional extensionality, quotient soundness and choice, or less.

## The translation

Statements are in higher-order abstract syntax. A setvar variable is a bound variable of type `"Set"`; a wff or class
variable is a parameter, a function of the setvar variables of the frame it has no `$d` with; each hypothesis and the
conclusion are closed over the setvar variables:

    ForAll[{φ, ...}, Implies[ForAll[setvars, e1], ... ForAll[setvars, conclusion]]]

A proof step is a term in the proof's setvar variables; an application of an assertion binds the images of its setvar
variables again around the steps of its hypotheses, so each holds for every value, as the assertion asks. Steps the
compressed proof saves are let-bound closures; dummy variables are let-bound to an inhabitant.

set.mm allows an assertion with no `$d` between two setvar variables to be applied with the same variable for both. In
higher-order abstract syntax that instance is another statement, its *variant* `A{z:=y}`: MetamathLink proves a theorem's
variant by its own proof with the variables merged, a defining axiom's by reflexivity of the constructor's variant, and
the bundled axioms' (`ax-6` ... `ax-13`, `df-clab`) by proofs the semantics gives. A syntax axiom used with the same
variable twice, `[ x / x ] ph`, gets the variant of its definition the same way.

Declarations reach TypeTheory's kernel as core terms, its own locally nameless form, as LeanLink's do
(`Method -> "Surface"` elaborates surface syntax instead, five times slower).

## Files

| file | |
|---|---|
| `Kernel/Database.wl` | the statements of a MetamathObject, the grammar of the syntax axioms and the parser, compressed proofs |
| `Kernel/Translation.wl` | frames, statements and proof terms, definitions, variants |
| `Kernel/Semantics.wl` | the Axiomatic and ZFC semantics |
| `Kernel/SetmmLibrary.wl` | set.mm's axioms as theorems over the ZFC environment, with no axiom of their own |
| `Kernel/Core.wl` | the terms as TypeTheory's core terms |
| `Kernel/Import.wl` | `MetamathToTypeTheory` |

A database can be saved as WXF and imported with no network, `MetamathToTypeTheory[File["set.wxf"]]`.

## Tests

```bash
TYPETHEORY_PACLET=/path/to/TypeTheory/TypeTheory wolframscript -f scripts/run_tests.wls
```

MetamathLink is kept apart from TypeTheory, as LeanLink is: TypeTheory does not depend on it. It follows TypeTheory's
[GUIDE.md](GUIDE.md).
