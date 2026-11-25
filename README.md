# MetamathLink

Metamath databases in [TypeTheory](https://github.com/WolframInstitute/TypeTheory), a proof engine for the Calculus of
Inductive Constructions in pure Wolfram Language. `MetamathToTypeTheory` reads a database with
`ResourceFunction["MetamathImport"]`, translates each statement into a statement of type theory and each proof into a proof
term, and TypeTheory's kernel checks every one again.

- **Axiomatic semantics**, any database: `wff` is `Prop`, every other typecode a declared type, every syntax axiom a declared
  constant and every logical axiom an axiom of the environment (`demo0.mm`).
- **ZFC semantics**, set.mm over `TypeTheoryEnvironment["ZFC"]`, Aczel's model of ZFC: `setvar` is `"Set"`, `class` is
  `"Class"`, the primitive syntax denotes the connectives, quantifiers and class vocabulary of the model, every other syntax
  axiom is defined by its `df-` axiom, and every axiom is a theorem.

Statements are in higher-order abstract syntax: a setvar variable is a bound variable of type `"Set"`; a wff or class
variable is a function of the setvar variables it has no `$d` with.

```wl
PacletDirectoryLoad["MetamathLink"]
Needs["WolframInstitute`MetamathLink`"]
env = MetamathToTypeTheory[File["MetamathLink/Data/demo0.mm"]]
TypeTheoryType[TypeTheoryTerm["th1", env]]
```

MetamathLink is kept apart from TypeTheory, as LeanLink is: TypeTheory does not depend on it. It follows TypeTheory's
[GUIDE.md](GUIDE.md).
