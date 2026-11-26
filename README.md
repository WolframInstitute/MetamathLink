# MetamathLink

Metamath databases in [TypeTheory](https://github.com/WolframInstitute/TypeTheory), a proof engine for the Calculus of
Inductive Constructions in pure Wolfram Language. `MetamathToTypeTheory` reads a database with
`ResourceFunction["MetamathImport"]`, translates each statement into a statement of type theory and each proof into a proof
term, and TypeTheory's kernel checks every one again: Metamath's checker is not trusted, nor is this translation.

```wl
PacletDirectoryLoad["MetamathLink"]
Needs["WolframInstitute`TypeTheory`"]
Needs["WolframInstitute`MetamathLink`"]

database = MetamathImport[File["MetamathLink/Data/demo0.mm"]]   (* read, verified and parsed by the Rust library *)
database["th1", "ParseTree"]                             (* Tree["weq", {Tree["t", None], Tree["t", None]}] *)
database["th1", "Proof"]                                 (* Metamath's normal proof *)
MetamathVerify[File["set.mm"]]                           (* Success["Verified", ...], all of set.mm in 1 s *)

env = MetamathToTypeTheory[database, "th1"]              (* what th1 needs, every proof checked by TypeTheory *)
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
| `Kernel/Objects.wl` | `MetamathImport`, `MetamathDatabase`, `MetamathVerify` |
| `Kernel/Library.wl` | MetamathLink's library, the Rust crate in `Libs/metamath_link` |
| `Kernel/Database.wl` | the statements of a database, the grammar of the syntax axioms and the parser, compressed proofs |
| `Kernel/Translation.wl` | frames, statements and proof terms, definitions, variants |
| `Kernel/Semantics.wl` | the Axiomatic and ZFC semantics |
| `Kernel/SetmmLibrary.wl` | set.mm's axioms as theorems over the ZFC environment, with no axiom of their own |
| `Kernel/Core.wl` | the terms as TypeTheory's core terms |
| `Kernel/Import.wl` | `MetamathToTypeTheory` |

A database can be saved as WXF and imported with no network, `MetamathToTypeTheory[File["set.wxf"]]`.

## The library

`MetamathLink/Libs/metamath_link` is a Rust crate on [metamath-rs](https://github.com/metamath/metamath-knife), the
library of metamath-knife: it reads a `.mm` file, verifies every proof and parses every statement with the grammar of
the database's syntax axioms, and gives the kernel the database as typed WXF through
[wolfram-export](https://github.com/WolframResearch/wolfram-rust-library). All of set.mm, 121,324 statements, is read,
verified and parsed in 2 s. A statement its grammar does not parse, as in demo0, whose grammar is ambiguous where the
parser looks ahead, is parsed by MetamathLink's own parser; without a library for the platform, a `.mm` file is read by
`ResourceFunction["MetamathImport"]`.

```bash
sh scripts/build_library.sh         # cargo test, then cargo wl build: MetamathLink/Binaries/metamath_link-<SystemID>/
sh scripts/build_library.sh --all   # the five platforms a release carries, cross-compiled from a Mac
```

It needs Rust and `cargo-wl` (`cargo install cargo-wl`), which writes the library's loader, `Functions.wl`; `--all` needs
the Rust targets of the platforms and the linkers `.cargo/config.toml` names.

## set.mm through 2p2e4

```bash
TYPETHEORY_PACLET=/path/to/TypeTheory/TypeTheory wolframscript -f scripts/import_setmm.wls set.mm 2p2e4 --out 2p2e4.tte
```

imports the cone of `2p2e4`, 3403 statements of set.mm down to the construction of the complex numbers, with
TypeTheory's compiled kernel: 3801 constants, no axiom beyond the prelude's, `2p2e4`'s closure the prelude's propositional
extensionality, choice and quotient soundness, and `TypeTheoryCheck` checks every constant again.

| `2p2e4`'s cone | time | memory |
|---|---|---|
| all of set.mm read, verified and parsed by the library (in Rust) | 2.0 s | |
| the same into the kernel, 121,324 statements | 4.6 s | 0.7 GB |
| the import from all of set.mm | 39 s | about 2 GB at its peak |
| the import from `Data/setmm-2p2e4.wxf`, the cone saved with its trees | 40 s | 1.0 GB |
| `TypeTheoryCheck` of the 3801 constants | 3.5 s | |
| metamath-knife verifying all of set.mm, one thread | 0.86 s | |

## Tests

```bash
TYPETHEORY_PACLET=/path/to/TypeTheory/TypeTheory wolframscript -f scripts/run_tests.wls
```

MetamathLink is kept apart from TypeTheory, as LeanLink is: TypeTheory does not depend on it. It follows TypeTheory's
[GUIDE.md](GUIDE.md).
