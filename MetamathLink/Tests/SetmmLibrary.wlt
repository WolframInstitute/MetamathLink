(* ::Package:: *)

(* Tests for SetmmLibrary.wl: set.mm's axioms as theorems over TypeTheoryEnvironment["ZFC"], with no axiom of their own,
   and a forged one rejected. *)

PacletDirectoryLoad[FileNameJoin[{Directory[], "MetamathLink"}]]

Needs["WolframInstitute`TypeTheory`"]
Needs["WolframInstitute`MetamathLink`"]

setmm = WolframInstitute`MetamathLink`PackageScope`setmmEnvironment[]


VerificationTest[
	{Information[setmm, "Axioms"] === Information[TypeTheoryEnvironment["Prelude"], "Axioms"], MatchQ[TypeTheoryCheck[setmm], _Success]},
	{True, True},
	TestID -> "set.mm's-axioms-add-no-axiom-to-the-ZFC-environment"
]

(* the axioms of set.mm, under their labels: the closure of each is the prelude's, and propositional calculus needs only
   classical logic's choice of the prelude where set.mm uses ax-3 *)
VerificationTest[
	Map[
		Function[name, Sort[Keys[TypeTheoryAxiomClosure[TypeTheoryTerm @@ {name, setmm}]]]],
		{"ax-1", "ax-2", "ax-gen", "ax-12", "ax-3", "df-clab", "df-cleq", "ax-ext", "ax-rep", "ax-ac"}
	],
	{
		{}, {}, {}, {"propositionalExtensionality", "quotientSoundness"},
		{"choice", "propositionalExtensionality", "quotientSoundness"},
		{"propositionalExtensionality", "quotientSoundness"},
		{"propositionalExtensionality", "quotientSoundness"},
		{"propositionalExtensionality", "quotientSoundness"},
		{"choice", "propositionalExtensionality", "quotientSoundness"},
		{"choice", "propositionalExtensionality", "quotientSoundness"}
	},
	TestID -> "The-axioms-of-set.mm-are-theorems-of-the-model"
]

VerificationTest[
	MatchQ[
		TypeTheoryCheck[
			TypeTheoryTerm["ax-7", setmm],
			TypeTheoryTerm[ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, Implies["setClass"[x] == "setClass"[y], Implies["setClass"[x] == "setClass"[z], "setClass"[y] == "setClass"[z]]]], setmm]
		],
		_Success
	],
	True,
	TestID -> "\"ax-7\"-states-set.mm's-ax-7-about-classes-of-sets"
]

VerificationTest[
	FailureQ[TypeTheoryEnvironment[setmm, {TypeTheoryTheorem[
		"forgedAxiom6",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"]}, "setClass"[x] == "setClass"[y]],
		Function[{Typed[x, "Set"], Typed[y, "Set"]}, "ax-6"[x, y]]
	]}]],
	True,
	TestID -> "A-forged-axiom-of-set.mm-is-rejected"
]
