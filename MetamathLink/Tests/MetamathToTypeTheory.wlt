(* ::Package:: *)

(* Tests for MetamathToTypeTheory: demo0 in the axiomatic semantics, set.mm's propositional calculus in the ZFC
   semantics, and databases whose proofs do not prove their statements, rejected. *)

PacletDirectoryLoad[FileNameJoin[{Directory[], "MetamathLink"}]]

Needs["WolframInstitute`TypeTheory`"]
Needs["WolframInstitute`MetamathLink`"]

data = FileNameJoin[{Directory[], "MetamathLink", "Data"}]

demo = MetamathToTypeTheory[File[FileNameJoin[{data, "demo0.mm"}]]]


VerificationTest[
	{
		TypeTheoryType[TypeTheoryTerm["th1", demo]] === TypeTheoryTerm[ForAll[{Typed[t, "term"]}, "weq"[t, t]], demo],
		Sort[Keys[TypeTheoryAxiomClosure[TypeTheoryTerm["th1", demo]]]],
		MatchQ[TypeTheoryCheck[demo], _Success]
	},
	{True, Sort[{"term", "weq", "mp", "tpl", "tze", "a2", "wim", "a1"}], True},
	TestID -> "demo0-proves-th1-from-its-own-axioms"
]

(* the propositional calculus of set.mm: its axioms are theorems of the ZFC library, an intuitionistic theorem needs no
   axiom and one that uses ax-3 needs the prelude's classical ones *)
propositional = MetamathToTypeTheory[File[FileNameJoin[{data, "setmm-propositional.mm"}]], "Through" -> "pm2.18"]

VerificationTest[
	{
		Head[propositional],
		Keys[TypeTheoryAxiomClosure[TypeTheoryTerm["mpd", propositional]]],
		Sort[Keys[TypeTheoryAxiomClosure[TypeTheoryTerm["pm2.18", propositional]]]],
		TypeTheoryType[TypeTheoryTerm["pm2.43", propositional]] === TypeTheoryTerm[
			ForAll[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]}, Implies[Implies[\[CurlyPhi], Implies[\[CurlyPhi], \[Psi]]], Implies[\[CurlyPhi], \[Psi]]]],
			propositional
		]
	},
	{TypeTheoryEnvironment, {}, {"choice", "propositionalExtensionality", "quotientSoundness"}, True},
	TestID -> "set.mm's-propositional-calculus-in-the-ZFC-semantics"
]

(* a proof that does not prove its statement: the statement of th1 changed, and a proof step changed *)
demoText = ReadString[FileNameJoin[{data, "demo0.mm"}]]

VerificationTest[
	{
		First[MetamathToTypeTheory[ResourceFunction["MetamathImport"][StringReplace[demoText, "th1 $p |- t = t" -> "th1 $p |- t = r"]]]],
		First[MetamathToTypeTheory[ResourceFunction["MetamathImport"][StringReplace[demoText, "tt tze tpl tt tt a1 mp mp" -> "tt tze tpl tt tt a1 mp"]]]]
	},
	{"ProofMismatch", "ProofMismatch"},
	TestID -> "Proofs-that-do-not-prove-their-statements-are-rejected"
]
