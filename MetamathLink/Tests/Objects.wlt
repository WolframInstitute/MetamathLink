(* ::Package:: *)

(* Tests for MetamathImport, MetamathDatabase and MetamathVerify: a database read and verified by MetamathLink's
   library, its statements, parse trees, proofs and cones, and its import into TypeTheory by labels. *)

PacletDirectoryLoad[FileNameJoin[{Directory[], "MetamathLink"}]]

Needs["WolframInstitute`TypeTheory`"]
Needs["WolframInstitute`MetamathLink`"]

data = FileNameJoin[{Directory[], "MetamathLink", "Data"}]

demo = MetamathImport[File[FileNameJoin[{data, "demo0.mm"}]]]

broken = With[{file = FileNameJoin[{$TemporaryDirectory, "metamathlink-objects-broken-demo0.mm"}]},
	Export[file, StringReplace[ReadString[FileNameJoin[{data, "demo0.mm"}]], "th1 $p |- t = t" -> "th1 $p |- t = r"], "Text"]
]


VerificationTest[
	{
		Head[demo],
		Information[demo, "Theorems"],
		Length[Information[demo, "Axioms"]],
		Information[demo, "Typecodes"],
		FileNameTake[Information[demo, "Source"]],
		Length[demo] === Length[Keys[demo]],
		KeyExistsQ[demo, "th1"]
	},
	{MetamathDatabase, {"th1"}, 7, {"term", "wff", "|-"}, "demo0.mm", True, True},
	TestID -> "import-demo0"
]

VerificationTest[
	{demo["th1"]["Symbols"], demo["th1"]["Kind"], Head[demo["no such label"]]},
	{{"t", "=", "t"}, "Theorem", Failure},
	TestID -> "statement"
]

(* demo0's grammar is ambiguous where the library's parser looks ahead: MetamathLink's parser gives this tree *)
VerificationTest[
	demo["th1", "ParseTree"],
	Tree["weq", {Tree["t", None], Tree["t", None]}],
	TestID -> "parse-tree"
]

(* th1's proof is not compressed in the file: its normal proof is the file's *)
VerificationTest[
	demo["th1", "Proof"],
	StringSplit["tt tze tpl tt weq tt tt weq tt a2 tt tze tpl tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl tt tt a1 mp mp"],
	TestID -> "normal-proof"
]

VerificationTest[
	{Head[demo["a1", "Proof"]], First[demo["a1", "Proof"]]},
	{Failure, "NoProof"},
	TestID -> "an-axiom-has-no-proof"
]

(* set.mm's propositional calculus: compressed proofs, with steps saved and used again, written out as normal proofs; the
   library parses its statements *)
propositional = MetamathImport[File[FileNameJoin[{data, "setmm-propositional.mm"}]]]

VerificationTest[
	With[{theorems = Information[propositional, "Theorems"]},
		{
			Length[theorems] === MetamathVerify[propositional]["Theorems"],
			Select[theorems, ! MatchQ[propositional[#, "Proof"], {__String}] &],
			Last[propositional["mp2", "Proof"]],
			propositional["ax-mp", "ParseTree"]
		}
	],
	{True, {}, "ax-mp", Tree["ps", None]},
	TestID -> "normal-proofs-of-compressed-proofs"
]

VerificationTest[
	{Last[demo["th1", "Cone"]], Sort[demo["th1", "Cone"]] === Sort[DeleteDuplicates[demo["th1", "Cone"]]], MemberQ[demo["th1", "Cone"], "a1"]},
	{"th1", True, True},
	TestID -> "cone"
]

VerificationTest[
	With[{verified = MetamathVerify[File[FileNameJoin[{data, "demo0.mm"}]]]},
		{Head[verified], First[verified], verified["Theorems"], verified["Axioms"], MetamathVerify[demo] === verified}
	],
	{Success, "Verified", 1, 7, True},
	TestID -> "verify"
]

VerificationTest[
	{Head[#], First[#], Length[#["Diagnostics"]]} &[MetamathVerify[File[broken]]],
	{Failure, "InvalidDatabase", 1},
	TestID -> "verify-refuses-a-proof-that-does-not-verify"
]

VerificationTest[
	{Head[#], First[#]} &[MetamathImport[File[broken]]],
	{Failure, "InvalidDatabase"},
	TestID -> "import-refuses-a-proof-that-does-not-verify"
]

VerificationTest[
	With[{environment = MetamathToTypeTheory[demo, "th1"]},
		{Head[environment], Sort[Keys[TypeTheoryAxiomClosure[TypeTheoryTerm["th1", environment]]]]}
	],
	{TypeTheoryEnvironment, Sort[{"term", "weq", "mp", "tpl", "tze", "a2", "wim", "a1"}]},
	TestID -> "to-type-theory-by-label"
]

(* the summary box holds counts, not the statements *)
VerificationTest[
	{FreeQ[ToBoxes[propositional], "pm2.43"], ByteCount[ToBoxes[propositional]] < 50000},
	{True, True},
	TestID -> "summary-box"
]
