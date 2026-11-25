(* ::Package:: *)

(* Tests for MetamathLink's library: a database read, verified and parsed by metamath-rs, its trees those of
   MetamathLink's own parser, and a database that does not verify refused. *)

PacletDirectoryLoad[FileNameJoin[{Directory[], "MetamathLink"}]]

Needs["WolframInstitute`MetamathLink`"]

data = FileNameJoin[{Directory[], "MetamathLink", "Data"}]


VerificationTest[
	Keys[WolframInstitute`MetamathLink`PackageScope`libraryFunctions[]],
	{"metamath_database"},
	TestID -> "library-loads"
]

(* set.mm's propositional calculus, a prefix of set.mm: the grammar of the whole of set.mm parses every statement, but
   that of a prefix stops at trujust, the first statement that needs a setvar variable read as a class, x = x, and
   metamath-rs parses no statement after one it cannot parse. The trees it gives are those of MetamathLink's parser. *)
propositional = WolframInstitute`MetamathLink`PackageScope`metamathDatabase[File[FileNameJoin[{data, "setmm-propositional.mm"}]]]

VerificationTest[
	With[
		{
			assertions = Select[propositional["Order"], MatchQ[propositional["Statements"][#]["Kind"], "Axiom" | "Theorem"] && propositional["Statements"][#]["Typecode"] === "|-" &],
			parsed = Function[label, WolframInstitute`MetamathLink`Database`Private`parsedStatementTree[propositional, label]]
		},
		With[{trees = Select[assertions, KeyExistsQ[propositional["Trees"], #] &]},
			{
				Length[trees] > 1000,
				SelectFirst[assertions, ! KeyExistsQ[propositional["Trees"], #] &],
				Select[trees, propositional["Trees"][#] =!= parsed[#] &]
			}
		]
	],
	{True, "trujust", {}},
	TestID -> "library-trees-are-the-parser's"
]

VerificationTest[
	propositional["Statements"]["ax-mp"],
	<|"Kind" -> "Axiom", "Label" -> "ax-mp", "Typecode" -> "|-", "Symbols" -> {"ps"}, "Disjoint" -> {},
		"Floating" -> {{"wph", "wff", "ph"}, {"wps", "wff", "ps"}}, "Essential" -> {"min", "maj"}|>,
	TestID -> "library-statement"
]

(* demo0 has no $j syntax, and its grammar is ambiguous where metamath-rs's parser looks ahead: its formulas are parsed
   by MetamathLink's parser *)
VerificationTest[
	With[{demo = WolframInstitute`MetamathLink`PackageScope`metamathDatabase[File[FileNameJoin[{data, "demo0.mm"}]]]},
		{KeyExistsQ[demo["Trees"], "th1"], WolframInstitute`MetamathLink`PackageScope`statementTree[demo, "th1"]}
	],
	{
		False,
		WolframInstitute`MetamathLink`PackageScope`syntaxNode["weq", {WolframInstitute`MetamathLink`PackageScope`variableNode["t"], WolframInstitute`MetamathLink`PackageScope`variableNode["t"]}]
	},
	TestID -> "library-falls-back-to-the-parser"
]

VerificationTest[
	With[{broken = FileNameJoin[{$TemporaryDirectory, "metamathlink-broken-demo0.mm"}]},
		Export[broken, StringReplace[ReadString[FileNameJoin[{data, "demo0.mm"}]], "th1 $p |- t = t" -> "th1 $p |- t = r"], "Text"];
		{Head[#], First[#], Length[#["Diagnostics"]]} &[WolframInstitute`MetamathLink`PackageScope`metamathDatabase[File[broken]]]
	],
	{Failure, "InvalidDatabase", 1},
	TestID -> "library-refuses-a-database-that-does-not-verify"
]
