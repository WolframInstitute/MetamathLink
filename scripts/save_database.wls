#!/usr/bin/env wolframscript
(* ::Package:: *)

(* Save a Metamath database as WXF, which MetamathToTypeTheory imports with no network, the whole database or only what
   some labels need: their cone, with the hypotheses of its assertions, the grammar of its syntax axioms, and the parse
   trees MetamathLink's library gave.

     wolframscript -f scripts/save_database.wls set.mm out.wxf [label ...]

   MetamathLink/Data/setmm-2p2e4.wxf is made with the labels 2p2e4. *)

repositoryRoot = ParentDirectory[DirectoryName[$InputFileName]]

PacletDirectoryLoad[FileNameJoin[{repositoryRoot, "MetamathLink"}]]

If[ StringQ[Environment["TYPETHEORY_PACLET"]], Get[FileNameJoin[{Environment["TYPETHEORY_PACLET"], "Kernel", "TypeTheory.wl"}]]]

Needs["WolframInstitute`MetamathLink`"]

arguments = Rest[$ScriptCommandLine]

If[ Length[arguments] < 2,
	Print["usage: wolframscript -f scripts/save_database.wls set.mm out.wxf [label ...]"];
	Exit[2]
]

database = WolframInstitute`MetamathLink`PackageScope`metamathDatabase[File[ExpandFileName[First[arguments]]]]

(* the cone of the labels, with the hypotheses of its assertions and those their proofs refer to, as the floating
   hypotheses of dummy variables *)
kept = If[ Length[arguments] > 2,
	With[{cone = WolframInstitute`MetamathLink`PackageScope`metamathCone[database, WolframInstitute`MetamathLink`PackageScope`databaseSemantics[database, Automatic], Drop[arguments, 2]]},
		With[
			{
				needed = Association[Map[# -> True &,
					Join[cone, Catenate[Map[
						Function[label, With[{statement = database["Statements"][label]},
							Join[Map[First, Lookup[statement, "Floating", {}]], Lookup[statement, "Essential", {}], If[statement["Kind"] === "Theorem", WolframInstitute`MetamathLink`PackageScope`proofLabels[statement], {}]]
						]],
						cone
					]]]
				]]
			},
			Select[database["Order"], Function[label, KeyExistsQ[needed, label]]]
		]
	],
	database["Order"]
]

(* the grammar of the syntax axioms kept, and the parse trees MetamathLink's library gave of the statements kept *)
saved = With[{statements = KeyTake[database["Statements"], kept]},
	Join[
		KeyDrop[database, {"Identifier", "Grammar", "Trees"}],
		<|"Statements" -> statements, "Order" -> kept|>,
		If[KeyExistsQ[database, "Trees"], <|"Trees" -> KeyTake[database["Trees"], kept]|>, <||>],
		<|"Grammar" -> WolframInstitute`MetamathLink`PackageScope`grammarOf[Join[database, <|"Statements" -> statements|>]]|>
	]
]

file = Export[ExpandFileName[First[Rest[arguments]]], saved, "WXF", PerformanceGoal -> "Size"]

Print[file, ": ", Length[kept], " statements, ", Round[FileByteCount[file] / 1024.], " KB"]
