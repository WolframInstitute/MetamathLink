#!/usr/bin/env wolframscript
(* ::Package:: *)

(* Save a Metamath database as WXF, which MetamathToTypeTheory imports with no network, the whole database or only what
   some labels need: their cone, with every floating and essential hypothesis, and the whole grammar.

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

kept = If[ Length[arguments] > 2,
	With[{needed = Association[Map[# -> True &, WolframInstitute`MetamathLink`PackageScope`metamathCone[database, Drop[arguments, 2]]]]},
		Select[database["Order"], Function[label, KeyExistsQ[needed, label] || MatchQ[database["Statements"][label]["Kind"], "Floating" | "Essential"]]]
	],
	database["Order"]
]

saved = Join[
	KeyDrop[database, {"Identifier"}],
	<|"Statements" -> KeyTake[database["Statements"], kept], "Order" -> kept|>
]

file = Export[ExpandFileName[First[Rest[arguments]]], saved, "WXF", PerformanceGoal -> "Size"]

Print[file, ": ", Length[kept], " statements, ", Round[FileByteCount[file] / 1024.], " KB"]
