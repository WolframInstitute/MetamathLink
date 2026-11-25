#!/usr/bin/env wolframscript
(* ::Package:: *)

(* Import what some set.mm theorems need into TypeTheory, every proof checked again by its kernel, and report.

   Usage:
     TYPETHEORY_PACLET=/path/to/TypeTheory/TypeTheory wolframscript -f scripts/import_setmm.wls set.mm [label ...] [--out file.tte]

   set.mm is the database file, or a .wxf database MetamathLink saved (no network then); the labels default to 2p2e4.
   The import is strict: an axiom the ZFC semantics does not prove stops it. It prints the time, the constants, the
   axioms beyond the prelude's (none, when the import succeeds), each label's statement and axiom closure, checks the
   whole environment again with TypeTheoryCheck, and with --out exports it in Format 3. Run it under a memory cap:
   2p2e4's cone, 3496 statements, takes 3 minutes and 0.5 GB. *)

repositoryRoot = ParentDirectory[DirectoryName[$InputFileName]]

PacletDirectoryLoad[FileNameJoin[{repositoryRoot, "MetamathLink"}]]

(* TypeTheory from the directory TYPETHEORY_PACLET names, a checkout's TypeTheory directory, or as installed: its
   umbrella file is read itself, since a newer TypeTheory installed would win over a directory of an older version *)
If[ StringQ[Environment["TYPETHEORY_PACLET"]], Get[FileNameJoin[{Environment["TYPETHEORY_PACLET"], "Kernel", "TypeTheory.wl"}]]]

Needs["WolframInstitute`TypeTheory`"]
Needs["WolframInstitute`MetamathLink`"]

arguments = Rest[$ScriptCommandLine]

output = Replace[arguments, {{___, "--out", file_String, ___} :> file, _ -> None}]

positional = Replace[arguments, {{before___, "--out", _String, after___} :> {before, after}}]

If[ positional === {},
	Print["usage: wolframscript -f scripts/import_setmm.wls set.mm [label ...] [--out file.tte]"];
	Exit[2]
]

source = ExpandFileName[First[positional]]

labels = Replace[Rest[positional], {} -> {"2p2e4"}]

database = WolframInstitute`MetamathLink`PackageScope`metamathDatabase[File[source]]

{seconds, environment} = AbsoluteTiming[MetamathToTypeTheory[database, "Cone" -> labels, "UnprovedAxioms" -> "Fail"]]

If[ FailureQ[environment],
	Print["import failed at ", environment["Label"], ": ", environment["Message"]];
	Exit[1]
]

Print["imported in ", Round[seconds, 0.1], " s: ", Total[Information[environment, "Kinds"]], " constants ", Information[environment, "Kinds"]]

Print["axioms beyond the prelude's: ", Complement[Information[environment, "Axioms"], Information[TypeTheoryEnvironment["Prelude"], "Axioms"]]]

Scan[
	Function[label,
		(* the statement stays inside its TypeTheoryTerm: taken out, it would evaluate *)
		Print[label, ": ", TypeTheoryType[TypeTheoryTerm @@ {label, environment}]];
		Print["    closure: ", Keys[TypeTheoryAxiomClosure[TypeTheoryTerm @@ {label, environment}]]]
	],
	labels
]

{checkSeconds, check} = AbsoluteTiming[TypeTheoryCheck[environment]]

Print["TypeTheoryCheck in ", Round[checkSeconds, 0.1], " s: ", If[MatchQ[check, _Success], "every constant checks again", check]]

If[ StringQ[output], Print["exported: ", Export[output, environment], ", ", FileByteCount[output], " bytes"]]

Exit[If[MatchQ[check, _Success], 0, 1]]
