(* ::Package:: *)

(*
MetamathLink's library, the Rust crate in Libs/metamath_link: metamath-rs, the library of metamath-knife, reads a
database, verifies every proof, and parses every statement with the grammar of the database's syntax axioms. Its
functions take and give typed WXF through wolfram-export; `cargo wl build` writes the library with its loader,
Functions.wl, into Binaries/metamath_link-<SystemID>/, and scripts/build_library.sh runs it.

	libraryDatabase[path]   <|"Statements" -> ..., "Order" -> ..., "ProvableTypecode" -> "|-", "FormulaTypecode" -> "wff",
	                          "Trees" -> <|label -> tree, ...|>|>, the shape of metamathDatabase, or a Failure

A statement the grammar does not parse has no tree there; statementTree parses it itself.
*)


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[libraryFunctions]
PackageScoped[libraryDatabase]


(* ::Section:: *)
(*Usage Messages*)


libraryFunctions::usage = "libraryFunctions[] gives the functions of MetamathLink's library for this platform by their names, or a Failure when it has \
none."
libraryDatabase::usage = "libraryDatabase[path] reads the database in the file path with MetamathLink's library: its statements, verified, and the \
parse trees of those its grammar parses; or a Failure."


(* ::Section:: *)
(*Function Definitions*)


libraryLoader[] := FileNameJoin[{PacletObject["WolframInstitute/MetamathLink"]["Location"], "Binaries", "metamath_link-" <> $SystemID, "Functions.wl"}]

(* loaded once a session; a platform with no library gives the same Failure each time *)
libraryFunctions[] := libraryFunctions[] = With[{loader = libraryLoader[]},
	Replace[If[FileExistsQ[loader], Get[loader], $Failed], {
		functions_Association :> functions,
		_ :> Failure["NoLibrary", <|
			"MessageTemplate" -> "MetamathLink has no library for `1`; scripts/build_library.sh builds it.",
			"MessageParameters" -> {$SystemID}
		|>]
	}]
]

libraryDatabase[path_String] := Replace[libraryFunctions[], functions_Association :> functions["metamath_database"][ExpandFileName[path]]]
