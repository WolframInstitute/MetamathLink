(* ::Package:: *)

(*
Metamath databases as objects. MetamathImport reads a database into a MetamathDatabase, every proof verified by
MetamathLink's library as it is read, whose statements, parse trees, proofs and cones the object gives; MetamathVerify
verifies a file alone, as metamath-knife does; MetamathToTypeTheory takes a MetamathDatabase and the labels to import.

	MetamathDatabase[<|"Statements" -> ..., "Order" -> ..., "Trees" -> ..., "Grammar" -> ..., "Identifier" -> ...,
		"Source" -> path|>]       the database of metamathDatabase, with the file it was read from
*)


(* ::Section:: *)
(*PackageExported*)


PackageExported[MetamathImport]
PackageExported[MetamathDatabase]
PackageExported[MetamathVerify]


(* ::Section:: *)
(*Usage Messages*)


MetamathImport::usage = "MetamathImport[File[path]] reads the Metamath database in the file path, every proof verified and every statement parsed \
by MetamathLink's library, and gives a MetamathDatabase.\nMetamathImport[File[\"database.wxf\"]] reads a database MetamathLink saved.\n\
MetamathImport[object] reads the MetamathObject that ResourceFunction[\"MetamathImport\"] gives."
MetamathDatabase::usage = "MetamathDatabase[...] is a Metamath database that MetamathImport read.\ndatabase[label] gives the statement label.\n\
database[label, \"ParseTree\"] gives the parse tree of its formula as a Tree, database[label, \"Proof\"] its proof as Metamath's normal proof, the labels \
in order, and database[label, \"Cone\"] the statements it needs.\nInformation[database, property] gives \"Axioms\", \"Theorems\", \"Hypotheses\", \
\"Typecodes\" and \"Source\"."
MetamathVerify::usage = "MetamathVerify[File[path]] verifies every proof of the Metamath database in the file path with MetamathLink's library, and \
gives Success[\"Verified\", ...] with the number of its axioms and theorems, or a Failure with the verifier's diagnostics.\n\
MetamathVerify[database] verifies the file the MetamathDatabase database was read from."


(* ::Section:: *)
(*Function Definitions*)


MetamathImport[File[path_String]] := With[{source = ExpandFileName[path]},
	Replace[metamathDatabase[File[source]], database_Association :> MetamathDatabase[Append[database, "Source" -> source]]]
]

MetamathImport[object_?metamathObjectQ] := MetamathDatabase[metamathDatabase[object]]

MetamathVerify[File[path_String]] := Replace[libraryFunctions[], functions_Association :> functions["metamath_verify"][ExpandFileName[path]]]

MetamathVerify[MetamathDatabase[database_Association]] := Replace[Lookup[database, "Source", None], {
	source_String /; ! StringEndsQ[source, ".wxf"] :> MetamathVerify[File[source]],
	_ :> Failure["NoSource", <|
		"MessageTemplate" -> "The database was not read from a Metamath file, which MetamathVerify verifies.",
		"MessageParameters" -> {}
	|>]
}]

MetamathToTypeTheory[MetamathDatabase[database_Association], options : OptionsPattern[]] := MetamathToTypeTheory[database, options]

MetamathToTypeTheory[MetamathDatabase[database_Association], labels : (_String | {__String}), options : OptionsPattern[]] :=
	MetamathToTypeTheory[database, "Cone" -> labels, options]


(* ::Subsection:: *)
(*Statements, parse trees, proofs and cones*)


MetamathDatabase[database_Association][label_String] := databaseStatement[database, label]

MetamathDatabase[database_Association][label_String, "ParseTree"] := Replace[databaseStatement[database, label], {
	statement_Association :> Replace[statementTree[database, label], tree : (_syntaxNode | _variableNode) :> publicTree[tree]],
	failure_Failure :> failure
}]

MetamathDatabase[database_Association][label_String, "Proof"] := Replace[databaseStatement[database, label], {
	statement_Association /; statement["Kind"] === "Theorem" :> normalProof[database, label],
	statement_Association :> Failure["NoProof", <|"MessageTemplate" -> "`1` is no theorem; it has no proof.", "MessageParameters" -> {label}|>],
	failure_Failure :> failure
}]

MetamathDatabase[database_Association][labels : (_String | {__String}), "Cone"] :=
	metamathCone[database, databaseSemantics[database, Automatic], Flatten[{labels}]]

(* a parse tree as a Tree of the Wolfram Language: a syntax axiom over its arguments, a variable a leaf *)
publicTree[syntaxNode[label_String, arguments_List]] := Tree[label, Map[publicTree, arguments]]
publicTree[variableNode[variable_String]] := Tree[variable, None]

(* Metamath's normal proof: the labels of the proof in order, a step the compressed proof saves written out again where
   it is used. Each step is the labels of its subproof; a label takes the steps of its mandatory hypotheses. *)
normalProof[database_Association, label_String] := Replace[
	First[Fold[Function[{state, step}, normalStep[database, state, step]], {{}, {}}, databaseProof[database, label]]],
	{
		{proof_List} :> proof,
		_ :> Failure["MalformedProof", <|"MessageTemplate" -> "The proof of `1` does not end in one step.", "MessageParameters" -> {label}|>]
	}
]

normalStep[_, {stack_List, saved_List}, markStep[_]] := {stack, Append[saved, Last[stack]]}
normalStep[_, {stack_List, saved_List}, recallStep[index_Integer]] := {Append[stack, First[Take[saved, {index + 1}]]], saved}
normalStep[database_Association, {stack_List, saved_List}, step_String] := With[{arity = hypothesisCount[database["Statements"][step]]},
	{Append[Drop[stack, -arity], Append[Catenate[Take[stack, -arity]], step]], saved}
]

(* a hypothesis, a dummy variable's floating hypothesis and an unknown step, as ? in a proof not finished, take none *)
hypothesisCount[statement_Association] := Length[Lookup[statement, "Floating", {}]] + Length[Lookup[statement, "Essential", {}]]
hypothesisCount[_] := 0


(* ::Subsection:: *)
(*Keys, properties and the summary box*)


MetamathDatabase /: Keys[MetamathDatabase[database_Association]] := database["Order"]

MetamathDatabase /: Length[MetamathDatabase[database_Association]] := Length[database["Order"]]

MetamathDatabase /: KeyExistsQ[MetamathDatabase[database_Association], label_] := KeyExistsQ[database["Statements"], label]

(* the statements in the order of the database, which those the library reads do not keep *)
MetamathDatabase /: Normal[MetamathDatabase[database_Association]] := KeyTake[database["Statements"], database["Order"]]

$databaseProperties = {"Axioms", "Theorems", "Hypotheses", "Typecodes", "Source"}

MetamathDatabase /: Information[MetamathDatabase[database_Association], "Properties"] := $databaseProperties

MetamathDatabase /: Information[MetamathDatabase[database_Association], property_String] := databaseProperty[database, property]

databaseProperty[database_, "Axioms"] := labelsOfKind[database, "Axiom"]
databaseProperty[database_, "Theorems"] := labelsOfKind[database, "Theorem"]
databaseProperty[database_, "Hypotheses"] := labelsOfKind[database, "Floating" | "Essential"]
databaseProperty[database_, "Typecodes"] := DeleteDuplicates[Map[Function[label, database["Statements"][label]["Typecode"]], database["Order"]]]
databaseProperty[database_, "Source"] := Lookup[database, "Source", None]
databaseProperty[_, property_String] := Missing["UnknownProperty", property]

labelsOfKind[database_, kinds_] := Select[database["Order"], Function[label, MatchQ[database["Statements"][label]["Kind"], kinds]]]

(* The box holds the counts, not the database, which may be all of set.mm: it is not interpretable *)
MetamathDatabase /: MakeBoxes[object : MetamathDatabase[database_Association], form : StandardForm | TraditionalForm] := With[
	{counts = Counts[Map[Function[statement, statement["Kind"]], Values[database["Statements"]]]]},
	BoxForm`ArrangeSummaryBox[
		MetamathDatabase,
		object,
		Graphics[{RGBColor[0.55, 0.25, 0.1], Disk[]}, ImageSize -> 12],
		{
			BoxForm`SummaryItem[{"Theorems: ", Lookup[counts, "Theorem", 0]}],
			BoxForm`SummaryItem[{"Axioms: ", Lookup[counts, "Axiom", 0]}]
		},
		{
			BoxForm`SummaryItem[{"Hypotheses: ", Lookup[counts, "Floating", 0] + Lookup[counts, "Essential", 0]}],
			BoxForm`SummaryItem[{"Parse trees from the library: ", Length[Lookup[database, "Trees", <||>]]}],
			BoxForm`SummaryItem[{"Source: ", Replace[Lookup[database, "Source", None], source_String :> FileNameTake[source]]}]
		},
		form,
		"Interpretable" -> False
	]
]
