(* ::Package:: *)

(*
MetamathToTypeTheory: a database's statements, in order, as declarations of a TypeTheory environment, each checked by
TypeTheory's kernel as it is added. A syntax axiom with a meaning in the semantics adds nothing; one defined by its df-
axiom becomes a definition when that axiom comes; a syntax theorem adds nothing, its proof being expanded where it is
used. An axiom is proved as the semantics proves it, or declared as an axiom in the axiomatic semantics, and a theorem is
proved by the translation of its proof.
*)


(* ::Section:: *)
(*PackageImport*)


PackageImport["WolframInstitute`TypeTheory`"]


(* ::Section:: *)
(*PackageExported*)


PackageExported[MetamathToTypeTheory]


(* ::Section:: *)
(*PackageScoped*)


PackageScoped[metamathDeclarations]


(* ::Section:: *)
(*Usage Messages*)


MetamathToTypeTheory::usage = "MetamathToTypeTheory[File[path]] imports the Metamath database in the file into a TypeTheoryEnvironment, \
every proof checked again by TypeTheory's kernel.\nMetamathToTypeTheory[object] imports the MetamathObject that ResourceFunction[\"MetamathImport\"] gives.\n\
Options: \"Semantics\" -> \"Axiomatic\" or \"ZFC\" (Automatic: \"ZFC\" when the database has set.mm's setvar typecode); \"Through\" -> label, the last \
statement to import (All: every one); \"UnprovedAxioms\" -> \"Fail\" or \"Assume\", whether an axiom the semantics does not prove stops the import or is \
declared as an axiom."
metamathDeclarations::usage = "metamathDeclarations[context, label] gives the declarations the statement label adds and the context after it, or a Failure."


(* ::Section:: *)
(*Function Definitions*)


Options[MetamathToTypeTheory] = {"Semantics" -> Automatic, "Through" -> All, "UnprovedAxioms" -> "Fail"}

MetamathToTypeTheory[File[path_String], options : OptionsPattern[]] := MetamathToTypeTheory[ResourceFunction["MetamathImport"][File[path]], options]

MetamathToTypeTheory[object_?metamathObjectQ, options : OptionsPattern[]] := With[{database = metamathDatabase[object]},
	With[
		{
			semantics = metamathSemantics[Replace[OptionValue["Semantics"], Automatic :> If[MemberQ[Values[database["Statements"]], KeyValuePattern["Typecode" -> "setvar"]], "ZFC", "Axiomatic"]]],
			labels = Replace[OptionValue["Through"], {All :> database["Order"], last_String :> Take[database["Order"], UpTo[First[FirstPosition[database["Order"], last, {Length[database["Order"]]}]]]]}]
		},
		First[Fold[
			addStatement,
			{semantics["Environment"], Append[translationContext[database, semantics], "UnprovedAxioms" -> OptionValue["UnprovedAxioms"]]},
			labels
		]]
	]
]

addStatement[{failure_Failure, context_}, _] := {failure, context}
addStatement[{environment_, context_}, label_String] := Replace[metamathDeclarations[context, label], {
	{declarations_List, next_Association} :> {Fold[addDeclaration[label], environment, declarations], next},
	failure_Failure :> {Failure[failure[[1]], Append[failure[[2]], "Label" -> label]], context}
}]

addDeclaration[label_][failure_Failure, _] := failure
addDeclaration[label_][environment_, declaration_] := Replace[TypeTheoryEnvironment[environment, {declaration}],
	failure_Failure :> Failure["KernelRejected", <|
		"MessageTemplate" -> "TypeTheory's kernel rejects the translation of `1`: `2`",
		"MessageParameters" -> {label, failure["Message"]},
		"Label" -> label,
		"Declaration" -> declaration,
		"Failure" -> failure
	|>]
]

(* the declarations of one statement *)
metamathDeclarations[context_, label_String] := With[{statement = context["Database"]["Statements"][label], database = context["Database"]},
	Which[
		MatchQ[statement["Kind"], "Floating" | "Essential"],
			{{}, context},
		statement["Kind"] === "Theorem" && statement["Typecode"] =!= database["ProvableTypecode"],
			{{}, context},
		statement["Kind"] === "Axiom" && statement["Typecode"] =!= database["ProvableTypecode"],
			syntaxDeclarations[context, statement],
		statement["Kind"] === "Axiom",
			axiomDeclarations[context, statement],
		True,
			theoremDeclarations[context, statement]
	]
]

(* a syntax axiom: in the axiomatic semantics a constant, after its typecodes' types; in another, nothing *)
syntaxDeclarations[context_, statement_Association] := If[context["Semantics"]["Name"] =!= "Axiomatic",
	{{}, context},
	With[
		{
			newTypecodes = Complement[
				DeleteDuplicates[Join[Map[First[Rest[#]] &, statement["Floating"]], {statement["Typecode"]}]],
				Keys[context["Semantics"]["TypecodeTypes"]],
				Lookup[context, "DeclaredTypecodes", {}]
			],
			type = Inactive[TypeSpecifier][Map[Function[floating, typecodeTypeOf[context, First[Rest[floating]]]], statement["Floating"]] -> typecodeTypeOf[context, statement["Typecode"]]]
		},
		{
			Join[
				Map[Function[typecode, TypeTheoryAxiom @@ {typecode, TypeUniverse[1]}], newTypecodes],
				{declarationOf[TypeTheoryAxiom, statement["Label"], If[statement["Floating"] === {}, typecodeTypeOf[context, statement["Typecode"]], type]]}
			],
			Append[context, "DeclaredTypecodes" -> Join[Lookup[context, "DeclaredTypecodes", {}], newTypecodes]]
		}
	]
]

typecodeTypeOf[context_, typecode_String] := Lookup[context["Semantics"]["TypecodeTypes"], typecode, typecode]

axiomDeclarations[context_, statement_Association] := With[{label = statement["Label"]},
	Which[
		KeyExistsQ[context["Semantics"]["AxiomProofs"], label],
			checkedDeclarations[{declarationOf[TypeTheoryTheorem, label, statementTerm[context, label], context["Semantics"]["AxiomProofs"][label]]}, context],
		context["Semantics"]["Name"] === "Axiomatic",
			checkedDeclarations[{declarationOf[TypeTheoryAxiom, label, statementTerm[context, label]]}, context],
		True,
			Replace[definitionOf[context, label], {
				definition_Association :> With[{constructor = constructorDefinition[context, label, definition]},
					With[{defined = Append[context, "Definitions" -> Append[context["Definitions"], definition["Constructor"] -> constructor]]},
						checkedDeclarations[
							{
								declarationOf[TypeTheoryDefinition, definition["Constructor"], Catch[constructorValue[context, label, constructor, definition["Right"]], "translation"]],
								declarationOf[TypeTheoryTheorem, label, statementTerm[defined, label], definitionProofTerm[defined, label, definition]]
							},
							defined
						]
					]
				],
				None :> If[context["UnprovedAxioms"] === "Assume",
					checkedDeclarations[{declarationOf[TypeTheoryAxiom, label, statementTerm[context, label]]}, context],
					Failure["UnprovedAxiom", <|"MessageTemplate" -> "The semantics `1` neither proves the axiom `2` nor reads it as a definition.", "MessageParameters" -> {context["Semantics"]["Name"], label}|>]
				]
			}]
	]
]

theoremDeclarations[context_, statement_Association] := checkedDeclarations[
	{declarationOf[TypeTheoryTheorem, statement["Label"], statementTerm[context, statement["Label"]], proofTerm[context, statement["Label"]]]},
	context
]

checkedDeclarations[declarations_List, context_] := Replace[FirstCase[declarations, _Failure], {Missing["NotFound"] :> {declarations, context}, failure_ :> failure}]

(* a declaration from inactive terms, activated inside HoldComplete; a Failure of the translation passes through *)
declarationOf[head_, name_String, terms___] := Replace[FirstCase[{terms}, _Failure], {
	Missing["NotFound"] :> Replace[Join @@ Map[heldTerm, {terms}], HoldComplete[held___] :> head[name, held]],
	failure_ :> failure
}]
