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
PackageScoped[libraryCheck]


(* ::Section:: *)
(*Usage Messages*)


MetamathToTypeTheory::usage = "MetamathToTypeTheory[File[path]] imports the Metamath database in the file into a TypeTheoryEnvironment, \
every proof checked again by TypeTheory's kernel.\nMetamathToTypeTheory[object] imports the MetamathObject that ResourceFunction[\"MetamathImport\"] gives.\n\
MetamathToTypeTheory[File[\"database.wxf\"]] imports a database MetamathLink saved, with no network.\n\
Options: \"Semantics\" -> \"Axiomatic\" or \"ZFC\" (Automatic: \"ZFC\" when the database has set.mm's setvar typecode); \"Through\" -> label, the last \
statement to import (All: every one); \"UnprovedAxioms\" -> \"Fail\" or \"Assume\", whether an axiom the semantics does not prove stops the import or is \
declared as an axiom."
metamathDeclarations::usage = "metamathDeclarations[context, label] gives the declarations the statement label adds and the context after it, or a Failure."
libraryCheck::usage = "libraryCheck[declaration] in the declarations of a statement is a theorem that checks a constant of the environment against the \
translation, added to a copy of the environment that is not kept."


(* ::Section:: *)
(*Function Definitions*)


Options[MetamathToTypeTheory] = {"Semantics" -> Automatic, "Through" -> All, "UnprovedAxioms" -> "Fail"}

MetamathToTypeTheory[File[path_String], options : OptionsPattern[]] := MetamathToTypeTheory[metamathDatabase[File[path]], options]

MetamathToTypeTheory[object_?metamathObjectQ, options : OptionsPattern[]] := MetamathToTypeTheory[metamathDatabase[object], options]

MetamathToTypeTheory[database_Association /; KeyExistsQ[database, "Grammar"], options : OptionsPattern[]] := With[
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

addStatement[{failure_Failure, context_}, _] := {failure, context}
addStatement[{environment_, context_}, label_String] := Replace[reapVariants[metamathDeclarations[context, label]], {
	{{declarations_List, next_Association}, variants_List} :> Replace[Fold[addVariant, {{}, next}, variants], {
		{variantDeclarations_List, final_Association} :> {Fold[addDeclaration[label], environment, Join[variantDeclarations, declarations]], final},
		failure_Failure :> {Failure[failure[[1]], Append[failure[[2]], "Label" -> label]], context}
	}],
	{failure_Failure, _} :> {Failure[failure[[1]], Append[failure[[2]], "Label" -> label]], context}
}]

SetAttributes[reapVariants, HoldFirst]
reapVariants[expression_] := Replace[Reap[expression, "variant"], {{value_, {}} :> {value, {}}, {value_, {variants_List}} :> {value, DeleteDuplicates[variants]}}]

addDeclaration[label_][failure_Failure, _] := failure
(* a constant of the environment that stands for a statement: checked by a theorem that is not kept *)
addDeclaration[label_][environment_, libraryCheck[declaration_]] := Replace[TypeTheoryEnvironment[environment, {declaration}], {
	_Failure :> Failure["LibraryMismatch", <|
		"MessageTemplate" -> "The environment's `1` does not have the statement or value its translation from the database has.",
		"MessageParameters" -> {label},
		"Label" -> label,
		"Declaration" -> declaration
	|>],
	_ :> environment
}]
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
		MemberQ[context["Semantics"]["LibraryAssertions"], label],
			checkedDeclarations[{libraryCheck[declarationOf[TypeTheoryTheorem, "metamathLibraryCheck", statementTerm[context, label], label]]}, context],
		KeyExistsQ[context["Semantics"]["AxiomProofs"], label],
			checkedDeclarations[{declarationOf[TypeTheoryTheorem, label, statementTerm[context, label], context["Semantics"]["AxiomProofs"][label]]}, context],
		context["Semantics"]["Name"] === "Axiomatic",
			checkedDeclarations[{declarationOf[TypeTheoryAxiom, label, statementTerm[context, label]]}, context],
		justificationOf[context, statement] =!= None,
			checkedDeclarations[{declarationOf[TypeTheoryTheorem, label, statementTerm[context, label], justificationOf[context, statement]]}, context],
		True,
			Replace[definitionOf[context, label], {
				definition_Association :> With[{constructor = constructorDefinition[context, label, definition]},
					With[
						{
							defined = Join[context, <|
								"Definitions" -> Append[context["Definitions"], definition["Constructor"] -> constructor],
								"DefinitionAxioms" -> Append[Lookup[context, "DefinitionAxioms", <||>], label -> definition]
							|>]
						},
						checkedDeclarations[
							{
								If[ MemberQ[context["Semantics"]["LibraryDefinitions"], definition["Constructor"]],
									libraryCheck[declarationOf[
										TypeTheoryTheorem,
										"metamathLibraryCheck",
										Inactive[Equal][definition["Constructor"], Catch[constructorValue[context, label, constructor, definition["Right"]], "translation"]],
										"equalityReflexivity"[definition["Constructor"]]
									]],
									declarationOf[TypeTheoryDefinition, definition["Constructor"], Catch[constructorValue[context, label, constructor, definition["Right"]], "translation"]]
								],
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

(* set.mm states the axioms of the complex numbers, and ax-inf2, after proving each from the others as a theorem axNAME:
   ax-NAME is proved by axNAME when that theorem comes earlier with the same statement and hypotheses *)
justificationOf[context_, statement_Association] := With[
	{
		candidate = StringReplace[statement["Label"], StartOfString ~~ "ax-" -> "ax"],
		statements = context["Database"]["Statements"]
	},
	If[ And[
			candidate =!= statement["Label"],
			KeyExistsQ[statements, candidate],
			statements[candidate]["Kind"] === "Theorem",
			KeyExistsQ[Lookup[context, "Imported", <||>], candidate],
			statements[candidate]["Symbols"] === statement["Symbols"],
			statements[candidate]["Floating"] === statement["Floating"],
			Map[Function[hypothesis, statements[hypothesis]["Symbols"]], statements[candidate]["Essential"]] ===
				Map[Function[hypothesis, statements[hypothesis]["Symbols"]], statement["Essential"]]
		],
		candidate,
		None
	]
]

theoremDeclarations[context_, statement_Association] := checkedDeclarations[
	{declarationOf[TypeTheoryTheorem, statement["Label"], statementTerm[context, statement["Label"]], proofTerm[context, statement["Label"]]]},
	Append[context, "Imported" -> Append[Lookup[context, "Imported", <||>], statement["Label"] -> True]]
]

(* the declarations of a variant, after those of the variants its proof asks for; each is declared once. An axiom has no
   proof to rename: its variant must be proved by the semantics *)
addVariant[failure_Failure, _] := failure

(* a variant of an axiom: a defining axiom's by reflexivity, another proved by the semantics, or assumed when the import
   assumes what it cannot prove *)
axiomVariant[{declarations_List, context_Association}, label_String, renaming_Association, name_String] := With[
	{
		extended = Join[context, <|
			"VariantStatements" -> Append[Lookup[context, "VariantStatements", <||>], name -> variantEntry[context, label, renaming]],
			"Variants" -> Append[Lookup[context, "Variants", <||>], name -> True]
		|>]
	},
	Which[
		(* its constructor's variant is defined by the renamed right side, so its two sides are one term *)
		KeyExistsQ[Lookup[context, "DefinitionAxioms", <||>], label],
			With[{definition = context["DefinitionAxioms"][label]},
				declareVariant[
					{declarations, extended},
					name,
					TypeTheoryTheorem,
					reapVariants[{statementTerm[extended, name], definitionProofTerm[extended, name, Append[definition, "Left" -> renameTree[definition["Left"], renaming]]]}]
				]
			],
		KeyExistsQ[context["Semantics"]["AxiomVariants"], name],
			declareVariant[{declarations, extended}, name, TypeTheoryTheorem, reapVariants[{statementTerm[extended, name], context["Semantics"]["AxiomVariants"][name]}]],
		context["UnprovedAxioms"] === "Assume",
			Replace[declareVariant[{declarations, extended}, name, TypeTheoryAxiom, reapVariants[{statementTerm[extended, name]}]], {
				{inner_List, next_Association} :> {inner, Append[next, "AssumedVariants" -> Append[Lookup[next, "AssumedVariants", {}], name]]},
				failure_Failure :> failure
			}],
		True,
			Failure["AliasedAxiom", <|
				"MessageTemplate" -> "A proof applies the axiom `1` with the same variable for two of its setvar variables; its variant `2` needs a proof.",
				"MessageParameters" -> {label, name}
			|>]
	]
]

(* the declaration of a variant from its terms, after the variants they ask for *)
declareVariant[{declarations_List, context_Association}, name_String, head_, {terms_List, variants_List}] := Replace[
	Fold[addVariant, {declarations, context}, variants],
	{
		{inner_List, next_Association} :> Replace[checkedDeclarations[{declarationOf[head, name, Sequence @@ terms]}, next], {
			{{variant_}, final_Association} :> {Append[inner, variant], final},
			failure_Failure :> failure
		}],
		failure_Failure :> failure
	}
]

addVariant[{declarations_List, context_Association}, {label_String, renaming_Association}] := With[{name = variantLabel[label, renaming]},
	Which[
		KeyExistsQ[Lookup[context, "Variants", <||>], name],
			{declarations, context},
		statementOf[context, label]["Kind"] =!= "Theorem",
			axiomVariant[{declarations, context}, label, renaming, name],
		True,
			With[
				{
					extended = Join[context, <|
						"VariantStatements" -> Append[Lookup[context, "VariantStatements", <||>], name -> variantEntry[context, label, renaming]],
						"Variants" -> Append[Lookup[context, "Variants", <||>], name -> True]
					|>]
				},
				Replace[reapVariants[{statementTerm[extended, name], proofTerm[extended, name]}], {
					{{statement_, term_}, variants_List} :> Replace[Fold[addVariant, {declarations, extended}, variants], {
						{inner_List, next_Association} :> Replace[
							checkedDeclarations[{declarationOf[TypeTheoryTheorem, name, statement, term]}, next],
							{
								{{variant_}, final_Association} :> {Append[inner, variant], final},
								failure_Failure :> failure
							}
						],
						failure_Failure :> failure
					}]
				}]
			]
	]
]

(* a variant of a constructor: defined by the right side of its definition renamed, after the variants that asks for *)
addVariant[{declarations_List, context_Association}, {"syntax", constructor_String, renaming_Association}] := With[{name = variantLabel[constructor, renaming]},
	If[ KeyExistsQ[Lookup[context, "Variants", <||>], name],
		{declarations, context},
		With[{definition = variantConstructorDefinition[context, constructor, renaming]},
			Replace[reapVariants[Catch[constructorValue[definition["Context"], definition["Label"], definition, definition["Right"]], "translation"]], {
				{value_, variants_List} :> Replace[
					Fold[addVariant, {declarations, Append[context, "Variants" -> Append[Lookup[context, "Variants", <||>], name -> True]]}, variants],
					{
						{inner_List, next_Association} :> Replace[checkedDeclarations[{declarationOf[TypeTheoryDefinition, name, value]}, next], {
							{{variant_}, final_Association} :> {Append[inner, variant], final},
							failure_Failure :> failure
						}],
						failure_Failure :> failure
					}
				]
			}]
		]
	]
]


checkedDeclarations[declarations_List, context_] := Replace[FirstCase[declarations, _Failure, Missing["NotFound"], {1, 2}], {Missing["NotFound"] :> {declarations, context}, failure_ :> failure}]

(* a declaration from inactive terms, activated inside HoldComplete; a Failure of the translation passes through *)
declarationOf[head_, name_String, terms___] := Replace[FirstCase[{terms}, _Failure], {
	Missing["NotFound"] :> Replace[Join @@ Map[heldTerm, {terms}], HoldComplete[held___] :> head[name, held]],
	failure_ :> failure
}]
