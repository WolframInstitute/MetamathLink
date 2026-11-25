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
PackageScoped[metamathCone]


(* ::Section:: *)
(*Usage Messages*)


MetamathToTypeTheory::usage = "MetamathToTypeTheory[File[path]] imports the Metamath database in the file into a TypeTheoryEnvironment, \
every proof checked again by TypeTheory's kernel.\nMetamathToTypeTheory[object] imports the MetamathObject that ResourceFunction[\"MetamathImport\"] gives.\n\
MetamathToTypeTheory[File[\"database.wxf\"]] imports a database MetamathLink saved, with no network.\n\
Options: \"Semantics\" -> \"Axiomatic\" or \"ZFC\" (Automatic: \"ZFC\" when the database has set.mm's setvar typecode); \"Through\" -> label, the last \
statement to import (All: every one); \"Cone\" -> label or {label, ...}, import only what these need; \"UnprovedAxioms\" -> \"Fail\" or \"Assume\", whether an axiom the semantics does not prove stops the import or is \
declared as an axiom; Method -> \"Core\" or \"Surface\", whether declarations are given to TypeTheory's kernel as core terms, the \
kernel's own form, or in surface syntax, elaborated first; \"BatchSize\" -> n, how many declarations TypeTheory's compiled kernel checks at once \
(Automatic: 1000; 1 adds them one at a time)."
metamathDeclarations::usage = "metamathDeclarations[context, label] gives the declarations the statement label adds and the context after it, or a Failure."
metamathCone::usage = "metamathCone[database, labels] gives the statements the assertions labels need, in the order of the database: the assertions \
their proofs apply, the syntax of every statement with its defining axiom, and the theorem axNAME that proves an axiom ax-NAME."
libraryCheck::usage = "libraryCheck[declaration] in the declarations of a statement is a theorem that checks a constant of the environment against the \
translation, added to a copy of the environment that is not kept."


(* ::Section:: *)
(*Function Definitions*)


Options[MetamathToTypeTheory] = {"Semantics" -> Automatic, "Through" -> All, "Cone" -> None, "UnprovedAxioms" -> "Fail", Method -> "Core", "BatchSize" -> Automatic}

MetamathToTypeTheory[File[path_String], options : OptionsPattern[]] := MetamathToTypeTheory[metamathDatabase[File[path]], options]

MetamathToTypeTheory[object_?metamathObjectQ, options : OptionsPattern[]] := MetamathToTypeTheory[metamathDatabase[object], options]

MetamathToTypeTheory[database_Association /; KeyExistsQ[database, "Grammar"], options : OptionsPattern[]] := With[
	{
		semantics = metamathSemantics[Replace[OptionValue["Semantics"], Automatic :> If[MemberQ[Values[database["Statements"]], KeyValuePattern["Typecode" -> "setvar"]], "ZFC", "Axiomatic"]]],
		labels = Replace[OptionValue["Cone"], {
			None :> Replace[OptionValue["Through"], {All :> database["Order"], last_String :> Take[database["Order"], UpTo[First[FirstPosition[database["Order"], last, {Length[database["Order"]]}]]]]}],
			targets : (_String | {__String}) :> metamathCone[database, Flatten[{targets}]]
		}]
	},
	Block[{$declarationMethod = OptionValue[Method], $batchSize = Replace[OptionValue["BatchSize"], Automatic -> 1000]},
		Block[{$declarationSemantics = semantics},
			First[flushed[Fold[
				addStatement,
				{semantics["Environment"], Append[translationContext[database, semantics], "UnprovedAxioms" -> OptionValue["UnprovedAxioms"]], {}},
				labels
			]]]
		]
	]
]

(* The state of an import: the environment, the context of the translation, and the declarations translated but not yet
   added, each with its label. They are added in batches, checked by TypeTheory's compiled kernel where it has one,
   before a check of a constant of the environment, and at the end. *)
addStatement[{failure_Failure, context_, pending_}, _] := {failure, context, pending}
addStatement[{environment_, context_, pending_List}, label_String] := Replace[reapVariants[metamathDeclarations[context, label]], {
	{{declarations_List, next_Association}, variants_List} :> Replace[Fold[addVariant, {{}, next}, variants], {
		{variantDeclarations_List, final_Association} :> Fold[enqueued[label], {environment, final, pending}, Join[variantDeclarations, declarations]],
		failure_Failure :> {relabeled[failure, label], context, pending}
	}],
	{failure_Failure, _} :> {relabeled[failure, label], context, pending}
}]

relabeled[Failure[tag_, data_Association], label_String] := Failure[tag, Append[data, "Label" -> label]]
relabeled[failure_, _] := failure

(* a check of a constant of the environment waits for what comes before it *)
enqueued[label_][{failure_Failure, context_, pending_}, _] := {failure, context, pending}
enqueued[label_][state_List, check_libraryCheck] := Replace[flushed[state], {
	{environment_, context_, {}} :> {addDeclaration[label][environment, check], context, {}},
	other_ :> other
}]
enqueued[label_][{environment_, context_, pending_List}, declaration_] := With[{queue = Append[pending, {label, declaration}]},
	If[Length[queue] >= $batchSize, flushed[{environment, context, queue}], {environment, context, queue}]
]

(* the declarations waiting, added at once with the compiled kernel's check, which TypeTheory replaces by its own where
   it has no compiled kernel; where the batch fails, it is added again one declaration at a time, so that the failure is
   the first declaration's that does not check, with its label *)
flushed[{failure_Failure, context_, pending_}] := {failure, context, pending}
flushed[{environment_, context_, {}}] := {environment, context, {}}
flushed[{environment_, context_, pending_List}] := Replace[TypeTheoryEnvironment[environment, Map[Last, pending], Method -> "Compiled"], {
	_Failure :> {Fold[Function[{current, entry}, addDeclaration[First[entry]][current, Last[entry]]], environment, pending], context, {}},
	extended_ :> {extended, context, {}}
}]

$batchSize = 1000

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
									libraryCheck[surfaceDeclarationOf[
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

(* a declaration from inactive terms: in core terms, which the kernel takes as they are, unless a term has no core form
   or the import asks for surface syntax; then activated inside HoldComplete. A Failure of the translation passes through *)
declarationOf[head_, name_String, terms___] := Replace[FirstCase[{terms}, _Failure], {
	Missing["NotFound"] :> Replace[
		If[$declarationMethod === "Core", coreDeclaration[$declarationSemantics, head, name, terms], None],
		None :> surfaceDeclarationOf[head, name, terms]
	],
	failure_ :> failure
}]

surfaceDeclarationOf[head_, name_String, terms___] := Replace[FirstCase[{terms}, _Failure], {
	Missing["NotFound"] :> Replace[Join @@ Map[heldTerm, {terms}], HoldComplete[held___] :> head[name, held]],
	failure_ :> failure
}]

$declarationMethod = "Surface"
$declarationSemantics = <||>


(* ::Subsection:: *)
(*Cones*)


(* the statements some assertions need, found from them: the assertions and syntax theorems each proof applies, the
   syntax axioms in every statement and hypothesis with the axiom that defines each, and for an axiom ax-NAME the earlier
   theorem axNAME of the same statement that proves it; a level at a time, each statement met once *)
metamathCone[database_Association, targets_List] := With[{definitions = definingAxioms[database]},
	Module[{needed = <||>, frontier = Select[DeleteDuplicates[targets], Function[label, KeyExistsQ[database["Statements"], label]]]},
		While[frontier =!= {},
			Scan[Function[label, needed[label] = True], frontier];
			frontier = Select[
				DeleteDuplicates[Catenate[Map[Function[label, requirementsOf[database, definitions, label]], frontier]]],
				Function[label, ! KeyExistsQ[needed, label] && KeyExistsQ[database["Statements"], label]]
			]
		];
		Select[database["Order"], Function[entry, KeyExistsQ[needed, entry]]]
	]
]

requirementsOf[database_, definitions_Association, label_String] := With[{statement = database["Statements"][label]},
	Switch[statement["Kind"],
		"Theorem",
			Join[
				Select[proofLabels[statement], Function[step, MatchQ[Lookup[database["Statements"], step, <||>]["Kind"], "Axiom" | "Theorem"]]],
				syntaxRequirements[database, definitions, label]
			],
		"Axiom",
			Join[
				syntaxRequirements[database, definitions, label],
				If[ statement["Typecode"] === database["ProvableTypecode"],
					Select[{StringReplace[label, StartOfString ~~ "ax-" -> "ax"]}, Function[candidate, candidate =!= label && KeyExistsQ[database["Statements"], candidate]]],
					Lookup[definitions, label, {}]
				]
			],
		_,
			{}
	]
]

(* the labels a proof refers to, without decoding it: a compressed proof lists them between its parentheses, its
   mandatory hypotheses aside, which are no assertions *)
proofLabels[statement_Association] := Replace[statement["Proof"], {
	{"(", rest___String} :> Take[{rest}, LengthWhile[{rest}, Function[token, token =!= ")"]]],
	proof : {___String} :> DeleteDuplicates[proof],
	_ -> {}
}]

(* the syntax labels of a provable statement and its hypotheses, and so their definitions *)
syntaxRequirements[database_, definitions_, label_String] := If[database["Statements"][label]["Typecode"] =!= database["ProvableTypecode"],
	{},
	DeleteDuplicates[Cases[
		Join[{statementTree[database, label]}, Map[Function[hypothesis, statementTree[database, label, hypothesis]], database["Statements"][label]["Essential"]]],
		syntaxNode[syntax_String, _] :> syntax,
		Infinity
	]]
]

(* each syntax axiom's defining axioms: the axioms ( C <-> D ) or C = D whose left side is C applied to variables *)
definingAxioms[database_Association] := GroupBy[
	Cases[
		Map[
			Function[label, {label, statementTree[database, label]}],
			Select[database["Order"], Function[label, database["Statements"][label]["Kind"] === "Axiom" && database["Statements"][label]["Typecode"] === database["ProvableTypecode"]]]
		],
		{label_, syntaxNode[_, {syntaxNode[constructor_String, {variableNode[_String] ...}], _}]} :> constructor -> label
	],
	First -> Last
]
