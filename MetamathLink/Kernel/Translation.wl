(* ::Package:: *)

(*
Statements and proofs of a Metamath database as terms of TypeTheory, in higher-order abstract syntax.

A variable of a binder typecode, set.mm's setvar, is a bound variable of type "Set". Any other variable is a parameter of
the statement: a wff variable a proposition and a class variable a class, each a function of the setvar variables of the
frame it may depend on, those with which it has no $d. A statement with essential hypotheses e1, ..., en and conclusion c
is

	ForAll[{Typed[φ, type], ...}, Implies[ForAll[setvars, e1], ... Implies[ForAll[setvars, en], ForAll[setvars, c]]]]

the parameters in the order of the frame's floating hypotheses, each hypothesis and the conclusion closed over the setvar
variables of the frame. An occurrence of φ is φ[x, ...], applied to the variables it depends on as the binders in scope
bind them; every variable keeps one symbol, so an inner binder shadows an outer one as in Metamath.

A proof step proves its statement closed over every setvar variable of the proof, the frame's and the dummy ones: an
assertion A applied with the substitution σ is

	Function[{V}, A[φ -> Function[{σ(deps of φ)}, σ(φ)], ..., Function[{σ(W)}, q[V]], ..., σ(W)]]

with W the setvar variables of A and q the proofs of its hypotheses: each hypothesis of A must hold for every value of
its setvar variables, which the step gives by binding the symbols of their images again. A step saved by the compressed
proof is let-bound and used by name. The proof of the theorem applies its last step to the frame's setvar variables and
to an inhabitant for each dummy one.

Each syntax axiom denotes a term by the semantics: a primitive of the semantics, a definition, or, in the axiomatic
semantics, a declared constant. A definition is an axiom ( C <-> D ) or C = D whose left side is a new syntax axiom
applied to distinct variables: C becomes a TypeTheoryDefinition, the function of its arguments that D is, and the axiom a
theorem proved by reflexivity. Terms are built with Inactive heads and activated inside HoldComplete only, so that no
Equal or And of them evaluates.
*)


(* ::Section:: *)
(*PackageImport*)


PackageImport["WolframInstitute`TypeTheory`"]


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[frameOf]
PackageScoped[variableSymbol]
PackageScoped[translateTree]
PackageScoped[statementTerm]
PackageScoped[proofTerm]
PackageScoped[definitionOf]
PackageScoped[heldTerm]
PackageScoped[translationContext]
PackageScoped[constructorDefinition]
PackageScoped[constructorValue]
PackageScoped[definitionProofTerm]


(* ::Section:: *)
(*Usage Messages*)


frameOf::usage = "frameOf[context, label] gives the frame of the assertion label: its setvar variables, its other variables with the setvar variables \
each depends on, its essential hypotheses and its distinct variable pairs."
variableSymbol::usage = "variableSymbol[name] gives the symbol that stands for the Metamath variable name in terms, the same symbol at every binder."
translateTree::usage = "translateTree[context, dependencies, tree] gives the term the parse tree denotes, inactive, the variables other than setvar \
ones applied to the setvar variables dependencies gives for each."
statementTerm::usage = "statementTerm[context, label] gives the statement of the assertion label as an inactive term."
proofTerm::usage = "proofTerm[context, label] gives the proof term of the theorem label as an inactive term, or a Failure."
definitionOf::usage = "definitionOf[context, label] gives <|\"Constructor\" -> c, \"Left\" -> tree, \"Right\" -> tree|> when the axiom label defines the \
syntax axiom c, and None otherwise."
heldTerm::usage = "heldTerm[term] gives HoldComplete of the inactive term activated, its heads the surface syntax of TypeTheory."
constructorDefinition::usage = "constructorDefinition[context, label, definition] gives how the constructor the axiom label defines takes its arguments: \
its parameters, the setvar ones among them, and the setvar parameters each other one depends on."
constructorValue::usage = "constructorValue[context, label, constructor, right] gives the value of the defined constructor, an inactive function of its parameters."
definitionProofTerm::usage = "definitionProofTerm[context, label, definition] gives the proof of the defining axiom label by reflexivity, an inactive term."
translationContext::usage = "translationContext[database, semantics] gives the context of a translation: the database, the semantics and the \
definitions read so far."


(* ::Section:: *)
(*Function Definitions*)


(* ::Subsection:: *)
(*Inactive terms*)


heldTerm[term_] := HoldComplete[term] /. Inactive[head_Symbol] :> head

termForAll[{}, body_] := body
termForAll[binders_List, body_] := Inactive[ForAll][binders, body]
termFunction[{}, body_] := body
termFunction[binders_List, body_] := Inactive[Function][binders, body]
termTyped[symbol_, type_] := Inactive[Typed][symbol, type]
termImplies[premise_, conclusion_] := Inactive[Implies][premise, conclusion]
termApply[head_, {}] := head
termApply[head_, arguments_List] := head @@ arguments

variableSymbol[name_String] := variableSymbol[name] = Symbol["WolframInstitute`MetamathLink`Variables`" <> variableSymbolName[name]]

(* set.mm's wff variables by the Greek letters it shows them as; any other name that is not a symbol's by a hash *)
$greekNames = <|
	"ph" -> "\[CurlyPhi]", "ps" -> "\[Psi]", "ch" -> "\[Chi]", "th" -> "\[Theta]", "ta" -> "\[Tau]", "et" -> "\[Eta]",
	"ze" -> "\[Zeta]", "si" -> "\[Sigma]", "rh" -> "\[Rho]", "mu" -> "\[Mu]", "la" -> "\[Lambda]", "ka" -> "\[Kappa]"
|>

variableSymbolName[name_String] := Which[
	KeyExistsQ[$greekNames, name],
		$greekNames[name],
	StringMatchQ[name, RegularExpression["[A-Za-z][A-Za-z0-9]*"]],
		name,
	True,
		"variable" <> IntegerString[Hash[name], 36]
]

hypothesisSymbol[index_Integer] := Symbol["WolframInstitute`MetamathLink`Variables`hypothesis" <> IntegerString[index]]
stepSymbol[index_Integer] := Symbol["WolframInstitute`MetamathLink`Variables`step" <> IntegerString[index]]


(* ::Subsection:: *)
(*Frames*)


translationContext[database_Association, semantics_Association] := <|"Database" -> database, "Semantics" -> semantics, "Definitions" -> <||>|>

binderTypecodeQ[context_, typecode_String] := MemberQ[context["Semantics"]["BinderTypecodes"], typecode]

disjointQ[pairs_List, a_String, b_String] := MemberQ[pairs, {a, b} | {b, a}]

frameOf[context_Association, label_String] := With[{statement = context["Database"]["Statements"][label]},
	With[
		{
			setvars = Cases[statement["Floating"], {_, typecode_, variable_} /; binderTypecodeQ[context, typecode] :> variable],
			others = Cases[statement["Floating"], {_, typecode_, variable_} /; ! binderTypecodeQ[context, typecode] :> {variable, typecode}]
		},
		<|
			"Label" -> label,
			"Setvars" -> setvars,
			"Others" -> others,
			"Dependencies" -> Association[Map[
				Function[other, First[other] -> Select[setvars, Function[setvar, ! disjointQ[statement["Disjoint"], setvar, First[other]]]]],
				others
			]],
			"Essential" -> statement["Essential"],
			"Disjoint" -> statement["Disjoint"]
		|>
	]
]

setType[context_] := context["Semantics"]["TypecodeTypes"][First[context["Semantics"]["BinderTypecodes"]]]

parameterType[context_, typecode_String, dependencies_List] := With[{type = typecodeType[context, typecode]},
	If[dependencies === {}, type, Inactive[TypeSpecifier][ConstantArray[setType[context], Length[dependencies]] -> type]]
]

typecodeType[context_, typecode_String] := Lookup[context["Semantics"]["TypecodeTypes"], typecode, typecode]

setvarBinders[context_, setvars_List] := Map[Function[setvar, termTyped[variableSymbol[setvar], setType[context]]], setvars]


(* ::Subsection:: *)
(*Expressions*)


(* dependencies: the setvar variables each other variable of the frame is applied to; a variable it does not list, a dummy
   of a proof, stands for the inhabitant of its typecode *)
translateTree[context_, dependencies_Association, variableNode[variable_String]] := Which[
	KeyExistsQ[dependencies, variable],
		termApply[variableSymbol[variable], Map[variableSymbol, dependencies[variable]]],
	setvarNameQ[context, variable],
		variableSymbol[variable],
	True,
		dummyInhabitant[context, variable]
]

translateTree[context_, dependencies_Association, syntaxNode[label_String, arguments_List]] := Which[
	KeyExistsQ[context["Semantics"]["Syntax"], label],
		context["Semantics"]["Syntax"][label][
			Function[tree, translateTree[context, dependencies, tree]],
			AssociationThread[Map[Last, context["Database"]["Statements"][label]["Floating"]], arguments]
		],
	KeyExistsQ[context["Definitions"], label],
		definedConstructorTerm[context, dependencies, context["Definitions"][label], arguments],
	context["Semantics"]["Name"] === "Axiomatic",
		termApply[label, Map[Function[tree, translateTree[context, dependencies, tree]], arguments]],
	True,
		Throw[Failure["UndefinedSyntax", <|"MessageTemplate" -> "The syntax `1` has no meaning in the semantics `2`.", "MessageParameters" -> {label, context["Semantics"]["Name"]}|>], "translation"]
]

setvarNameQ[context_, variable_String] := MemberQ[context["Semantics"]["BinderTypecodes"], variableTypecode[context, variable]]

variableTypecode[context_, variable_String] := Lookup[context["VariableTypecodes"], variable, None]

dummyInhabitant[context_, variable_String] := Lookup[
	context["Semantics"]["Inhabitants"],
	variableTypecode[context, variable],
	Throw[Failure["NoInhabitant", <|"MessageTemplate" -> "The dummy variable `1` has no inhabitant to stand for it.", "MessageParameters" -> {variable}|>], "translation"]
]

(* a defined syntax axiom: its setvar arguments as they are, every other argument a function of the setvar arguments it
   may depend on, binding the symbols of the variables there *)
definedConstructorTerm[context_, dependencies_, definition_Association, arguments_List] := With[
	{setvarArguments = Association[MapThread[Rule, {definition["Parameters"], arguments}]]},
	If[ ! DuplicateFreeQ[Map[setvarArguments, definition["SetvarParameters"]]],
		Throw[Failure["AliasedSyntax", <|
			"MessageTemplate" -> "The syntax `1` is used with the same variable for two of its setvar arguments, which needs a variant of its definition.",
			"MessageParameters" -> {definition["Constructor"]}
		|>], "translation"]
	];
	termApply[
		definition["Constructor"],
		MapThread[
			Function[{parameter, argument},
				If[ MemberQ[definition["SetvarParameters"], parameter],
					translateTree[context, dependencies, argument],
					termFunction[
						Map[Function[setvar, termTyped[variableSymbol[First[setvarArguments[setvar]]], setType[context]]], definition["Dependencies"][parameter]],
						translateTree[context, dependencies, argument]
					]
				]
			],
			{definition["Parameters"], arguments}
		]
	]
]


(* ::Subsection:: *)
(*Statements*)


statementTerm[context_, label_String] := Catch[statementTermOf[context, label], "translation"]

statementTermOf[context_, label_String] := With[
	{
		frame = frameOf[context, label],
		database = context["Database"]
	},
	With[
		{
			local = Append[context, "VariableTypecodes" -> variableTypecodesOf[database, label]],
			closed = Function[tree, termForAll[setvarBinders[context, frame["Setvars"]], tree]]
		},
		termForAll[
			Map[Function[other, termTyped[variableSymbol[First[other]], parameterType[context, Last[other], frame["Dependencies"][First[other]]]]], frame["Others"]],
			Fold[
				Function[{conclusion, hypothesis}, termImplies[hypothesis, conclusion]],
				closed[translateTree[local, frame["Dependencies"], confirmTree[statementTree[database, label]]]],
				Reverse[Map[
					Function[hypothesis, closed[translateTree[local, frame["Dependencies"], confirmTree[statementTree[database, label, hypothesis]]]]],
					frame["Essential"]
				]]
			]
		]
	]
]

confirmTree[failure_Failure] := Throw[failure, "translation"]
confirmTree[tree_] := tree

variableTypecodesOf[database_, label_String] := Association[Map[Function[floating, Last[floating] -> First[Rest[floating]]], database["Statements"][label]["Floating"]]]


(* ::Subsection:: *)
(*Definitions*)


(* an axiom ( C <-> D ) or C = D, C a syntax axiom with no meaning yet applied to distinct variables in the order of its
   floating hypotheses *)
definitionOf[context_, label_String] := With[{tree = statementTree[context["Database"], label]},
	Replace[tree, {
		syntaxNode[equivalence_, {left : syntaxNode[constructor_String, arguments : {variableNode[_String] ...}], right_}] /; And[
			MemberQ[context["Semantics"]["DefinitionHeads"], equivalence],
			! KeyExistsQ[context["Semantics"]["Syntax"], constructor],
			! KeyExistsQ[context["Definitions"], constructor],
			DuplicateFreeQ[arguments]
		] :> <|"Constructor" -> constructor, "Head" -> equivalence, "Left" -> left, "Right" -> right|>,
		_ -> None
	}]
]

(* the definition of the constructor: its parameters are the variables of the left side; each that is not a setvar is a
   function of the setvar parameters it is not disjoint from in the defining axiom *)
constructorDefinition[context_, label_String, definition_Association] := With[
	{
		frame = frameOf[context, label],
		parameters = Map[First, Last[definition["Left"]]]
	},
	With[{setvarParameters = Select[parameters, Function[parameter, MemberQ[frame["Setvars"], parameter]]]},
		<|
			"Constructor" -> definition["Constructor"],
			"Label" -> label,
			"Parameters" -> parameters,
			"SetvarParameters" -> setvarParameters,
			"Dependencies" -> Association[Map[
				Function[parameter, parameter -> Select[setvarParameters, Function[setvar, ! disjointQ[frame["Disjoint"], setvar, parameter]]]],
				Complement[parameters, setvarParameters]
			]]
		|>
	]
]

(* the value of the constructor: a function of its parameters, the right side in their terms *)
constructorValue[context_, label_String, constructor_Association, right_] := With[
	{
		local = Append[context, "VariableTypecodes" -> variableTypecodesOf[context["Database"], label]],
		typecodes = variableTypecodesOf[context["Database"], label]
	},
	termFunction[
		Map[
			Function[parameter,
				If[ MemberQ[constructor["SetvarParameters"], parameter],
					termTyped[variableSymbol[parameter], setType[context]],
					termTyped[variableSymbol[parameter], parameterType[context, typecodes[parameter], constructor["Dependencies"][parameter]]]
				]
			],
			constructor["Parameters"]
		],
		translateTree[local, constructor["Dependencies"], right]
	]
]


(* ::Subsection:: *)
(*Proofs*)


proofTerm[context_, label_String] := Catch[proofTermOf[context, label], "translation"]

proofTermOf[context_, label_String] := Module[
	{
		frame = frameOf[context, label],
		database = context["Database"],
		run, setvars, local, final, lets
	},
	run = runProof[context, label];
	(* the setvar variables of the proof: the frame's, then the dummy ones in the order they appear *)
	setvars = Join[frame["Setvars"], Complement[run["Setvars"], frame["Setvars"]]];
	local = Join[context, <|"VariableTypecodes" -> run["VariableTypecodes"], "ProofSetvars" -> setvars, "Frame" -> frame|>];
	lets = Map[Function[saved, Inactive[Set][stepSymbol[First[saved]], stepTerm[local, Last[saved]]]], run["Saved"]];
	final = termApply[
		stepTerm[local, run["Result"]],
		Join[Map[variableSymbol, frame["Setvars"]], Map[Function[setvar, dummyInhabitant[local, setvar]], Drop[setvars, Length[frame["Setvars"]]]]]
	];
	termFunction[assertionBinders[local, label], Fold[Function[{body, binding}, Inactive[With][{binding}, body]], final, Reverse[lets]]]
]

(* the binders of a proof of the assertion label: its parameters, its hypotheses and its setvar variables *)
assertionBinders[context_, label_String] := With[
	{
		frame = frameOf[context, label],
		local = Append[context, "VariableTypecodes" -> variableTypecodesOf[context["Database"], label]]
	},
	Join[
		Map[Function[other, termTyped[variableSymbol[First[other]], parameterType[context, Last[other], frame["Dependencies"][First[other]]]]], frame["Others"]],
		MapIndexed[
			Function[{hypothesis, index},
				termTyped[
					hypothesisSymbol[First[index]],
					termForAll[setvarBinders[context, frame["Setvars"]], translateTree[local, frame["Dependencies"], confirmTree[statementTree[context["Database"], label, hypothesis]]]]
				]
			],
			frame["Essential"]
		],
		setvarBinders[context, frame["Setvars"]]
	]
]

(* the proof of a defining axiom: its two sides are one term once the constructor is unfolded *)
definitionProofTerm[context_, label_String, definition_Association] := Catch[
	termFunction[
		assertionBinders[context, label],
		termApply[
			context["Semantics"]["Reflexivity"][definition["Head"]],
			{translateTree[Append[context, "VariableTypecodes" -> variableTypecodesOf[context["Database"], label]], frameOf[context, label]["Dependencies"], definition["Left"]]}
		]
	],
	"translation"
]

(* a step's term: closed over the setvar variables of the proof *)
stepTerm[context_, savedStep[index_Integer]] := stepSymbol[index]

stepTerm[context_, hypothesisStep[index_Integer]] := termFunction[
	setvarBinders[context, context["ProofSetvars"]],
	termApply[hypothesisSymbol[index], Map[variableSymbol, context["Frame"]["Setvars"]]]
]

stepTerm[context_, assertionStep[label_String, substitution_Association, hypotheses_List]] := With[
	{
		frame = frameOf[context, label],
		recall = Function[step, termApply[stepTerm[context, step], Map[variableSymbol, context["ProofSetvars"]]]]
	},
	With[{images = Map[Function[setvar, First[substitution[setvar]]], frame["Setvars"]]},
		If[ ! DuplicateFreeQ[images],
			Throw[Failure["AliasedApplication", <|
				"MessageTemplate" -> "The step applies `1` with the same variable for two of its setvar variables, which needs a variant of it.",
				"MessageParameters" -> {label}
			|>], "translation"]
		];
		termFunction[
			setvarBinders[context, context["ProofSetvars"]],
			termApply[
				assertionReference[context, label],
				Join[
					Map[
						Function[other,
							termFunction[
								setvarBinders[context, Map[Function[setvar, First[substitution[setvar]]], frame["Dependencies"][First[other]]]],
								translateTree[context, proofDependencies[context], substitution[First[other]]]
							]
						],
						frame["Others"]
					],
					Map[Function[step, termFunction[setvarBinders[context, images], recall[step]]], hypotheses],
					Map[variableSymbol, images]
				]
			]
		]
	]
]

(* the variables of the theorem's frame, applied to their dependencies; a dummy is not among them *)
proofDependencies[context_] := context["Frame"]["Dependencies"]

(* every assertion is declared under its label, an axiom proved as the semantics proves it *)
assertionReference[context_, label_String] := label


(* ::Subsection:: *)
(*Running a proof*)


(* the proof run on a stack: each step is a syntax tree, of a floating hypothesis or a syntax axiom, or a proof step, with
   the tree of what it proves; every application is checked as Metamath checks it, its essential hypotheses matched
   against the trees of their proofs, and the result against the theorem's statement *)
runProof[context_, label_String] := Module[
	{
		database = context["Database"],
		statement, proof, stack = {}, saved = <||>, savedProofs = {}, setvars = {}, typecodes = <||>, result
	},
	statement = database["Statements"][label];
	proof = databaseProof[database, label];
	typecodes = variableTypecodesOf[database, label];
	Scan[
		Function[step,
			Switch[step,
				(* a saved proof step is let-bound once and used by name; a saved syntax tree is copied *)
				markStep[_Integer],
					If[ MatchQ[Last[stack], proofItem[_, _]],
						AppendTo[savedProofs, Length[savedProofs] + 1 -> First[Last[stack]]];
						stack = Append[Most[stack], proofItem[savedStep[Length[savedProofs]], Last[Last[stack]]]]
					];
					saved[First[step]] = Last[stack],
				recallStep[_Integer],
					AppendTo[stack, saved[First[step]]],
				Except[_String],
					Throw[Failure["UnknownProofStep", <|"MessageTemplate" -> "The proof of `1` has the step `2`, which is neither a label nor a saved step.", "MessageParameters" -> {label, step}|>], "translation"],
				_,
					With[{item = proofItemOf[context, label, statement, step, stack]},
						stack = Append[Drop[stack, -First[item]], Last[item]];
						If[ MatchQ[Last[item], syntaxItem[variableNode[_], _]],
							With[{variable = First[First[Last[item]]], typecode = Last[Last[item]]},
								typecodes[variable] = typecode;
								If[binderTypecodeQ[context, typecode], setvars = Union[setvars, {variable}]]
							]
						]
					]
			]
		],
		proof
	];
	result = Last[stack];
	If[ Length[stack] =!= 1 || ! MatchQ[result, proofItem[_, _]] || Last[result] =!= confirmTree[statementTree[database, label]],
		Throw[Failure["ProofMismatch", <|"MessageTemplate" -> "The proof of `1` does not end in its statement.", "MessageParameters" -> {label}|>], "translation"]
	];
	<|"Result" -> First[result], "Saved" -> savedProofs, "Setvars" -> setvars, "VariableTypecodes" -> typecodes|>
]

(* the item a label pushes, with the number of items it pops *)
proofItemOf[context_, theorem_String, statement_, step_String, stack_List] := With[{entry = context["Database"]["Statements"][step]},
	Switch[entry["Kind"],
		"Floating",
			{0, syntaxItem[variableNode[entry["Variable"]], entry["Typecode"]]},
		"Essential",
			{0, proofItem[hypothesisStep[First[FirstPosition[statement["Essential"], step]]], confirmTree[statementTree[context["Database"], theorem, step]]]},
		"Axiom" | "Theorem",
			assertionItem[context, entry, stack]
	]
]

assertionItem[context_, entry_Association, stack_List] := With[
	{
		count = Length[entry["Floating"]] + Length[entry["Essential"]],
		provable = context["Database"]["ProvableTypecode"]
	},
	With[{popped = Take[stack, -count]},
		With[
			{
				substitution = Association[MapThread[
					Function[{floating, item}, Last[floating] -> checkedSyntax[item, floating]],
					{entry["Floating"], Take[popped, Length[entry["Floating"]]]}
				]],
				hypotheses = Drop[popped, Length[entry["Floating"]]]
			},
			If[ entry["Typecode"] === provable,
				MapThread[
					Function[{hypothesis, item},
						If[ ! MatchQ[item, proofItem[_, _]] || Last[item] =!= substituteTree[confirmTree[statementTree[context["Database"], entry["Label"], hypothesis]], substitution],
							Throw[Failure["HypothesisMismatch", <|"MessageTemplate" -> "A hypothesis of `1` does not match its proof.", "MessageParameters" -> {entry["Label"]}|>], "translation"]
						]
					],
					{entry["Essential"], hypotheses}
				];
				{count, proofItem[assertionStep[entry["Label"], substitution, Map[First, hypotheses]], substituteTree[confirmTree[statementTree[context["Database"], entry["Label"]]], substitution]]},
				{count, syntaxItem[syntaxTreeOf[context, entry, substitution], entry["Typecode"]]}
			]
		]
	]
]

checkedSyntax[syntaxItem[tree_, typecode_], {_, typecode_, _}] := tree
checkedSyntax[item_, floating_] := Throw[Failure["SyntaxMismatch", <|
	"MessageTemplate" -> "A step gives `1` where the floating hypothesis `2` is expected.",
	"MessageParameters" -> {Head[item], First[floating]}
|>], "translation"]

(* a syntax axiom builds its node; a syntax theorem, as set.mm's weq, stands for the tree its own proof builds *)
syntaxTreeOf[context_, entry_Association, substitution_Association] := If[entry["Kind"] === "Axiom",
	syntaxNode[entry["Label"], Map[Function[floating, substitution[Last[floating]]], entry["Floating"]]],
	substituteTree[syntaxTheoremTree[context, entry["Label"]], substitution]
]

syntaxTheoremTree[context_, label_String] := Module[{stack = {}},
	Scan[
		Function[step,
			With[{item = proofItemOf[context, label, context["Database"]["Statements"][label], step, stack]},
				stack = Append[Drop[stack, -First[item]], Last[item]]
			]
		],
		databaseProof[context["Database"], label]
	];
	First[Last[stack]]
]

substituteTree[tree_, substitution_Association] := Replace[tree, variableNode[variable_String] :> Lookup[substitution, variable, variableNode[variable]], {0, Infinity}]
