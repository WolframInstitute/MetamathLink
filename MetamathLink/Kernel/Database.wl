(* ::Package:: *)

(*
A Metamath database as MetamathLink reads it: the statements of the file read by MetamathLink's library (Library.wl),
or of a MetamathObject, the value of ResourceFunction["MetamathImport"], each as an association, in the order of the file.

	<|"Kind" -> "Axiom" | "Theorem", "Label" -> label, "Typecode" -> typecode, "Symbols" -> {symbol, ...},
	  "Disjoint" -> {{variable, variable}, ...}, "Floating" -> {{label, typecode, variable}, ...},
	  "Essential" -> {label, ...}|>                                       an assertion, $a or $p
	<|"Kind" -> "Floating", "Label" -> label, "Typecode" -> typecode, "Variable" -> variable|>   a $f hypothesis
	<|"Kind" -> "Essential", "Label" -> label, "Typecode" -> typecode, "Symbols" -> {symbol, ...}|>   a $e hypothesis

The floating hypotheses of an assertion are its mandatory ones, in the order of the file, and its essential ones
follow them: a proof pops them in this order. A theorem's proof is read from the object when it is needed, as a list
of labels with markStep[k] and recallStep[k], the compressed proof's saving and reusing of a step.

The grammar is the syntax axioms, the axioms whose typecode is not the provable one: a statement is parsed as a tree
of syntaxNode[label, {argument, ...}], the arguments in the order of the axiom's floating hypotheses, with
variableNode[variable] at the leaves. The library's grammar, metamath-rs's, parses the statements of a database it reads,
database["Trees"]; a statement it does not parse, as in a database whose grammar is ambiguous where its parser looks ahead,
and every statement of a database MetamathImport read, are parsed here. This parser is a memoized recursive descent that
keeps every parse of every typecode at every position, so the grammar may be ambiguous locally; a statement must have
exactly one parse.
*)


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[metamathDatabase]
PackageScoped[metamathObjectQ]
PackageScoped[databaseStatement]
PackageScoped[databaseProof]
PackageScoped[syntaxNode]
PackageScoped[variableNode]
PackageScoped[markStep]
PackageScoped[recallStep]
PackageScoped[statementTree]
PackageScoped[grammarOf]


(* ::Section:: *)
(*Usage Messages*)


metamathDatabase::usage = "metamathDatabase[object] gives the database of the MetamathObject object, an association of the statements by label, \
their order and its grammar.\nmetamathDatabase[File[path]] reads the file with MetamathLink's library, which verifies it and parses its statements, or \
with ResourceFunction[\"MetamathImport\"] where there is no library; or a database saved as a .wxf file."
metamathObjectQ::usage = "metamathObjectQ[expr] gives True when expr is a MetamathObject, the value of ResourceFunction[\"MetamathImport\"]."
databaseStatement::usage = "databaseStatement[database, label] gives the statement of label, an association, or a Failure if the database has none."
databaseProof::usage = "databaseProof[database, label] gives the proof of the theorem label as a list of labels, markStep[k] and recallStep[k], decoding a \
compressed proof."
syntaxNode::usage = "syntaxNode[label, {argument, ...}] is the syntax axiom label applied to its arguments, in the order of its floating hypotheses."
variableNode::usage = "variableNode[variable] is the variable as a leaf of a parse tree."
markStep::usage = "markStep[k] in a proof saves the step on top of the stack as the k-th saved step."
recallStep::usage = "recallStep[k] in a proof pushes the k-th saved step again."
statementTree::usage = "statementTree[database, label] gives the parse tree of the statement label, its typecode replaced by the typecode of formulas when \
it is the provable one, or a Failure when it has no parse or more than one.\nstatementTree[database, assertion, label] parses the essential hypothesis label \
with the variables of the assertion that has it."
grammarOf::usage = "grammarOf[database] gives the grammar of the database: its syntax axioms as rules by typecode, indexed by their first symbol; \
metamathDatabase keeps it as database[\"Grammar\"]."


(* ::Section:: *)
(*Function Definitions*)


metamathObjectQ[object_] := MatchQ[Head[object], _Symbol] && SymbolName[Head[object]] === "MetamathObject" && MatchQ[object, _[_Association]]

(* the two rules for a file exclude each other, so that neither depends on the order a kernel tries them in *)
metamathDatabase[File[path_String] /; StringEndsQ[path, ".wxf"]] := Replace[Import[path, "WXF"],
	database_Association /; ! KeyExistsQ[database, "Identifier"] :> Append[database, "Identifier" -> CreateUUID["metamath-"]]
]

(* a .mm file is read by MetamathLink's library, verified, with the trees of the statements its grammar parses; where
   there is no library for the platform, by ResourceFunction["MetamathImport"] *)
metamathDatabase[File[path_String] /; ! StringEndsQ[path, ".wxf"]] := Replace[libraryDatabase[path], {
	database_Association :> Join[database, <|"Grammar" -> grammarOf[database], "Identifier" -> CreateUUID["metamath-"]|>],
	Failure["NoLibrary", _] :> metamathDatabase[ResourceFunction["MetamathImport"][File[path]]]
}]

metamathDatabase[object_?metamathObjectQ] := With[
	{
		database = <|
			"Statements" -> Association[KeyValueMap[Function[{label, statement}, label -> normalizedStatement[statement]], First[object]["Statements"]]],
			"Order" -> Keys[First[object]["Statements"]],
			"ProvableTypecode" -> "|-",
			"FormulaTypecode" -> "wff"
		|>
	},
	Join[database, <|"Grammar" -> grammarOf[database], "Identifier" -> CreateUUID["metamath-"]|>]
]

normalizedStatement["Axiom"[label_String, {typecode_String, symbols___String}, {disjoint_List, floating_List, essential_List}]] := <|
	"Kind" -> "Axiom", "Label" -> label, "Typecode" -> typecode, "Symbols" -> {symbols},
	"Disjoint" -> disjoint, "Floating" -> floatingTriple /@ floating, "Essential" -> essentialLabel /@ essential
|>
normalizedStatement["Theorem"[label_String, {typecode_String, symbols___String}, {disjoint_List, floating_List, essential_List}, proof_List]] := <|
	"Kind" -> "Theorem", "Label" -> label, "Typecode" -> typecode, "Symbols" -> {symbols},
	"Disjoint" -> disjoint, "Floating" -> floatingTriple /@ floating, "Essential" -> essentialLabel /@ essential, "Proof" -> proof
|>
normalizedStatement["Hypothesis"[label_String, {typecode_String, variable_String}]] := <|"Kind" -> "Floating", "Label" -> label, "Typecode" -> typecode, "Variable" -> variable|>
normalizedStatement["EssentialHypothesis"[label_String, {typecode_String, symbols___String}]] := <|"Kind" -> "Essential", "Label" -> label, "Typecode" -> typecode, "Symbols" -> {symbols}|>

floatingTriple["Hypothesis"[label_String, {typecode_String, variable_String}]] := {label, typecode, variable}

variableTypecodeRule[{_String, typecode_String, variable_String}] := variable -> typecode
essentialLabel["EssentialHypothesis"[label_String, _List]] := label

databaseStatement[database_Association, label_String] := Lookup[database["Statements"], label, Failure["UnknownLabel", <|
	"MessageTemplate" -> "The database has no statement `1`.",
	"MessageParameters" -> {label}
|>]]

(* a proof as the file has it: a list of labels, or a compressed proof, "(" labels ")" and its letters. A compressed proof
   numbers its steps: 1 to m the theorem's mandatory hypotheses, floating then essential, m + 1 to m + k the labels in the
   parentheses, and beyond them the steps saved by Z, in the order they were saved. A number is written with U to Y as
   digits of base 5 before a last digit A to T of base 20. *)
databaseProof[database_Association, label_String] := decodedProof[database["Statements"][label]]

decodedProof[statement_Association] := Replace[statement["Proof"], {
	{"(", rest___String} :> With[{count = LengthWhile[{rest}, # =!= ")" &]},
		compressedProof[statement, Take[{rest}, count], StringJoin[Drop[{rest}, count + 1]]]
	],
	proof : {___String} :> proof
}]

compressedProof[statement_Association, labels_List, letters_String] := With[
	{
		mandatory = Join[Map[First, statement["Floating"]], statement["Essential"]],
		codes = ToCharacterCode[letters]
	},
	With[{named = Join[mandatory, labels]},
		Last[Fold[
			Function[{state, code},
				Which[
					code === 90,
						{First[state], Append[Last[state], markStep[Count[Last[state], _markStep]]]},
					code >= 85,
						{5 First[state] + code - 84, Last[state]},
					True,
						With[{number = 20 First[state] + code - 64},
							{0, Append[Last[state], If[number <= Length[named], First[Take[named, {number}]], recallStep[number - Length[named] - 1]]]}
						]
				]
			],
			{0, {}},
			codes
		]]
	]
]

(* ::Subsection:: *)
(*The grammar and the parser*)


(* a rule: the label, its symbols with each variable as {variable, typecode}, and its variables in the order of the
   axiom's floating hypotheses, the order of the arguments of its node; the rules of a typecode are indexed by their
   first symbol when it is a constant, and the others are tried at every position *)
grammarOf[database_Association] := Map[
	Function[rules,
		<|
			"ByFirstSymbol" -> GroupBy[Select[rules, Function[rule, StringQ[First[rule["Symbols"]]]]], Function[rule, First[rule["Symbols"]]]],
			"Others" -> Select[rules, Function[rule, ! StringQ[First[rule["Symbols"]]]]]
		|>
	],
	GroupBy[
		Map[
			Function[statement,
				With[{typecodes = Association[Map[variableTypecodeRule, statement["Floating"]]]},
					<|
						"Label" -> statement["Label"],
						"Typecode" -> statement["Typecode"],
						"Symbols" -> Map[Function[symbol, If[KeyExistsQ[typecodes, symbol], {symbol, typecodes[symbol]}, symbol]], statement["Symbols"]],
						"Arguments" -> Map[Last, statement["Floating"]]
					|>
				]
			],
			Select[Values[database["Statements"]], Function[statement, statement["Kind"] === "Axiom" && statement["Typecode"] =!= database["ProvableTypecode"] && statement["Symbols"] =!= {}]]
		],
		Function[rule, rule["Typecode"]]
	]
]

(* A statement's tree is parsed once for a database, which is never changed: a proof applies an assertion at every step,
   and its tree is looked up, not parsed again. The cache is keyed by the database's identifier. No Enclose here: a rule
   puts the whole database into its body, which Enclose would walk at every call. *)
(* memoized as down values, a hash table that takes a new tree in constant time: an association assigned inside a Lookup of
   it is copied at every new key *)
(* the tree MetamathLink's library parsed, if it did *)
statementTree[database_Association, label_String] := Replace[
	cachedTree[database["Identifier"], label],
	_cachedTree :> (cachedTree[database["Identifier"], label] = Lookup[Lookup[database, "Trees", <||>], label, parsedStatementTree[database, label]])
]

statementTree[database_Association, assertion_String, label_String] := Replace[
	cachedTree[database["Identifier"], {assertion, label}],
	_cachedTree :> (cachedTree[database["Identifier"], {assertion, label}] = Lookup[Lookup[database, "Trees", <||>], label, parsedStatementTree[database, assertion, label]])
]

parsedStatementTree[database_Association, label_String] := Replace[
	databaseStatement[database, label],
	statement_Association :> parseSymbols[database, formulaTypecode[database, statement["Typecode"]], statement["Symbols"], floatingTypecodes[statement], label]
]

(* an essential hypothesis is parsed with the variables of an assertion that has it *)
parsedStatementTree[database_Association, assertion_String, label_String] := Replace[
	{databaseStatement[database, assertion], databaseStatement[database, label]},
	{
		{frame_Association, statement_Association} :>
			parseSymbols[database, formulaTypecode[database, statement["Typecode"]], statement["Symbols"], floatingTypecodes[frame], label],
		{___, failure_Failure, ___} :> failure
	}
]

formulaTypecode[database_, typecode_String] := If[typecode === database["ProvableTypecode"], database["FormulaTypecode"], typecode]

floatingTypecodes[statement_Association] := Association[Map[variableTypecodeRule, statement["Floating"]]]

parseSymbols[database_, typecode_String, symbols_List, variableTypecodes_Association, label_String] := Block[
	{
		$parseMemo = <||>,
		$parseTokens = symbols,
		$parseLength = Length[symbols],
		$parseVariables = variableTypecodes,
		$parseRules = database["Grammar"]
	},
	Replace[
		Cases[parsesFrom[typecode, 1], {tree_, position_} /; position === $parseLength + 1 :> tree],
		{
			{tree_} :> tree,
			{} :> Failure["NoParse", <|"MessageTemplate" -> "The statement `1` has no parse as `2`.", "MessageParameters" -> {label, typecode}|>],
			trees_ :> Failure["AmbiguousParse", <|"MessageTemplate" -> "The statement `1` has `2` parses.", "MessageParameters" -> {label, Length[trees]}|>]
		}
	]
]

(* every parse of typecode starting at position: a list of {tree, next position}; the memo is set to {} first, so a
   rule that would call itself at the same position finds no parse there instead of looping *)
parsesFrom[typecode_String, position_Integer] := Lookup[$parseMemo, Key[{typecode, position}],
	$parseMemo[{typecode, position}] = {};
	$parseMemo[{typecode, position}] = Join[
		If[ position <= $parseLength && Lookup[$parseVariables, tokenAt[position], None] === typecode,
			{{variableNode[tokenAt[position]], position + 1}},
			{}
		],
		Catenate[Map[Function[rule, ruleParses[rule, position]], candidateRules[typecode, position]]]
	]
]

tokenAt[position_Integer] := First[Take[$parseTokens, {position}]]

candidateRules[typecode_String, position_Integer] := With[{rules = Lookup[$parseRules, typecode, <|"ByFirstSymbol" -> <||>, "Others" -> {}|>]},
	Join[If[position <= $parseLength, Lookup[rules["ByFirstSymbol"], tokenAt[position], {}], {}], rules["Others"]]
]

(* the states of a rule as its symbols are matched: the variables bound so far and the next position *)
ruleParses[rule_Association, position_Integer] := Map[
	Function[state, {syntaxNode[rule["Label"], Lookup[First[state], rule["Arguments"]]], Last[state]}],
	Fold[advanceStates, {{<||>, position}}, rule["Symbols"]]
]

advanceStates[states_List, constant_String] := Cases[states, {bound_, next_} /; next <= $parseLength && tokenAt[next] === constant :> {bound, next + 1}]
advanceStates[states_List, {variable_String, typecode_String}] := Catenate[Map[
	Function[state, Map[Function[parse, {Append[First[state], variable -> First[parse]], Last[parse]}], parsesFrom[typecode, Last[state]]]],
	states
]]
