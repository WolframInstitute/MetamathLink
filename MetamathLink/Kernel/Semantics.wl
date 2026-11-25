(* ::Package:: *)

(*
The semantics a translation gives a database: what its typecodes are, which typecode binds, what each primitive syntax
axiom denotes and how each axiom is proved.

	"Axiomatic"   any database: wff is Prop, every other typecode a declared type, every syntax axiom a declared constant
	              and every logical axiom an axiom of the environment
	"ZFC"         set.mm over TypeTheoryEnvironment["ZFC"]: setvar is "Set", class "Class" and wff Prop; the primitive
	              syntax denotes the connectives, the quantifiers and the class vocabulary of the ZFC library, the other
	              syntax is defined by its df- axiom, and every axiom is a theorem

A semantics is an association:

	"Name", "Environment"      its name and the environment it extends
	"BinderTypecodes"          the typecodes whose variables are bound variables, {"setvar"} or {}
	"TypecodeTypes"            the type of the terms of each typecode
	"Inhabitants"              a term of each typecode, for the dummy variables of proofs
	"Syntax"                   label -> Function[{translate, arguments}, term]: a primitive syntax axiom, its arguments
	                           by variable name
	"AxiomProofs"              label -> proof: the proof of an axiom, an inactive term or the name of a theorem
	"DefinitionHeads"          the syntax of the defining axioms, ( C <-> D ) and C = D
	"Reflexivity"              head -> the reflexivity that proves a defining axiom of that head
*)


(* ::Section:: *)
(*PackageImport*)


PackageImport["WolframInstitute`TypeTheory`"]


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[metamathSemantics]


(* ::Section:: *)
(*Usage Messages*)


metamathSemantics::usage = "metamathSemantics[\"Axiomatic\"] and metamathSemantics[\"ZFC\"] give the two semantics of a translation."


(* ::Section:: *)
(*Function Definitions*)


metamathSemantics["Axiomatic"] := <|
	"Name" -> "Axiomatic",
	"Environment" :> TypeTheoryEnvironment["Prelude"],
	"BinderTypecodes" -> {},
	"TypecodeTypes" -> <|"wff" -> Inactive[TypeUniverse][0]|>,
	"Inhabitants" -> <||>,
	"Syntax" -> <||>,
	"AxiomProofs" -> <||>,
	"DefinitionHeads" -> {},
	"Reflexivity" -> <||>
|>

setSymbol[variable_] := variableSymbol[First[variable]]

binding[variable_] := {Inactive[Typed][setSymbol[variable], "Set"]}

metamathSemantics["ZFC"] := <|
	"Name" -> "ZFC",
	"Environment" :> TypeTheoryEnvironment["ZFC"],
	"BinderTypecodes" -> {"setvar"},
	"TypecodeTypes" -> <|"setvar" -> "Set", "class" -> "Class", "wff" -> Inactive[TypeUniverse][0]|>,
	"Inhabitants" -> <|"setvar" -> "emptySet", "wff" -> True, "class" -> "setClass"["emptySet"]|>,
	"Syntax" -> <|
		"wn" -> Function[{translate, arguments}, Inactive[Not][translate[arguments["ph"]]]],
		"wi" -> Function[{translate, arguments}, Inactive[Implies][translate[arguments["ph"]], translate[arguments["ps"]]]],
		"wb" -> Function[{translate, arguments}, Inactive[Equivalent][translate[arguments["ph"]], translate[arguments["ps"]]]],
		"wa" -> Function[{translate, arguments}, Inactive[And][translate[arguments["ph"]], translate[arguments["ps"]]]],
		"wo" -> Function[{translate, arguments}, Inactive[Or][translate[arguments["ph"]], translate[arguments["ps"]]]],
		"wtru" -> Function[{translate, arguments}, True],
		"wfal" -> Function[{translate, arguments}, False],
		"wal" -> Function[{translate, arguments}, Inactive[ForAll][binding[arguments["x"]], translate[arguments["ph"]]]],
		"wex" -> Function[{translate, arguments}, Inactive[Exists][binding[arguments["x"]], translate[arguments["ph"]]]],
		"cv" -> Function[{translate, arguments}, "setClass"[setSymbol[arguments["x"]]]],
		"wceq" -> Function[{translate, arguments}, Inactive[Equal][translate[arguments["A"]], translate[arguments["B"]]]],
		"wcel" -> Function[{translate, arguments}, "classElement"[translate[arguments["A"]], translate[arguments["B"]]]],
		"cab" -> Function[{translate, arguments}, "classAbstraction"[Inactive[Function][binding[arguments["x"]], translate[arguments["ph"]]]]]
	|>,
	"AxiomProofs" -> $zfcAxiomProofs,
	"DefinitionHeads" -> {"wb", "wceq"},
	"Reflexivity" -> <|"wb" -> "equivalentReflexivity", "wceq" -> "equalityReflexivity"|>
|>

(* the axioms of propositional logic and the definitions of its primitive connectives, proved from the prelude; they move
   to the ZFC library as named theorems *)
$zfcAxiomProofs := <|
	"ax-mp" -> Inactive[Function][
		{Inactive[Typed][φ, Inactive[TypeUniverse][0]], Inactive[Typed][ψ, Inactive[TypeUniverse][0]], Inactive[Typed][minor, φ], Inactive[Typed][major, Inactive[Implies][φ, ψ]]},
		major[minor]
	],
	"ax-1" -> Inactive[Function][
		{Inactive[Typed][φ, Inactive[TypeUniverse][0]], Inactive[Typed][ψ, Inactive[TypeUniverse][0]], Inactive[Typed][a, φ], Inactive[Typed][b, ψ]},
		a
	],
	"ax-2" -> Inactive[Function][
		{
			Inactive[Typed][φ, Inactive[TypeUniverse][0]], Inactive[Typed][ψ, Inactive[TypeUniverse][0]], Inactive[Typed][χ, Inactive[TypeUniverse][0]],
			Inactive[Typed][f, Inactive[Implies][φ, Inactive[Implies][ψ, χ]]], Inactive[Typed][g, Inactive[Implies][φ, ψ]], Inactive[Typed][a, φ]
		},
		f[a][g[a]]
	],
	"ax-3" -> Inactive[Function][
		{
			Inactive[Typed][φ, Inactive[TypeUniverse][0]], Inactive[Typed][ψ, Inactive[TypeUniverse][0]],
			Inactive[Typed][f, Inactive[Implies][Inactive[Not][φ], Inactive[Not][ψ]]], Inactive[Typed][b, ψ]
		},
		"doubleNegationElimination"[φ, Inactive[Function][{Inactive[Typed][n, Inactive[Not][φ]]}, f[n][b]]]
	],
	"df-bi" -> Inactive[Function][
		{
			Inactive[Typed][φ, Inactive[TypeUniverse][0]], Inactive[Typed][ψ, Inactive[TypeUniverse][0]],
			Inactive[Typed][k, Inactive[Implies][
				Inactive[Implies][Inactive[Equivalent][φ, ψ], Inactive[Not][Inactive[Implies][Inactive[Implies][φ, ψ], Inactive[Not][Inactive[Implies][ψ, φ]]]]],
				Inactive[Not][Inactive[Implies][Inactive[Not][Inactive[Implies][Inactive[Implies][φ, ψ], Inactive[Not][Inactive[Implies][ψ, φ]]]], Inactive[Equivalent][φ, ψ]]]
			]]
		},
		k[
			Inactive[Function][{Inactive[Typed][e, Inactive[Equivalent][φ, ψ]], Inactive[Typed][m, Inactive[Implies][Inactive[Implies][φ, ψ], Inactive[Not][Inactive[Implies][ψ, φ]]]]}, m[Inactive[Part][e, 1], Inactive[Part][e, 2]]],
			Inactive[Function][
				{Inactive[Typed][b, Inactive[Not][Inactive[Implies][Inactive[Implies][φ, ψ], Inactive[Not][Inactive[Implies][ψ, φ]]]]]},
				"equivalentIntroduction"[
					"doubleNegationElimination"[Inactive[Implies][φ, ψ], Inactive[Function][{Inactive[Typed][n, Inactive[Not][Inactive[Implies][φ, ψ]]]},
						b[Inactive[Function][{Inactive[Typed][f, Inactive[Implies][φ, ψ]]}, Inactive[Typed]["falseElimination"[n[f]], Inactive[Not][Inactive[Implies][ψ, φ]]]]]
					]],
					"doubleNegationElimination"[Inactive[Implies][ψ, φ], Inactive[Function][{Inactive[Typed][n, Inactive[Not][Inactive[Implies][ψ, φ]]]},
						b[Inactive[Function][{Inactive[Typed][f, Inactive[Implies][φ, ψ]]}, n]]
					]]
				]
			]
		]
	],
	"df-an" -> Inactive[Function][
		{Inactive[Typed][φ, Inactive[TypeUniverse][0]], Inactive[Typed][ψ, Inactive[TypeUniverse][0]]},
		"equivalentIntroduction"[
			Inactive[Function][{Inactive[Typed][a, Inactive[And][φ, ψ]], Inactive[Typed][k, Inactive[Implies][φ, Inactive[Not][ψ]]]}, k[Inactive[Part][a, 1], Inactive[Part][a, 2]]],
			Inactive[Function][{Inactive[Typed][b, Inactive[Not][Inactive[Implies][φ, Inactive[Not][ψ]]]]},
				"andIntroduction"[
					"doubleNegationElimination"[φ, Inactive[Function][{Inactive[Typed][n, Inactive[Not][φ]]}, b[Inactive[Function][{Inactive[Typed][p, φ]}, Inactive[Typed]["falseElimination"[n[p]], Inactive[Not][ψ]]]]]],
					"doubleNegationElimination"[ψ, Inactive[Function][{Inactive[Typed][n, Inactive[Not][ψ]]}, b[Inactive[Function][{Inactive[Typed][p, φ]}, n]]]]
				]
			]
		]
	],
	"df-or" -> Inactive[Function][
		{Inactive[Typed][φ, Inactive[TypeUniverse][0]], Inactive[Typed][ψ, Inactive[TypeUniverse][0]]},
		"equivalentIntroduction"[
			Inactive[Function][{Inactive[Typed][o, Inactive[Or][φ, ψ]], Inactive[Typed][n, Inactive[Not][φ]]},
				Inactive[InductiveRecursor][Or][
					Inactive[Function][{Inactive[Typed][t, Inactive[Or][φ, ψ]]}, ψ],
					Inactive[Function][{Inactive[Typed][p, φ]}, Inactive[Typed]["falseElimination"[n[p]], ψ]],
					Inactive[Function][{Inactive[Typed][q, ψ]}, q],
					o
				]
			],
			Inactive[Function][{Inactive[Typed][f, Inactive[Implies][Inactive[Not][φ], ψ]]},
				Inactive[InductiveRecursor][Or][
					Inactive[Function][{Inactive[Typed][t, Inactive[Or][φ, Inactive[Not][φ]]]}, Inactive[Or][φ, ψ]],
					Inactive[Function][{Inactive[Typed][p, φ]}, "orIntroductionLeft"[p]],
					Inactive[Function][{Inactive[Typed][n, Inactive[Not][φ]]}, "orIntroductionRight"[f[n]]],
					"excludedMiddle"[φ]
				]
			]
		]
	]
|>
