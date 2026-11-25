(* ::Package:: *)

(*
set.mm's axioms as theorems over TypeTheoryEnvironment["ZFC"], Aczel's model of ZFC in TypeTheory's library, under their
labels: setmmEnvironment[] is the ZFC environment with them, the base of the ZFC semantics. No declaration here is an
axiom, so an imported theorem's axiom closure is the prelude's propositional extensionality, quotient soundness and
choice, or less.

Each is stated as the translation states it, in higher-order abstract syntax: a setvar variable a bound variable of
"Set", a wff or class variable a function of the setvar variables it may depend on, each hypothesis and the conclusion
closed over the setvar variables; set.mm's x = y is "setClass"[x] == "setClass"[y] and x e. y is
"classElement"["setClass"[x], "setClass"[y]].

	"ax-mp", "ax-1", "ax-2", "ax-3", "df-bi", "df-an", "df-or"     propositional calculus, the connectives native
	"df-tru", "df-fal", "df-ex", "ax-gen", "ax-4" ... "ax-13"     predicate calculus with equality
	"wsb", "df-clab", "df-cleq", "df-clel"                        substitution, as df-sb defines it, and classes
	"ax-ext", "ax-rep", "ax-sep", "ax-nul", "ax-pow", "ax-pr",     ZFC, each from the model's theorem by setmmTheorem
	"ax-un", "ax-reg", "ax-inf", "ax-ac"

The justification hypotheses of df-sb, df-cleq and df-clel are premises the proofs do not use.
*)


(* ::Section:: *)
(*PackageImport*)


PackageImport["WolframInstitute`TypeTheory`"]


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[setmmEnvironment]
PackageScoped[setmmTheorem]
PackageScoped[$setmmDeclarations]


(* ::Section:: *)
(*Usage Messages*)


setmmEnvironment::usage = "setmmEnvironment[] gives TypeTheoryEnvironment[\"ZFC\"] with set.mm's axioms as theorems under their labels, built and checked \
the first time it is asked for."
setmmTheorem::usage = "setmmTheorem[label, statement, proof] gives the theorem label of statement, in set.mm's vocabulary of classes, from proof, a proof \
of the statement read about sets: \"classElement\"[\"setClass\"[t], B] as B[t] and \"setClass\"[a] == \"setClass\"[b] as a == b."
$setmmDeclarations::usage = "$setmmDeclarations is the list of set.mm's axioms as theorems over the ZFC environment, under their labels."


(* ::Section:: *)
(*Function Definitions*)


setmmEnvironment[] := setmmEnvironment[] = TypeTheoryEnvironment[TypeTheoryEnvironment["ZFC"], $setmmDeclarations]

(* a theorem in set.mm's vocabulary from its proof about sets: the held statement with each "classElement"["setClass"[t], B]
   made membership[B, t] is the motive of a substitution along "classElementFunction", and with each
   "setClass"[a] == "setClass"[b] also made equality[a, b], that of one along "setClassEqualFunction"; at the two functions
   (B, z) |-> B[z] and (a, b) |-> a == b the statement is about Element and == of sets, which proof proves *)
SetAttributes[setmmTheorem, HoldAll]
setmmTheorem[name_, statement_, native_] := Module[{membership, equality},
	With[
		{
			byMembership = Hold[statement] /. HoldPattern["classElement"["setClass"[t_], b_]] :> membership[b, t]
		},
		With[{byBoth = byMembership /. HoldPattern["setClass"[a_] == "setClass"[b_]] :> equality[a, b] /. membership -> Function[{Typed[B, "Class"], Typed[z, "Set"]}, B[z]]},
			Replace[
				{byMembership, byBoth, Hold[native]},
				{Hold[k_], Hold[kl_], Hold[proof_]} :> TypeTheoryTheorem[
					name,
					statement,
					Construct[
						"equalitySubstitution",
						TypeSpecifier[{"Class", "Set"} -> TypeUniverse[0]],
						Function[{Typed[membership, TypeSpecifier[{"Class", "Set"} -> TypeUniverse[0]]]}, k],
						Function[{Typed[B, "Class"], Typed[z, "Set"]}, B[z]],
						Function[{Typed[B, "Class"], Typed[z, "Set"]}, "classElement"["setClass"[z], B]],
						"equalitySymmetry"["classElementFunction"],
						Construct[
							"equalitySubstitution",
							TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]],
							Function[{Typed[equality, TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]]}, kl],
							Function[{Typed[a, "Set"], Typed[b, "Set"]}, a == b],
							Function[{Typed[a, "Set"], Typed[b, "Set"]}, "setClass"[a] == "setClass"[b]],
							"equalitySymmetry"["setClassEqualFunction"],
							proof
						]
					]
				]
			]
		]
	]
]

$setmmDeclarations = {
	(* propositional calculus *)
	TypeTheoryTheorem[
		"ax-mp",
		ForAll[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]}, Implies[\[CurlyPhi], Implies[Implies[\[CurlyPhi], \[Psi]], \[Psi]]]],
		Function[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]], Typed[minor, \[CurlyPhi]], Typed[major, Implies[\[CurlyPhi], \[Psi]]]}, major[minor]]
	],
	TypeTheoryTheorem[
		"ax-1",
		ForAll[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]}, Implies[\[CurlyPhi], Implies[\[Psi], \[CurlyPhi]]]],
		Function[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]], Typed[p, \[CurlyPhi]], Typed[q, \[Psi]]}, p]
	],
	TypeTheoryTheorem[
		"ax-2",
		ForAll[
			{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]], Typed[\[Chi], TypeUniverse[0]]},
			Implies[Implies[\[CurlyPhi], Implies[\[Psi], \[Chi]]], Implies[Implies[\[CurlyPhi], \[Psi]], Implies[\[CurlyPhi], \[Chi]]]]
		],
		Function[
			{
				Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]], Typed[\[Chi], TypeUniverse[0]],
				Typed[f, Implies[\[CurlyPhi], Implies[\[Psi], \[Chi]]]], Typed[g, Implies[\[CurlyPhi], \[Psi]]], Typed[p, \[CurlyPhi]]
			},
			f[p, g[p]]
		]
	],
	TypeTheoryTheorem[
		"ax-3",
		ForAll[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]}, Implies[Implies[Not[\[CurlyPhi]], Not[\[Psi]]], Implies[\[Psi], \[CurlyPhi]]]],
		Function[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]], Typed[f, Implies[Not[\[CurlyPhi]], Not[\[Psi]]]], Typed[q, \[Psi]]},
			"doubleNegationElimination"[\[CurlyPhi], Function[{Typed[n, Not[\[CurlyPhi]]]}, f[n, q]]]
		]
	],
	TypeTheoryTheorem[
		"df-bi",
		ForAll[
			{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]},
			Not[Implies[
				Implies[Equivalent[\[CurlyPhi], \[Psi]], Not[Implies[Implies[\[CurlyPhi], \[Psi]], Not[Implies[\[Psi], \[CurlyPhi]]]]]],
				Not[Implies[Not[Implies[Implies[\[CurlyPhi], \[Psi]], Not[Implies[\[Psi], \[CurlyPhi]]]]], Equivalent[\[CurlyPhi], \[Psi]]]]
			]]
		],
		Function[
			{
				Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]],
				Typed[k, Implies[
					Implies[Equivalent[\[CurlyPhi], \[Psi]], Not[Implies[Implies[\[CurlyPhi], \[Psi]], Not[Implies[\[Psi], \[CurlyPhi]]]]]],
					Not[Implies[Not[Implies[Implies[\[CurlyPhi], \[Psi]], Not[Implies[\[Psi], \[CurlyPhi]]]]], Equivalent[\[CurlyPhi], \[Psi]]]]
				]]
			},
			k[
				Function[{Typed[e, Equivalent[\[CurlyPhi], \[Psi]]], Typed[m, Implies[Implies[\[CurlyPhi], \[Psi]], Not[Implies[\[Psi], \[CurlyPhi]]]]]}, m[e[[1]], e[[2]]]],
				Function[{Typed[b, Not[Implies[Implies[\[CurlyPhi], \[Psi]], Not[Implies[\[Psi], \[CurlyPhi]]]]]]},
					"equivalentIntroduction"[
						"doubleNegationElimination"[Implies[\[CurlyPhi], \[Psi]], Function[{Typed[n, Not[Implies[\[CurlyPhi], \[Psi]]]]},
							b[Function[{Typed[f, Implies[\[CurlyPhi], \[Psi]]]}, Typed["falseElimination"[n[f]], Not[Implies[\[Psi], \[CurlyPhi]]]]]]
						]],
						"doubleNegationElimination"[Implies[\[Psi], \[CurlyPhi]], Function[{Typed[n, Not[Implies[\[Psi], \[CurlyPhi]]]]},
							b[Function[{Typed[f, Implies[\[CurlyPhi], \[Psi]]]}, n]]
						]]
					]
				]
			]
		]
	],
	TypeTheoryTheorem[
		"df-an",
		ForAll[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]}, Equivalent[And[\[CurlyPhi], \[Psi]], Not[Implies[\[CurlyPhi], Not[\[Psi]]]]]],
		Function[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]},
			"equivalentIntroduction"[
				Function[{Typed[a, And[\[CurlyPhi], \[Psi]]], Typed[k, Implies[\[CurlyPhi], Not[\[Psi]]]]}, k[a[[1]], a[[2]]]],
				Function[{Typed[b, Not[Implies[\[CurlyPhi], Not[\[Psi]]]]]},
					"andIntroduction"[
						"doubleNegationElimination"[\[CurlyPhi], Function[{Typed[n, Not[\[CurlyPhi]]]}, b[Function[{Typed[p, \[CurlyPhi]]}, Typed["falseElimination"[n[p]], Not[\[Psi]]]]]]],
						"doubleNegationElimination"[\[Psi], Function[{Typed[n, Not[\[Psi]]]}, b[Function[{Typed[p, \[CurlyPhi]]}, n]]]]
					]
				]
			]
		]
	],
	TypeTheoryTheorem[
		"df-or",
		ForAll[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]}, Equivalent[Or[\[CurlyPhi], \[Psi]], Implies[Not[\[CurlyPhi]], \[Psi]]]],
		Function[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[\[Psi], TypeUniverse[0]]},
			"equivalentIntroduction"[
				Function[{Typed[o, Or[\[CurlyPhi], \[Psi]]], Typed[n, Not[\[CurlyPhi]]]},
					"orElimination"[o, Function[{Typed[p, \[CurlyPhi]]}, Typed["falseElimination"[n[p]], \[Psi]]], Function[{Typed[q, \[Psi]]}, q]]
				],
				Function[{Typed[f, Implies[Not[\[CurlyPhi]], \[Psi]]]},
					"orElimination"["excludedMiddle"[\[CurlyPhi]], Function[{Typed[p, \[CurlyPhi]]}, "orIntroductionLeft"[p]], Function[{Typed[n, Not[\[CurlyPhi]]]}, "orIntroductionRight"[f[n]]]]
				]
			]
		]
	],
	TypeTheoryTheorem[
		"df-tru",
		ForAll[{Typed[x, "Set"]}, Equivalent[True, Implies[ForAll[{Typed[x, "Set"]}, "setClass"[x] == "setClass"[x]], ForAll[{Typed[x, "Set"]}, "setClass"[x] == "setClass"[x]]]]],
		Function[{Typed[x, "Set"]},
			"equivalentIntroduction"[
				Function[{Typed[t, True], Typed[h, ForAll[{Typed[x, "Set"]}, "setClass"[x] == "setClass"[x]]]}, h],
				Function[{Typed[f, Implies[ForAll[{Typed[x, "Set"]}, "setClass"[x] == "setClass"[x]], ForAll[{Typed[x, "Set"]}, "setClass"[x] == "setClass"[x]]]]}, "trueIntroduction"]
			]
		]
	],
	TypeTheoryTheorem[
		"df-fal",
		Equivalent[False, Not[True]],
		"equivalentIntroduction"[
			Function[{Typed[f, False]}, Typed["falseElimination"[f], Not[True]]],
			Function[{Typed[n, Not[True]]}, n["trueIntroduction"]]
		]
	],
	(* predicate calculus *)
	TypeTheoryTheorem[
		"df-ex",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"]}, Equivalent[Exists[{Typed[x, "Set"]}, \[CurlyPhi][x]], Not[ForAll[{Typed[x, "Set"]}, Not[\[CurlyPhi][x]]]]]]
		],
		Function[{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[x, "Set"]},
			"equivalentIntroduction"[
				Function[{Typed[e, Exists[{Typed[x, "Set"]}, \[CurlyPhi][x]]], Typed[n, ForAll[{Typed[x, "Set"]}, Not[\[CurlyPhi][x]]]]},
					"existsElimination"[e, Function[{Typed[w, "Set"], Typed[p, \[CurlyPhi][w]]}, n[w, p]]]
				],
				Function[{Typed[k, Not[ForAll[{Typed[x, "Set"]}, Not[\[CurlyPhi][x]]]]]},
					"doubleNegationElimination"[
						Exists[{Typed[x, "Set"]}, \[CurlyPhi][x]],
						Function[{Typed[n, Not[Exists[{Typed[x, "Set"]}, \[CurlyPhi][x]]]]},
							k[Function[{Typed[w, "Set"], Typed[p, \[CurlyPhi][w]]}, n[Typed["existsIntroduction"[w, p], Exists[{Typed[x, "Set"]}, \[CurlyPhi][x]]]]]]
						]
					]
				]
			]
		]
	],
	TypeTheoryTheorem[
		"ax-gen",
		ForAll[{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]]}, Implies[ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]], ForAll[{Typed[x, "Set"]}, ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]]]]],
		Function[{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[h, ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]]], Typed[x, "Set"], Typed[w, "Set"]}, h[w]]
	],
	TypeTheoryTheorem[
		"ax-4",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[\[Psi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"]}, Implies[
				ForAll[{Typed[x, "Set"]}, Implies[\[CurlyPhi][x], \[Psi][x]]],
				Implies[ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]], ForAll[{Typed[x, "Set"]}, \[Psi][x]]]
			]]
		],
		Function[
			{
				Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[\[Psi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[x, "Set"],
				Typed[f, ForAll[{Typed[x, "Set"]}, Implies[\[CurlyPhi][x], \[Psi][x]]]], Typed[g, ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]]], Typed[w, "Set"]
			},
			f[w, g[w]]
		]
	],
	TypeTheoryTheorem[
		"ax-5",
		ForAll[{Typed[\[CurlyPhi], TypeUniverse[0]]}, ForAll[{Typed[x, "Set"]}, Implies[\[CurlyPhi], ForAll[{Typed[x, "Set"]}, \[CurlyPhi]]]]],
		Function[{Typed[\[CurlyPhi], TypeUniverse[0]], Typed[x, "Set"], Typed[p, \[CurlyPhi]], Typed[w, "Set"]}, p]
	],
	TypeTheoryTheorem[
		"ax-6",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"]}, Not[ForAll[{Typed[x, "Set"]}, Not["setClass"[x] == "setClass"[y]]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[h, ForAll[{Typed[x, "Set"]}, Not["setClass"[x] == "setClass"[y]]]]}, h[y, "equalityReflexivity"["setClass"[y]]]]
	],
	TypeTheoryTheorem[
		"ax-7",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, Implies["setClass"[x] == "setClass"[y], Implies["setClass"[x] == "setClass"[z], "setClass"[y] == "setClass"[z]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[e, "setClass"[x] == "setClass"[y]], Typed[f, "setClass"[x] == "setClass"[z]]},
			"equalityTransitivity"["equalitySymmetry"[e], f]
		]
	],
	TypeTheoryTheorem[
		"ax-8",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, Implies["setClass"[x] == "setClass"[y], Implies["classElement"["setClass"[x], "setClass"[z]], "classElement"["setClass"[y], "setClass"[z]]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[e, "setClass"[x] == "setClass"[y]]},
			Construct["equalitySubstitution", "Class", Function[{Typed[C, "Class"]}, "classElement"[C, "setClass"[z]]], "setClass"[x], "setClass"[y], e]
		]
	],
	TypeTheoryTheorem[
		"ax-9",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, Implies["setClass"[x] == "setClass"[y], Implies["classElement"["setClass"[z], "setClass"[x]], "classElement"["setClass"[z], "setClass"[y]]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[e, "setClass"[x] == "setClass"[y]]},
			Construct["equalitySubstitution", "Class", Function[{Typed[C, "Class"]}, "classElement"["setClass"[z], C]], "setClass"[x], "setClass"[y], e]
		]
	],
	TypeTheoryTheorem[
		"ax-10",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"]}, Implies[Not[ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]]], ForAll[{Typed[x, "Set"]}, Not[ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]]]]]]
		],
		Function[{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[x, "Set"], Typed[n, Not[ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x]]]], Typed[w, "Set"]}, n]
	],
	TypeTheoryTheorem[
		"ax-11",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"], Typed[y, "Set"]}, Implies[
				ForAll[{Typed[x, "Set"]}, ForAll[{Typed[y, "Set"]}, \[CurlyPhi][x, y]]],
				ForAll[{Typed[y, "Set"]}, ForAll[{Typed[x, "Set"]}, \[CurlyPhi][x, y]]]
			]]
		],
		Function[
			{
				Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]], Typed[x, "Set"], Typed[y, "Set"],
				Typed[h, ForAll[{Typed[x, "Set"]}, ForAll[{Typed[y, "Set"]}, \[CurlyPhi][x, y]]]], Typed[v, "Set"], Typed[w, "Set"]
			},
			h[w, v]
		]
	],
	TypeTheoryTheorem[
		"ax-12",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"], Typed[y, "Set"]}, Implies[
				"setClass"[x] == "setClass"[y],
				Implies[ForAll[{Typed[y, "Set"]}, \[CurlyPhi][x, y]], ForAll[{Typed[x, "Set"]}, Implies["setClass"[x] == "setClass"[y], \[CurlyPhi][x, y]]]]
			]]
		],
		Function[
			{
				Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]], Typed[x, "Set"], Typed[y, "Set"],
				Typed[e, "setClass"[x] == "setClass"[y]], Typed[h, ForAll[{Typed[y, "Set"]}, \[CurlyPhi][x, y]]],
				Typed[w, "Set"], Typed[f, "setClass"[w] == "setClass"[y]]
			},
			Construct[
				"equalitySubstitution", "Set", Function[{Typed[s, "Set"]}, \[CurlyPhi][s, y]], x, w,
				"setClassInjective"[x, w, "equalityTransitivity"[e, "equalitySymmetry"[f]]],
				h[y]
			]
		]
	],
	TypeTheoryTheorem[
		"ax-13",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, Implies[Not["setClass"[x] == "setClass"[y]], Implies["setClass"[y] == "setClass"[z], ForAll[{Typed[x, "Set"]}, "setClass"[y] == "setClass"[z]]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[n, Not["setClass"[x] == "setClass"[y]]], Typed[e, "setClass"[y] == "setClass"[z]], Typed[w, "Set"]}, e]
	],
	(* substitution, defined as df-sb defines it, and classes *)
	TypeTheoryDefinition[
		"wsb",
		Function[{Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]], Typed[t, "Set"]},
			ForAll[{Typed[y, "Set"]}, Implies["setClass"[y] == "setClass"[t], ForAll[{Typed[x, "Set"]}, Implies["setClass"[x] == "setClass"[y], \[CurlyPhi][x, t]]]]]
		]
	],
	TypeTheoryTheorem[
		"df-clab",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"], Typed[y, "Set"]}, Equivalent[
				"classElement"["setClass"[x], "classAbstraction"[Function[{Typed[y, "Set"]}, \[CurlyPhi][x, y]]]],
				"wsb"[Function[{Typed[y, "Set"], Typed[x, "Set"]}, \[CurlyPhi][x, y]], x]
			]]
		],
		Function[{Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set"} -> TypeUniverse[0]]], Typed[x, "Set"], Typed[y, "Set"]},
			With[{membership = "classElementSetClass"[x, "classAbstraction"[Function[{Typed[v, "Set"]}, \[CurlyPhi][x, v]]]]},
				"equivalentIntroduction"[
					Function[{Typed[m, "classElement"["setClass"[x], "classAbstraction"[Function[{Typed[v, "Set"]}, \[CurlyPhi][x, v]]]]]},
						Function[{Typed[v, "Set"], Typed[e, "setClass"[v] == "setClass"[x]], Typed[w, "Set"], Typed[f, "setClass"[w] == "setClass"[v]]},
							Construct[
								"equalitySubstitution", "Set", Function[{Typed[s, "Set"]}, \[CurlyPhi][x, s]], x, w,
								"equalitySymmetry"["setClassInjective"[w, x, "equalityTransitivity"[f, e]]],
								membership[[1]][m]
							]
						]
					],
					Function[{Typed[k, "wsb"[Function[{Typed[v, "Set"], Typed[u, "Set"]}, \[CurlyPhi][u, v]], x]]},
						membership[[2]][k[x, "equalityReflexivity"["setClass"[x]], x, "equalityReflexivity"["setClass"[x]]]]
					]
				]
			]
		]
	],
	TypeTheoryTheorem[
		"df-cleq",
		ForAll[
			{Typed[A, "Class"], Typed[B, "Class"]},
			Implies[
				ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]},
					Equivalent["setClass"[y] == "setClass"[z], ForAll[{Typed[u, "Set"]}, Equivalent["classElement"["setClass"[u], "setClass"[y]], "classElement"["setClass"[u], "setClass"[z]]]]]
				],
				Implies[
					ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]},
						Equivalent["setClass"[t] == "setClass"[t], ForAll[{Typed[v, "Set"]}, Equivalent["classElement"["setClass"[v], "setClass"[t]], "classElement"["setClass"[v], "setClass"[t]]]]]
					],
					ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]},
						Equivalent[A == B, ForAll[{Typed[x, "Set"]}, Equivalent["classElement"["setClass"[x], A], "classElement"["setClass"[x], B]]]]
					]
				]
			]
		],
		Function[
			{
				Typed[A, "Class"], Typed[B, "Class"], Typed[h, ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]}, Equivalent["setClass"[y] == "setClass"[z], ForAll[{Typed[u, "Set"]}, Equivalent["classElement"["setClass"[u], "setClass"[y]], "classElement"["setClass"[u], "setClass"[z]]]]]]], Typed[k, ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]}, Equivalent["setClass"[t] == "setClass"[t], ForAll[{Typed[v, "Set"]}, Equivalent["classElement"["setClass"[v], "setClass"[t]], "classElement"["setClass"[v], "setClass"[t]]]]]]],
				Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]
			},
			"equivalentIntroduction"[
				Function[{Typed[e, A == B], Typed[w, "Set"]},
					Construct[
						"equalitySubstitution", "Class", Function[{Typed[C, "Class"]}, Equivalent["classElement"["setClass"[w], A], "classElement"["setClass"[w], C]]], A, B, e,
						"equivalentReflexivity"["classElement"["setClass"[w], A]]
					]
				],
				Function[{Typed[m, ForAll[{Typed[w, "Set"]}, Equivalent["classElement"["setClass"[w], A], "classElement"["setClass"[w], B]]]]},
					"functionExtensionality"[Function[{Typed[w, "Set"]},
						"propositionalExtensionality"["equivalentIntroduction"[
							Function[{Typed[p, A[w]]}, "classElementSetClass"[w, B][[1]][m[w][[1]]["classElementSetClass"[w, A][[2]][p]]]],
							Function[{Typed[p, B[w]]}, "classElementSetClass"[w, A][[1]][m[w][[2]]["classElementSetClass"[w, B][[2]][p]]]]
						]]
					]]
				]
			]
		]
	],
	TypeTheoryTheorem[
		"df-clel",
		ForAll[
			{Typed[A, "Class"], Typed[B, "Class"]},
			Implies[
				ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]},
					Equivalent["classElement"["setClass"[y], "setClass"[z]], Exists[{Typed[u, "Set"]}, And["setClass"[u] == "setClass"[y], "classElement"["setClass"[u], "setClass"[z]]]]]
				],
				Implies[
					ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]},
						Equivalent["classElement"["setClass"[t], "setClass"[t]], Exists[{Typed[v, "Set"]}, And["setClass"[v] == "setClass"[t], "classElement"["setClass"[v], "setClass"[t]]]]]
					],
					ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]},
						Equivalent["classElement"[A, B], Exists[{Typed[x, "Set"]}, And["setClass"[x] == A, "classElement"["setClass"[x], B]]]]
					]
				]
			]
		],
		Function[
			{
				Typed[A, "Class"], Typed[B, "Class"], Typed[h, ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]}, Equivalent["classElement"["setClass"[y], "setClass"[z]], Exists[{Typed[u, "Set"]}, And["setClass"[u] == "setClass"[y], "classElement"["setClass"[u], "setClass"[z]]]]]]], Typed[k, ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]}, Equivalent["classElement"["setClass"[t], "setClass"[t]], Exists[{Typed[v, "Set"]}, And["setClass"[v] == "setClass"[t], "classElement"["setClass"[v], "setClass"[t]]]]]]],
				Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]
			},
			"equivalentIntroduction"[
				Function[{Typed[m, "classElement"[A, B]]},
					"existsElimination"[m, Function[{Typed[a, "Set"], Typed[q, And[A == "setClass"[a], B[a]]]},
						Typed[
							"existsIntroduction"[a, "andIntroduction"["equalitySymmetry"[q[[1]]], "classElementSetClass"[a, B][[2]][q[[2]]]]],
							Exists[{Typed[w, "Set"]}, And["setClass"[w] == A, "classElement"["setClass"[w], B]]]
						]
					]]
				],
				Function[{Typed[m, Exists[{Typed[w, "Set"]}, And["setClass"[w] == A, "classElement"["setClass"[w], B]]]]},
					"existsElimination"[m, Function[{Typed[a, "Set"], Typed[q, And["setClass"[a] == A, "classElement"["setClass"[a], B]]]},
						Typed[
							"existsIntroduction"[a, "andIntroduction"["equalitySymmetry"[q[[1]]], "classElementSetClass"[a, B][[1]][q[[2]]]]],
							"classElement"[A, B]
						]
					]]
				]
			]
		]
	],
	(* the axioms of ZFC, from the model's *)
	setmmTheorem[
		"ax-ext",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, Implies[
			ForAll[{Typed[z, "Set"]}, Equivalent["classElement"["setClass"[z], "setClass"[x]], "classElement"["setClass"[z], "setClass"[y]]]],
			"setClass"[x] == "setClass"[y]
		]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, "extensionality"[x, y]]
	],
	setmmTheorem[
		"ax-rep",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set", "Set", "Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]}, Implies[
				ForAll[{Typed[w, "Set"]}, Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"]}, Implies[ForAll[{Typed[y, "Set"]}, \[CurlyPhi][x, y, z, w]], "setClass"[z] == "setClass"[y]]]]],
				Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"]}, Equivalent[
					"classElement"["setClass"[z], "setClass"[y]],
					Exists[{Typed[w, "Set"]}, And["classElement"["setClass"[w], "setClass"[x]], ForAll[{Typed[y, "Set"]}, \[CurlyPhi][x, y, z, w]]]]
				]]]
			]]
		],
		Function[{Typed[\[CurlyPhi], TypeSpecifier[{"Set", "Set", "Set", "Set"} -> TypeUniverse[0]]], Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]},
			"replacement"[Function[{Typed[v, "Set"], Typed[u, "Set"]}, ForAll[{Typed[s, "Set"]}, \[CurlyPhi][x, s, v, u]]], x]
		]
	],
	setmmTheorem[
		"ax-sep",
		ForAll[
			{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]]},
			ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, Exists[{Typed[y, "Set"]}, ForAll[{Typed[x, "Set"]}, Equivalent[
				"classElement"["setClass"[x], "setClass"[y]],
				And["classElement"["setClass"[x], "setClass"[z]], \[CurlyPhi][x]]
			]]]]
		],
		Function[{Typed[\[CurlyPhi], TypeSpecifier[{"Set"} -> TypeUniverse[0]]], Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]},
			Typed[
				"existsIntroduction"["separationSet"[z, \[CurlyPhi]], "elementOfSeparation"[z, \[CurlyPhi]]],
				Exists[{Typed[s, "Set"]}, ForAll[{Typed[c, "Set"]}, Equivalent[Element[c, s], And[Element[c, z], \[CurlyPhi][c]]]]]
			]
		]
	],
	setmmTheorem[
		"ax-nul",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"]}, Exists[{Typed[x, "Set"]}, ForAll[{Typed[y, "Set"]}, Not["classElement"["setClass"[y], "setClass"[x]]]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"]},
			Typed["existsIntroduction"["emptySet", "emptySetEmpty"], Exists[{Typed[s, "Set"]}, ForAll[{Typed[c, "Set"]}, Not[Element[c, s]]]]]
		]
	],
	setmmTheorem[
		"ax-pow",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]}, Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"]}, Implies[
			ForAll[{Typed[w, "Set"]}, Implies["classElement"["setClass"[w], "setClass"[z]], "classElement"["setClass"[w], "setClass"[x]]]],
			"classElement"["setClass"[z], "setClass"[y]]
		]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]},
			Typed[
				"existsIntroduction"["powerSet"[x], Function[{Typed[c, "Set"]}, "elementOfPower"[x, c][[2]]]],
				Exists[{Typed[s, "Set"]}, ForAll[{Typed[c, "Set"]}, Implies[ForAll[{Typed[d, "Set"]}, Implies[Element[d, c], Element[d, x]]], Element[c, s]]]]
			]
		]
	],
	setmmTheorem[
		"ax-pr",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]}, Exists[{Typed[z, "Set"]}, ForAll[{Typed[w, "Set"]}, Implies[
			Or["setClass"[w] == "setClass"[x], "setClass"[w] == "setClass"[y]],
			"classElement"["setClass"[w], "setClass"[z]]
		]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]},
			Typed[
				"existsIntroduction"["pairSet"[x, y], Function[{Typed[c, "Set"]}, "elementOfPair"[x, y, c][[2]]]],
				Exists[{Typed[s, "Set"]}, ForAll[{Typed[c, "Set"]}, Implies[Or[c == x, c == y], Element[c, s]]]]
			]
		]
	],
	setmmTheorem[
		"ax-un",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]}, Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"]}, Implies[
			Exists[{Typed[w, "Set"]}, And["classElement"["setClass"[z], "setClass"[w]], "classElement"["setClass"[w], "setClass"[x]]]],
			"classElement"["setClass"[z], "setClass"[y]]
		]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]},
			Typed[
				"existsIntroduction"["unionSet"[x], Function[{Typed[c, "Set"], Typed[m, Exists[{Typed[d, "Set"]}, And[Element[c, d], Element[d, x]]]]},
					"elementOfUnion"[x, c][[2]]["existsElimination"[m, Function[{Typed[d, "Set"], Typed[k, And[Element[c, d], Element[d, x]]]},
						Typed["existsIntroduction"[d, "andIntroduction"[k[[2]], k[[1]]]], Exists[{Typed[e, "Set"]}, And[Element[e, x], Element[c, e]]]]
					]]]
				]],
				Exists[{Typed[s, "Set"]}, ForAll[{Typed[c, "Set"]}, Implies[Exists[{Typed[d, "Set"]}, And[Element[c, d], Element[d, x]]], Element[c, s]]]]
			]
		]
	],
	setmmTheorem[
		"ax-reg",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, Implies[
			Exists[{Typed[y, "Set"]}, "classElement"["setClass"[y], "setClass"[x]]],
			Exists[{Typed[y, "Set"]}, And["classElement"["setClass"[y], "setClass"[x]], ForAll[{Typed[z, "Set"]}, Implies["classElement"["setClass"[z], "setClass"[y]], Not["classElement"["setClass"[z], "setClass"[x]]]]]]]
		]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"]}, "regularity"[x]]
	],
	setmmTheorem[
		"ax-inf",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]}, Exists[{Typed[y, "Set"]}, And[
			"classElement"["setClass"[x], "setClass"[y]],
			ForAll[{Typed[z, "Set"]}, Implies["classElement"["setClass"[z], "setClass"[y]], Exists[{Typed[w, "Set"]}, And["classElement"["setClass"[z], "setClass"[w]], "classElement"["setClass"[w], "setClass"[y]]]]]]
		]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"]}, "infinity"[x]]
	],
	setmmTheorem[
		"ax-ac",
		ForAll[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]}, Exists[{Typed[y, "Set"]}, ForAll[{Typed[z, "Set"]}, ForAll[{Typed[w, "Set"]}, Implies[
			And["classElement"["setClass"[z], "setClass"[w]], "classElement"["setClass"[w], "setClass"[x]]],
			Exists[{Typed[v, "Set"]}, ForAll[{Typed[u, "Set"]}, Equivalent[
				Exists[{Typed[t, "Set"]}, And[And["classElement"["setClass"[u], "setClass"[w]], "classElement"["setClass"[w], "setClass"[t]]], And["classElement"["setClass"[u], "setClass"[t]], "classElement"["setClass"[t], "setClass"[y]]]]],
				"setClass"[u] == "setClass"[v]
			]]]
		]]]]],
		Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[z, "Set"], Typed[w, "Set"], Typed[v, "Set"], Typed[u, "Set"], Typed[t, "Set"]}, "choiceAxiom"[x]]
	]
}
