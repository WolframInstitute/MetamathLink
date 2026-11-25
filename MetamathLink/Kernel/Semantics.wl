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
	"LibraryAssertions"        the axioms the environment proves under their labels, each checked against its translation
	"LibraryDefinitions"       the syntax the environment defines under its label, checked against its df- axiom
	"AxiomVariants"            name -> HoldComplete[proof]: the variants of axioms with setvar variables identified, ax-7{z:=y}
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
	"LibraryAssertions" -> {},
	"LibraryDefinitions" -> {},
	"AxiomVariants" -> <||>,
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
	"AxiomProofs" -> <||>,
	(* the axioms the ZFC library proves under their labels, and the syntax it defines as their df- axioms do *)
	"LibraryAssertions" -> {
		"ax-mp", "ax-1", "ax-2", "ax-3", "df-bi", "df-an", "df-or", "df-tru", "df-fal", "df-ex",
		"ax-gen", "ax-4", "ax-5", "ax-6", "ax-7", "ax-8", "ax-9", "ax-10", "ax-11", "ax-12", "ax-13",
		"df-clab", "df-cleq", "df-clel",
		"ax-ext", "ax-rep", "ax-sep", "ax-nul", "ax-pow", "ax-pr", "ax-un", "ax-reg", "ax-inf", "ax-ac"
	},
	"LibraryDefinitions" -> {"wsb"},
	"AxiomVariants" -> $zfcAxiomVariants,
	"DefinitionHeads" -> {"wb", "wceq"},
	"Reflexivity" -> <|"wb" -> "equivalentReflexivity", "wceq" -> "equalityReflexivity"|>
|>

(* the variants of set.mm's axioms that proofs apply: an axiom whose setvar variables have no $d may be applied with two of
   them the same, which in higher-order abstract syntax is another statement *)
$zfcAxiomVariants := <|
	"ax-7{z:=y}" -> HoldComplete[Function[{Typed[x, "Set"], Typed[y, "Set"], Typed[e, "setClass"[x] == "setClass"[y]], Typed[f, "setClass"[x] == "setClass"[y]]},
		"equalityReflexivity"["setClass"[y]]
	]]
|>
