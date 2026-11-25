(* ::Package:: *)

(*
The translation's terms as TypeTheory's core terms, the kernel's own locally nameless representation, which a
declaration takes as it is: TypeTheory's kernel checks them without elaborating surface syntax first. LeanLink gives its
declarations core terms the same way.

	Inactive[ForAll][{Typed[x, A], ...}, B]      dependentFunctionType[HoldComplete[x], A, B, "Explicit"], one per binder
	Inactive[Function][{Typed[x, A], ...}, b]    lambdaAbstraction, one per binder
	Inactive[Implies][A, B]                      a dependentFunctionType whose body does not mention its variable
	Inactive[TypeSpecifier][{A, ...} -> B]       the same, one per argument
	Inactive[With][{Inactive[Set][x, Inactive[Typed][v, A]]}, b]
	                                             localDefinition[HoldComplete[x], A, v, b]
	Inactive[Not | And | Or | Equivalent][...]   the prelude's constants applied
	Inactive[Equal][a, b], Inactive[Exists][...] Equal and Exists at their implicit type, which the semantics names
	"name", True, False                          constantReference[HoldComplete[name], {}]
	f[a, ...]                                    application, one per argument

A bound variable becomes its de Bruijn index, the innermost binder of its symbol, so that the shadowing of a setvar
variable by a binder of the same symbol is Metamath's. A term with no core form here, as a proof the semantics gives in
surface syntax, is declared in surface syntax instead.
*)


(* ::Section:: *)
(*PackageImport*)


PackageImport["WolframInstitute`TypeTheory`"]


(* ::Section:: *)
(*PackageExported*)




(* ::Section:: *)
(*PackageScoped*)


PackageScoped[coreTerm]
PackageScoped[coreDeclaration]


(* ::Section:: *)
(*Usage Messages*)


coreTerm::usage = "coreTerm[semantics, term] gives the core term of the inactive term of the translation, or Failure[\"NoCoreForm\", ...] when a part of \
it has none here."
coreDeclaration::usage = "coreDeclaration[semantics, head, name, terms...] gives the declaration head[name, terms...] with its terms as core terms, or None \
when one has no core form."


(* ::Section:: *)
(*Function Definitions*)


coreHead[name_String] := coreHead[name] = Symbol["WolframInstitute`TypeTheory`PackageScope`" <> name]

coreTerm[semantics_Association, term_] := Catch[
	Block[{$coreSemantics = semantics}, core[term, {}]],
	"core"
]

coreDeclaration[semantics_Association, head_, name_String, terms___] := With[{cores = Map[Function[term, coreTerm[semantics, term]], {terms}]},
	If[ AnyTrue[cores, FailureQ],
		None,
		head @@ Prepend[cores, name]
	]
]

(* a definition takes its value with its type, Typed[value, type], both core terms *)
coreDeclaration[semantics_Association, TypeTheoryDefinition, name_String, Inactive[Typed][value_, type_]] := With[
	{cores = {coreTerm[semantics, value], coreTerm[semantics, type]}},
	If[ AnyTrue[cores, FailureQ],
		None,
		(* the declaration holds its arguments: the parts go in by With *)
		With[{coreValue = First[cores], coreType = Last[cores]}, TypeTheoryDefinition[name, Typed[coreValue, coreType]]]
	]
]

noCoreForm[term_] := Throw[Failure["NoCoreForm", <|"MessageTemplate" -> "`1` has no core form here.", "MessageParameters" -> {Short[HoldForm[term], 2]}|>], "core"]

constant[name_] := coreHead["constantReference"][HoldComplete[name], {}]
constant[name_, levels_List] := coreHead["constantReference"][HoldComplete[name], levels]

applied[function_, arguments_List] := Fold[Function[{head, argument}, Construct[coreHead["application"], head, argument]], function, arguments]

anonymous = Symbol["WolframInstitute`MetamathLink`Variables`anonymous"]

(* the scope: the symbols bound around a term, the innermost first *)
core[symbol_Symbol, scope_List] := Which[
	MemberQ[scope, symbol],
		coreHead["boundVariable"][First[FirstPosition[scope, symbol, {0}, {1}, Heads -> False]] - 1],
	symbol === True || symbol === False,
		constant[symbol],
	True,
		noCoreForm[symbol]
]

core[name_String, scope_List] := constant[name]

core[Inactive[TypeUniverse][level_Integer], scope_List] := coreHead["universeSort"][level]

core[Inactive[head : ForAll | Function][{}, body_], scope_List] := core[body, scope]
core[Inactive[head : ForAll | Function][{Inactive[Typed][symbol_Symbol, type_], rest___}, body_], scope_List] := Construct[
	coreHead[If[head === ForAll, "dependentFunctionType", "lambdaAbstraction"]],
	HoldComplete[symbol],
	core[type, scope],
	core[Inactive[head][{rest}, body], Prepend[scope, symbol]],
	"Explicit"
]

core[Inactive[Implies][premise_, conclusion_], scope_List] := Construct[
	coreHead["dependentFunctionType"], HoldComplete[anonymous], core[premise, scope], core[conclusion, Prepend[scope, anonymous]], "Explicit"
]

core[Inactive[TypeSpecifier][{} -> result_], scope_List] := core[result, scope]
core[Inactive[TypeSpecifier][{argument_, rest___} -> result_], scope_List] := Construct[
	coreHead["dependentFunctionType"], HoldComplete[anonymous], core[argument, scope], core[Inactive[TypeSpecifier][{rest} -> result], Prepend[scope, anonymous]], "Explicit"
]

core[Inactive[With][{Inactive[Set][symbol_Symbol, Inactive[Typed][value_, type_]]}, body_], scope_List] := Construct[
	coreHead["localDefinition"], HoldComplete[symbol], core[type, scope], core[value, scope], core[body, Prepend[scope, symbol]]
]

(* a type annotation that is not a binder only guides elaboration *)
core[Inactive[Typed][value_, _], scope_List] := core[value, scope]

core[Inactive[head : Not | And | Or | Equivalent][arguments___], scope_List] := applied[constant[head], Map[Function[argument, core[argument, scope]], {arguments}]]

core[Inactive[Equal][left_, right_], scope_List] := With[{type = $coreSemantics["EqualityType"]},
	applied[constant[Equal, {$coreSemantics["TypeLevels"][type]}], {core[type, scope], core[left, scope], core[right, scope]}]
]

core[Inactive[Exists][{binder : Inactive[Typed][_Symbol, type_]}, body_], scope_List] := applied[
	constant[Exists, {$coreSemantics["TypeLevels"][type]}],
	{core[type, scope], core[Inactive[Function][{binder}, body], scope]}
]

(* reflexivity of equality, the one polymorphic constant a translation applies, at the type of equalities *)
core["equalityReflexivity"[value_], scope_List] := With[{type = $coreSemantics["EqualityType"]},
	applied[constant["equalityReflexivity", {$coreSemantics["TypeLevels"][type]}], {core[type, scope], core[value, scope]}]
]

core[head_[arguments___], scope_List] /; ! MatchQ[head, _Inactive | _Symbol?(Function[symbol, Context[symbol] === "System`"])] :=
	applied[core[head, scope], Map[Function[argument, core[argument, scope]], {arguments}]]

core[term_, _] := noCoreForm[term]
