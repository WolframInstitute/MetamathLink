(* ::Package:: *)

(* ::Section::Closed:: *)
(*PackageInitialize*)


(* WolframInstitute`MetamathLink`: Metamath databases in the TypeTheory proof engine. A database read by
   ResourceFunction["MetamathImport"] is parsed, its statements translated to statements of type theory and its
   proofs to proof terms, which TypeTheory's kernel checks again. The feature files import TypeTheory's context, the
   terms they build are TypeTheory's surface syntax. *)

PackageInitialize["WolframInstitute`MetamathLink`",
	<|
		"HiddenImports" -> {},
		"LoadFirstFiles" -> {},
		"LoadLastFiles" -> {},
		"IgnoreFiles" -> {}
	|>
]
