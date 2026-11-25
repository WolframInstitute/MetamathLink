(* ::Package:: *)

PacletObject[<|
	"Name" -> "WolframInstitute/MetamathLink",
	"PublisherID" -> "WolframInstitute",
	"Version" -> "0.1.0",
	"WolframVersion" -> "15.0+",
	"Description" -> "Metamath databases in the TypeTheory proof engine: set.mm's theorems as theorems about the sets of a model of ZFC",
	"Creator" -> "Nikolay Murzin",
	"License" -> "MIT",
	"Keywords" -> {"Metamath", "set.mm", "type theory", "ZFC", "proof translation"},
	"Categories" -> {"Mathematics"},
	"PrimaryContext" -> "WolframInstitute`MetamathLink`",
	"Dependencies" -> {"WolframInstitute/TypeTheory" -> "0.63.*"},
	"Extensions" -> {
		{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`MetamathLink`"}},
		{"Test", "Root" -> "Tests", "Method" -> "Experimental-v1"}
	}
|>]
