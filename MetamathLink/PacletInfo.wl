(* ::Package:: *)

PacletObject[<|
	"Name" -> "WolframInstitute/MetamathLink",
	"PublisherID" -> "WolframInstitute",
	"Version" -> "0.2.0",
	"WolframVersion" -> "15.0+",
	"Description" -> "Metamath databases in the TypeTheory proof engine: set.mm's theorems as theorems about the sets of a model of ZFC",
	"Creator" -> "Nikolay Murzin",
	"License" -> "MIT",
	"Keywords" -> {"Metamath", "set.mm", "type theory", "ZFC", "proof translation"},
	"Categories" -> {"Mathematics"},
	"PrimaryContext" -> "WolframInstitute`MetamathLink`",
	"Dependencies" -> {"WolframInstitute/TypeTheory" -> "0.64.*"},
	"Extensions" -> {
		{"Kernel", "Root" -> "Kernel", "Context" -> {"WolframInstitute`MetamathLink`"}},
		{"Documentation", "Language" -> "English", "MainPage" -> "Guides/MetamathLink"},
		{"Test", "Root" -> "Tests", "Method" -> "Experimental-v1"},
		(* PacletBuild packs only the declared extensions: the databases the documentation and the tests read *)
		(* the library for each platform, which scripts/build_library.sh writes *)
		{"Asset", "Assets" -> {{"Binaries", "Binaries"}}},
		{
			"Asset",
			"Root" -> "Data",
			"Assets" -> {
				{"demo0", "demo0.mm"},
				{"setmm-propositional", "setmm-propositional.mm"},
				{"setmm-2p2e4", "setmm-2p2e4.wxf"}
			}
		}
	}
|>]
