#!/usr/bin/env wolframscript
(* Build the MetamathLink documentation with PacletPage: each docs/paclet/en/**/*.md page whose frontmatter names a page
   template (Symbol, Guide, TechNote) becomes a notebook under MetamathLink/Documentation/English/, and
   docs/paclet/en/ResourceDefinition.md becomes MetamathLink/ResourceDefinition.nb. No cloud login is needed.

       TYPETHEORY_PACLET=/path/to/TypeTheory/TypeTheory wolframscript -f build_docs.wls [--no-cache]

   The pages need TypeTheory's ZFC environment; the tutorial imports 2 + 2 = 4 from set.mm, a few minutes and 0.5 GB. *)

Get[FileNameJoin[{DirectoryName[$InputFileName], "pacletpage.wl"}]]

Print["PacletPage ", loadPacletPage[]]

buildDocumentation[]

Print["done"]
