# MetamathLink documentation guide

The documentation sources under `docs/paclet/en/` are literate markdown that
[`build_docs.wls`](../../../build_docs.wls) turns into evaluated notebooks with PacletPage, and
[`release.wls`](../../../release.wls) publishes as the
[documentation site](https://www.wolframcloud.com/obj/wolframinstitute/MetamathLink). They follow TypeTheory's
documentation guide, `docs/paclet/en/DOC_GUIDE.md` in the TypeTheory repository: build and read back every output, write
the real result into the `<!-- => ... -->` hint, link every symbol as `[Symbol]()`, never hide what a main function
returns, one output per cell.

What is particular to MetamathLink:

- A database comes from a file in `MetamathLink/Data` or a `.wxf` database MetamathLink saved, so that pages need
  no download of set.mm: `demo0.mm`, set.mm's propositional calculus `setmm-propositional.mm`, and `setmm-2p2e4.wxf`, the
  statements of set.mm that 2p2e4 needs.
- TypeTheory's terms display as TypeTheory shows them: an environment as its summary box, a statement as a term.
- [MetamathImport](https://resources.wolframcloud.com/FunctionRepository/resources/MetamathImport) of the Wolfram Function Repository, whose MetamathObject MetamathLink takes, is linked
  wherever a page names it, and the pages of the symbols that take its object show how in Properties & Relations.
- The tutorial runs in one context; every other page runs each section, and each example between `---`, in a clean one.
