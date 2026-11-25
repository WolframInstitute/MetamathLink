//! Parse trees, as MetamathLink's Wolfram Language code has them: `syntaxNode[label, {argument, ...}]`, the syntax
//! axiom applied to its arguments in the order of its floating hypotheses, with `variableNode[variable]` at the leaves.

use std::collections::HashMap;
use std::ops::Range;

use metamath_rs::statement::{StatementAddress, StatementRef};
use metamath_rs::verify::ProofBuilder;
use metamath_rs::{Database, Formula, StatementType, as_str};

use crate::database::variable_of;
use wolfram_serialize::ToWXF;

/// A node of a parse tree, serialized as the node itself: no head or tag of the enum's own.
#[derive(ToWXF, Debug, Clone, PartialEq)]
#[wolfram(enum_head = false)]
pub enum Tree {
    Syntax(SyntaxNode),
    Variable(VariableNode),
}

/// `syntaxNode[label, {argument, ...}]`
#[derive(ToWXF, Debug, Clone, PartialEq)]
#[wolfram(symbol = "WolframInstitute`MetamathLink`PackageScope`syntaxNode")]
pub struct SyntaxNode(pub String, pub Vec<Tree>);

/// `variableNode[variable]`
#[derive(ToWXF, Debug, Clone, PartialEq)]
#[wolfram(symbol = "WolframInstitute`MetamathLink`PackageScope`variableNode")]
pub struct VariableNode(pub String);

/// The tree of a parsed formula. metamath-rs keeps the children of a node in the order their variables appear in the
/// syntax axiom; its syntax proof puts them in the order of the axiom's floating hypotheses, as a proof pops them, so the
/// tree is built as that proof is. Each node is built once and moved into its parent: the builder's items are indices.
pub fn formula_tree(
    database: &Database,
    formula: &Formula,
    at: &HashMap<StatementAddress, StatementRef<'_>>,
) -> Tree {
    let mut builder = TreeBuilder {
        at,
        nodes: Vec::new(),
    };
    let root = formula
        .as_ref(database)
        .build_syntax_proof::<usize, Vec<usize>>(&mut Vec::new(), &mut builder);
    builder.take(root)
}

struct TreeBuilder<'a, 'b> {
    at: &'a HashMap<StatementAddress, StatementRef<'b>>,
    nodes: Vec<Option<Tree>>,
}

impl TreeBuilder<'_, '_> {
    fn take(&mut self, index: usize) -> Tree {
        self.nodes[index]
            .take()
            .expect("a node of a parse tree is used once")
    }
}

impl ProofBuilder for TreeBuilder<'_, '_> {
    type Item = usize;
    type Accum = Vec<usize>;

    fn push(&mut self, arguments: &mut Vec<usize>, argument: usize) {
        arguments.push(argument);
    }

    fn build(
        &mut self,
        address: StatementAddress,
        arguments: Vec<usize>,
        _: &[u8],
        _: Range<usize>,
    ) -> usize {
        // a node names a syntax axiom, or a variable through its floating hypothesis
        let statement = &self.at[&address];
        let node = match statement.statement_type() {
            StatementType::Floating => Tree::Variable(VariableNode(variable_of(statement))),
            _ => Tree::Syntax(SyntaxNode(
                as_str(statement.label()).to_string(),
                arguments
                    .into_iter()
                    .map(|argument| self.take(argument))
                    .collect(),
            )),
        };
        self.nodes.push(Some(node));
        self.nodes.len() - 1
    }
}
