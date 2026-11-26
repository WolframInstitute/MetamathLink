//! A Metamath database read and verified by metamath-rs, in the form MetamathLink's Wolfram Language code reads:
//!
//! ```text
//! <|"Statements" -> <|label -> statement, ...|>, "Order" -> {label, ...}, "ProvableTypecode" -> "|-",
//!   "FormulaTypecode" -> "wff", "Trees" -> <|label -> tree, ...|>|>
//! ```
//!
//! each statement an association with the keys of `normalizedStatement` in Database.wl, and each tree the parse of a
//! statement's formula, its typecode replaced by the typecode of formulas when it is the provable one.

use std::collections::{BTreeSet, HashMap};

use annotate_snippets::Renderer;
use metamath_rs::database::DbOptions;
use metamath_rs::formula::TypeCode;
use metamath_rs::scopeck::Hyp;
use metamath_rs::statement::{StatementAddress, StatementRef};
use metamath_rs::{Database, StatementType, as_str};
use wolfram_serialize::ToWXF;

use crate::tree::{Tree, formula_tree};

/// The provable typecode and the typecode of formulas: the database's grammar parses a provable statement as a formula.
const PROVABLE_TYPECODE: &str = "|-";
const FORMULA_TYPECODE: &str = "wff";

/// How many diagnostics a failure shows.
const DIAGNOSTICS_SHOWN: usize = 10;

/// The result of reading a database: the database itself, or a `Failure`.
#[derive(ToWXF)]
#[wolfram(enum_head = "System`Failure")]
pub enum Reading {
    #[wolfram(enum_head = false)]
    Database(MetamathDatabase),
    InvalidDatabase(Diagnostics),
}

/// The result of verifying a database: `Success["Verified", <|...|>]` with what it has, or a `Failure`.
#[derive(ToWXF)]
#[wolfram(enum_head = "System`Failure")]
pub enum Verification {
    #[wolfram(enum_head = "System`Success")]
    Verified(Counts),
    InvalidDatabase(Diagnostics),
}

/// Why a database is refused: how many errors the verifier found, and the first of them as text.
#[derive(ToWXF)]
#[wolfram(key_processor = "CamelCase")]
pub struct Diagnostics {
    message_template: String,
    message_parameters: Vec<String>,
    diagnostics: Vec<String>,
}

/// What a database that verifies has.
#[derive(ToWXF)]
#[wolfram(key_processor = "CamelCase")]
pub struct Counts {
    message_template: String,
    message_parameters: Vec<String>,
    axioms: i64,
    theorems: i64,
    hypotheses: i64,
}

#[derive(ToWXF)]
#[wolfram(key_processor = "CamelCase")]
pub struct MetamathDatabase {
    statements: HashMap<String, Statement>,
    order: Vec<String>,
    provable_typecode: String,
    formula_typecode: String,
    trees: HashMap<String, Tree>,
}

/// A statement with a label, as its association.
#[derive(ToWXF)]
#[wolfram(enum_head = false)]
pub enum Statement {
    Axiom(Axiom),
    Theorem(Theorem),
    Floating(FloatingHypothesis),
    Essential(EssentialHypothesis),
}

/// An `$a` statement: its floating hypotheses are its mandatory ones, `{label, typecode, variable}` in the order of the
/// file, and its disjoint variables the pairs of its mandatory `$d`.
#[derive(ToWXF)]
#[wolfram(key_processor = "CamelCase")]
pub struct Axiom {
    kind: &'static str,
    label: String,
    typecode: String,
    symbols: Vec<String>,
    disjoint: Vec<(String, String)>,
    floating: Vec<(String, String, String)>,
    essential: Vec<String>,
}

/// A `$p` statement, with its proof as the file has it: labels, or a compressed proof `( labels ) letters`.
#[derive(ToWXF)]
#[wolfram(key_processor = "CamelCase")]
pub struct Theorem {
    kind: &'static str,
    label: String,
    typecode: String,
    symbols: Vec<String>,
    disjoint: Vec<(String, String)>,
    floating: Vec<(String, String, String)>,
    essential: Vec<String>,
    proof: Vec<String>,
}

#[derive(ToWXF)]
#[wolfram(key_processor = "CamelCase")]
pub struct FloatingHypothesis {
    kind: &'static str,
    label: String,
    typecode: String,
    variable: String,
}

#[derive(ToWXF)]
#[wolfram(key_processor = "CamelCase")]
pub struct EssentialHypothesis {
    kind: &'static str,
    label: String,
    typecode: String,
    symbols: Vec<String>,
}

/// Reads the database in the file `path` and every file it includes, verifies every proof, and parses every statement
/// the grammar of its syntax axioms parses. A statement it does not parse has no tree here: MetamathLink parses it.
pub fn read(path: &str) -> Reading {
    let mut database = verified(path, Vec::new());
    if let Some(diagnostics) = diagnostics_of(&database, path) {
        return Reading::InvalidDatabase(diagnostics);
    }
    if database.grammar_pass().provable_typecode() == TypeCode::default() {
        if let Some(declared) = syntax_declaration(&database, path) {
            database = verified(path, declared);
            database.grammar_pass();
        }
    }
    database.stmt_parse_pass();
    Reading::Database(converted(&database))
}

/// Verifies the database in the file `path`, as metamath-knife does, and counts its statements.
pub fn verify(path: &str) -> Verification {
    let database = verified(path, Vec::new());
    if let Some(diagnostics) = diagnostics_of(&database, path) {
        return Verification::InvalidDatabase(diagnostics);
    }
    let count = |kinds: &[StatementType]| {
        database
            .statements()
            .filter(|statement| kinds.contains(&statement.statement_type()))
            .count() as i64
    };
    let (axioms, theorems) = (
        count(&[StatementType::Axiom]),
        count(&[StatementType::Provable]),
    );
    Verification::Verified(Counts {
        message_template: "`1` verifies: `2` theorems from `3` axioms.".to_string(),
        message_parameters: vec![path.to_string(), theorems.to_string(), axioms.to_string()],
        axioms,
        theorems,
        hypotheses: count(&[StatementType::Floating, StatementType::Essential]),
    })
}

/// The diagnostics of reading, scoping and verifying a database, if it has any.
fn diagnostics_of(database: &Database, path: &str) -> Option<Diagnostics> {
    let diagnostics = database.diag_notations();
    if diagnostics.is_empty() {
        return None;
    }
    let renderer = Renderer::plain();
    let count = diagnostics.len();
    let shown = database.render_diags(diagnostics, |message| renderer.render(message).to_string());
    Some(Diagnostics {
        message_template: "The database `1` does not verify: `2` errors.".to_string(),
        message_parameters: vec![path.to_string(), count.to_string()],
        diagnostics: shown.into_iter().take(DIAGNOSTICS_SHOWN).collect(),
    })
}

/// The database parsed from `path`, or from the contents `text` gives for it, and verified.
fn verified(path: &str, text: Vec<(String, Vec<u8>)>) -> Database {
    let mut database = Database::new(DbOptions {
        incremental: true,
        jobs: 1,
        ..DbOptions::default()
    });
    database.parse(path.to_string(), text);
    database.verify_pass();
    database
}

/// The grammar knows which typecodes are syntax, and that a provable statement is a formula, from `$j syntax` commands,
/// as set.mm has them; without them it takes every axiom for a rule of the grammar. A database that has none, as demo0,
/// gets them in front of its first line: every typecode of a floating hypothesis is syntax, and the provable typecode
/// is read as formulas.
fn syntax_declaration(database: &Database, path: &str) -> Option<Vec<(String, Vec<u8>)>> {
    let typecodes: BTreeSet<String> = database
        .statements()
        .filter(|statement| statement.statement_type() == StatementType::Floating)
        .map(|statement| math(&statement).0)
        .collect();
    let syntax: String = typecodes
        .iter()
        .map(|typecode| format!("syntax '{typecode}'; "))
        .collect();
    let declaration =
        format!("$( $j {syntax}syntax '{PROVABLE_TYPECODE}' as '{FORMULA_TYPECODE}'; $) ");
    let contents = std::fs::read(path).ok()?;
    Some(vec![(
        path.to_string(),
        [declaration.as_bytes(), &contents].concat(),
    )])
}

fn text(token: &[u8]) -> String {
    as_str(token).to_string()
}

/// The typecode and the symbols of a statement's math string.
fn math(statement: &StatementRef<'_>) -> (String, Vec<String>) {
    let mut tokens = statement.math_iter().map(|token| text(&token));
    let typecode = tokens.next().unwrap_or_default();
    (typecode, tokens.collect())
}

/// The variable of a floating hypothesis.
pub fn variable_of(statement: &StatementRef<'_>) -> String {
    math(statement).1.into_iter().next().unwrap_or_default()
}

fn converted(database: &Database) -> MetamathDatabase {
    let labeled: Vec<StatementRef<'_>> = database
        .statements()
        .filter(|statement| {
            matches!(
                statement.statement_type(),
                StatementType::Axiom
                    | StatementType::Provable
                    | StatementType::Floating
                    | StatementType::Essential
            )
        })
        .collect();
    // a frame names its hypotheses, and a formula its nodes, by the addresses of their statements
    let at: HashMap<StatementAddress, StatementRef<'_>> = labeled
        .iter()
        .map(|statement| (statement.address(), *statement))
        .collect();
    let parses = database.stmt_parse_result();
    MetamathDatabase {
        order: labeled
            .iter()
            .map(|statement| text(statement.label()))
            .collect(),
        statements: labeled
            .iter()
            .map(|statement| {
                (
                    text(statement.label()),
                    converted_statement(database, statement, &at),
                )
            })
            .collect(),
        provable_typecode: PROVABLE_TYPECODE.to_string(),
        formula_typecode: FORMULA_TYPECODE.to_string(),
        trees: labeled
            .iter()
            .filter_map(|statement| {
                parses.get_formula(statement).map(|formula| {
                    (
                        text(statement.label()),
                        formula_tree(database, formula, &at),
                    )
                })
            })
            .collect(),
    }
}

fn converted_statement(
    database: &Database,
    statement: &StatementRef<'_>,
    at: &HashMap<StatementAddress, StatementRef<'_>>,
) -> Statement {
    let label = text(statement.label());
    let (typecode, symbols) = math(statement);
    match statement.statement_type() {
        StatementType::Floating => Statement::Floating(FloatingHypothesis {
            kind: "Floating",
            label,
            typecode,
            variable: variable_of(statement),
        }),
        StatementType::Essential => Statement::Essential(EssentialHypothesis {
            kind: "Essential",
            label,
            typecode,
            symbols,
        }),
        kind => {
            let frame = database
                .scope_result()
                .get(statement.label())
                .expect("an assertion that verifies has a frame");
            let variable =
                |index: usize| text(database.name_result().atom_name(frame.var_list[index]));
            let floating: Vec<(String, String, String)> = frame
                .hypotheses
                .iter()
                .filter_map(|hypothesis| match hypothesis {
                    Hyp::Floating(address, _, _) => {
                        let hypothesis = &at[address];
                        Some((
                            text(hypothesis.label()),
                            math(hypothesis).0,
                            variable_of(hypothesis),
                        ))
                    }
                    Hyp::Essential(..) => None,
                })
                .collect();
            // a set of unordered pairs, which the translation reads as such: each pair, and the pairs, in the order of
            // the floating hypotheses of their variables, every one of which is mandatory
            let position = |index: usize| {
                let name = variable(index);
                floating
                    .iter()
                    .position(|(_, _, variable)| *variable == name)
                    .expect("a mandatory disjoint variable has a mandatory floating hypothesis")
            };
            let mut pairs: Vec<(usize, usize)> = frame
                .mandatory_dv
                .iter()
                .map(|&(first, second)| {
                    let (first, second) = (position(first), position(second));
                    (first.min(second), first.max(second))
                })
                .collect();
            pairs.sort_unstable();
            pairs.dedup();
            let disjoint = pairs
                .into_iter()
                .map(|(first, second)| (floating[first].2.clone(), floating[second].2.clone()))
                .collect();
            let essential = frame
                .hypotheses
                .iter()
                .filter_map(|hypothesis| match hypothesis {
                    Hyp::Essential(address, _) => Some(text(at[address].label())),
                    Hyp::Floating(..) => None,
                })
                .collect();
            if kind == StatementType::Provable {
                let proof = (0..statement.proof_len())
                    .map(|index| text(statement.proof_slice_at(index)))
                    .collect();
                Statement::Theorem(Theorem {
                    kind: "Theorem",
                    label,
                    typecode,
                    symbols,
                    disjoint,
                    floating,
                    essential,
                    proof,
                })
            } else {
                Statement::Axiom(Axiom {
                    kind: "Axiom",
                    label,
                    typecode,
                    symbols,
                    disjoint,
                    floating,
                    essential,
                })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tree::{SyntaxNode, VariableNode};

    const DEMO0: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../Data/demo0.mm");

    fn variable(name: &str) -> Tree {
        Tree::Variable(VariableNode(name.to_string()))
    }

    fn syntax(label: &str, arguments: Vec<Tree>) -> Tree {
        Tree::Syntax(SyntaxNode(label.to_string(), arguments))
    }

    fn demo0() -> MetamathDatabase {
        match read(DEMO0) {
            Reading::Database(database) => database,
            Reading::InvalidDatabase(failure) => {
                panic!("demo0 does not verify: {:?}", failure.diagnostics)
            }
        }
    }

    #[test]
    fn demo0_statements_in_order() {
        let database = demo0();
        assert_eq!(database.order.len(), database.statements.len());
        assert_eq!(&database.order[..3], ["tt", "tr", "ts"]);
        match &database.statements["th1"] {
            Statement::Theorem(theorem) => {
                assert_eq!(theorem.symbols, ["t", "=", "t"]);
                assert_eq!(
                    theorem.floating,
                    [("tt".to_string(), "term".to_string(), "t".to_string())]
                );
                assert!(theorem.essential.is_empty());
            }
            _ => panic!("th1 is a theorem"),
        }
    }

    /// demo0 has no `$j syntax` and gets it. Its grammar is ambiguous where metamath-rs's parser looks ahead, `( t = r`
    /// starting both a term `( t + r )` and a formula `( P -> Q )`: the formulas it parses have their trees, in the order
    /// of the floating hypotheses, and those it does not have none, rather than a wrong one.
    #[test]
    fn demo0_trees() {
        let database = demo0();
        assert_eq!(
            database.trees["weq"],
            syntax("weq", vec![variable("t"), variable("r")])
        );
        assert_eq!(
            database.trees["tpl"],
            syntax("tpl", vec![variable("t"), variable("r")])
        );
        assert_eq!(database.trees["tze"], syntax("tze", vec![]));
        assert!(!database.trees.contains_key("a1"));
        assert!(!database.trees.contains_key("th1"));
    }

    #[test]
    fn demo0_verifies() {
        match verify(DEMO0) {
            Verification::Verified(counts) => {
                assert_eq!((counts.axioms, counts.theorems), (7, 1))
            }
            Verification::InvalidDatabase(failure) => panic!("{:?}", failure.diagnostics),
        }
    }

    #[test]
    fn a_proof_that_does_not_verify_fails() {
        let path = std::env::temp_dir().join("metamath-link-broken-demo0.mm");
        std::fs::write(
            &path,
            std::fs::read_to_string(DEMO0)
                .unwrap()
                .replace("th1 $p |- t = t", "th1 $p |- t = r"),
        )
        .unwrap();
        match read(path.to_str().unwrap()) {
            Reading::InvalidDatabase(failure) => assert!(!failure.diagnostics.is_empty()),
            Reading::Database(_) => panic!("a broken proof verified"),
        }
    }

    /// The whole of a database named by `METAMATH_DATABASE`, as set.mm: every statement parsed, and the size of what the
    /// kernel receives. `METAMATH_DATABASE=set.mm cargo test --release -- --ignored --nocapture`
    #[test]
    #[ignore]
    fn whole_database() {
        let path = std::env::var("METAMATH_DATABASE").expect("METAMATH_DATABASE names a database");
        let start = std::time::Instant::now();
        let reading = read(&path);
        let read_in = start.elapsed();
        let start = std::time::Instant::now();
        let bytes = wolfram_serialize::to_wxf(&reading, None).unwrap();
        let written_in = start.elapsed();
        match reading {
            Reading::Database(database) => println!(
                "{} statements, {} trees, read in {read_in:?}; WXF {} MB in {written_in:?}",
                database.statements.len(),
                database.trees.len(),
                bytes.len() / 1_000_000
            ),
            Reading::InvalidDatabase(failure) => panic!("{:?}", failure.diagnostics),
        }
    }
}
