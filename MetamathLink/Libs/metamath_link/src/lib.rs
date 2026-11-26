//! MetamathLink's core: Metamath databases read, verified and parsed by metamath-rs, the library of metamath-knife,
//! and given to the Wolfram Language as typed WXF through wolfram-export.

mod database;
mod tree;

use wolfram_export::export;

/// The database in the file `path`, verified, with the parse tree of every statement; or a `Failure` with the
/// verifier's diagnostics.
#[export(wxf)]
fn metamath_database(path: String) -> database::Reading {
    database::read(&path)
}

/// Verifies the database in the file `path`, every proof, as metamath-knife does: `Success["Verified", ...]` with its
/// counts, or a `Failure` with the verifier's diagnostics. Nothing is converted for the kernel.
#[export(wxf)]
fn metamath_verify(path: String) -> database::Verification {
    database::verify(&path)
}
