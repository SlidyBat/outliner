//! Outliner: turn inlined code back into function calls.
//!
//! Users describe an MLIL fragment as a text pattern together with a C function
//! signature; during analysis every match is replaced with a call to a function
//! of that signature.  This crate holds everything that does not need Binary
//! Ninja: the pattern language, the matcher, the fused-guard recovery, the
//! expression sites and the rewrite planner.  The host (the `outliner-plugin`
//! crate) reads MLIL into an [`il::Function`], answers the matcher's questions
//! through an [`env::Env`], and executes the [`plan::Plan`] the round produces.

pub mod binding;
pub mod draft;
pub mod env;
pub mod fake;
pub mod fused;
pub mod generalize;
pub mod hybrid;
pub mod il;
pub mod literals;
pub mod matcher;
pub mod ops;
mod ops_generated;
pub mod pattern;
pub mod plan;
pub mod render;
pub mod sites;

pub use pattern::{parse_pattern, Pattern, PatternError};
