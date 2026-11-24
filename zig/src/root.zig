// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! CRUX · SILA · OMEGA-SMASHER compiler library.
//! Russian syntax -> recursive state IR -> dual backend (GHC | Kani) ->
//! OMEGA smasher -> (Z3 | Lean | SAS) -> proof closure -> SAT | UNSAT | MODEL,
//! with SAS lowered to CUDA and proof-carrying certificates.

pub const ast = @import("ast.zig");
pub const lexer = @import("lexer.zig");
pub const parser = @import("parser.zig");
pub const z3 = @import("z3.zig");
pub const sas = @import("sas.zig");
pub const cuda = @import("cuda.zig");
pub const lean = @import("lean.zig");
pub const monad_stack = @import("monad_stack.zig");
pub const omega = @import("omega.zig");
pub const pcc = @import("pcc.zig");
pub const domain = @import("domain.zig");
pub const arithmetic = @import("arithmetic.zig");
pub const search = @import("search.zig");
pub const suspension = @import("suspension.zig");
pub const pipeline = @import("pipeline.zig");
pub const abjad = @import("abjad.zig");

pub const version = "0.1.0";

test {
    @import("std").testing.refAllDecls(@This());
}
