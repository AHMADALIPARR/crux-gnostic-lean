// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! Proof-carrying code (port of pcc.rs / Crux.Pcc): Sila derivations,
//! proof certificates, certified states, and the JSON certificate written by
//! `crux cert`. Certificates embed the SHA-256 of every emitted artifact.

const std = @import("std");
const ast = @import("ast.zig");
const omega = @import("omega.zig");

pub const Rule = union(enum) {
    Axiom: ast.Formula,
    ModusPonens: struct { imp: *const Derivation, antecedent: *const Derivation },
    Generalization: struct { inner: *const Derivation, var_: []const u8 },
    RecursiveUnfold: *const Derivation,
    StateUpdate: struct { inner: *const Derivation, binding: ast.Binding },
    OmegaConfirmed: omega.OmegaResult,
};

pub const Derivation = struct {
    state: ast.State,
    formula: ast.Formula,
    rules: []const Rule,

    pub fn axiom(arena: std.mem.Allocator, state: ast.State, f: ast.Formula) !Derivation {
        return .{ .state = state, .formula = f, .rules = try arena.dupe(Rule, &.{.{ .Axiom = f }}) };
    }

    /// From `φ → ψ` and `φ` derive `ψ`.
    pub fn modusPonens(arena: std.mem.Allocator, state: ast.State, imp_formula: ast.Formula, imp: Derivation, ant: Derivation) !Derivation {
        const result = if (imp_formula == .Implies) imp_formula.Implies.rhs.* else imp_formula;
        return .{ .state = state, .formula = result, .rules = try arena.dupe(Rule, &.{.{ .ModusPonens = .{
            .imp = try ast.box(arena, imp),
            .antecedent = try ast.box(arena, ant),
        } }}) };
    }

    pub fn stateUpdate(arena: std.mem.Allocator, inner: Derivation, binding: ast.Binding) !Derivation {
        const base = try ast.box(arena, inner.state);
        return .{
            .state = .{ .Bind = .{ .base = base, .binding = binding } },
            .formula = inner.formula,
            .rules = try arena.dupe(Rule, &.{.{ .StateUpdate = .{ .inner = try ast.box(arena, inner), .binding = binding } }}),
        };
    }

    pub fn omegaConfirmed(arena: std.mem.Allocator, state: ast.State, f: ast.Formula, r: omega.OmegaResult) !Derivation {
        return .{ .state = state, .formula = f, .rules = try arena.dupe(Rule, &.{.{ .OmegaConfirmed = r }}) };
    }

    pub fn isValid(self: Derivation) bool {
        for (self.rules) |r| switch (r) {
            .Axiom, .OmegaConfirmed => {},
            .ModusPonens => |m| if (!m.imp.isValid() or !m.antecedent.isValid()) return false,
            .Generalization => |g| if (!g.inner.isValid()) return false,
            .RecursiveUnfold => |d| if (!d.isValid()) return false,
            .StateUpdate => |s| if (!s.inner.isValid()) return false,
        };
        return true;
    }
};

pub const Certificate = union(enum) {
    Z3Cert: struct { model: []const u8 },
    SASCert: struct { invariant: []const u8 },
    LeanCert: struct { expr: []const u8 },
    SilaCert: Derivation,
    Compose: struct { a: *const Certificate, b: *const Certificate },
    Reflect: ast.Formula,
};

pub const CertifiedState = struct {
    state: ast.State,
    formula: ast.Formula,
    derivation: Derivation,
    proof: Certificate,

    pub fn isProved(self: CertifiedState) bool {
        return self.derivation.isValid();
    }
};

/// Source `omega_to_derivation`.
pub fn omegaToDerivation(arena: std.mem.Allocator, state: ast.State, f: ast.Formula, r: omega.OmegaResult) !CertifiedState {
    const d = try Derivation.omegaConfirmed(arena, state, f, r);
    return .{ .state = state, .formula = f, .derivation = d, .proof = .{ .SilaCert = d } };
}

/// Source `compose_pcc`.
pub fn compose(arena: std.mem.Allocator, f: Certificate) !Certificate {
    return .{ .Compose = .{ .a = try ast.box(arena, f), .b = try ast.box(arena, Certificate{ .Reflect = ast.true_formula }) } };
}

fn writeJsonString(w: *ast.W, s: []const u8) ast.W.Error!void {
    try w.writeByte('"');
    for (s) |c| switch (c) {
        '"' => try w.writeAll("\\\""),
        '\\' => try w.writeAll("\\\\"),
        '\n' => try w.writeAll("\\n"),
        '\r' => try w.writeAll("\\r"),
        '\t' => try w.writeAll("\\t"),
        0...8, 11, 12, 14...31 => try w.print("\\u{x:0>4}", .{c}),
        else => try w.writeByte(c),
    };
    try w.writeByte('"');
}

fn writeSha(w: *ast.W, bytes: ?[]const u8) ast.W.Error!void {
    const b = bytes orelse return w.writeAll("null");
    var h: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(b, &h, .{});
    try w.writeByte('"');
    for (h) |x| try w.print("{x:0>2}", .{x});
    try w.writeByte('"');
}

fn writeOpt(w: *ast.W, s: ?[]const u8) ast.W.Error!void {
    if (s) |v| try writeJsonString(w, v) else try w.writeAll("null");
}

pub const CertInput = struct {
    name: []const u8,
    outcome: omega.Outcome,
    certified: CertifiedState,
    closure: ast.ProofClosure,
    cuda: ?[]const u8,
};

/// One certificate as a JSON object.
pub fn writeCertJson(arena: std.mem.Allocator, w: *ast.W, c: CertInput) !void {
    const o = c.outcome;
    try w.writeAll("{\n    \"goal\": ");
    try writeJsonString(w, c.name);
    try w.writeAll(",\n    \"state\": ");
    try writeJsonString(w, try ast.dumpAlloc(arena, c.certified.state));
    try w.writeAll(",\n    \"formula\": ");
    try writeJsonString(w, try ast.dumpAlloc(arena, c.certified.formula));
    try w.writeAll(",\n    \"result\": ");
    var aw: ast.W.Allocating = .init(arena);
    try ast.writeFinal(&aw.writer, o.result.toFinal());
    try writeJsonString(w, try aw.toOwnedSlice());
    try w.print(",\n    \"decided_by\": \"{s}\",\n", .{@tagName(o.decided_by)});
    try w.writeAll("    \"derivation\": { \"rules\": [\"OmegaConfirmed\"], \"valid\": ");
    try w.writeAll(if (c.certified.isProved()) "true" else "false");
    try w.writeAll(" },\n    \"certificate\": ");
    switch (o.decided_by) {
        .z3 => {
            try w.writeAll("{ \"kind\": \"Z3Cert\", \"model\": ");
            try writeOpt(w, o.z3_output);
        },
        .lean => {
            try w.writeAll("{ \"kind\": \"LeanCert\", \"lean_checked\": ");
            try w.writeAll(if (o.lean_checked) |b| (if (b) "true" else "false") else "null");
            try w.writeAll(", \"method\": ");
            try writeJsonString(w, if (o.lean_checked != null) "lean" else "decide");
        },
        .sas => {
            var inv: ast.W.Allocating = .init(arena);
            try @import("sas.zig").writeState(&inv.writer, o.sas_trace.final_state);
            try w.writeAll("{ \"kind\": \"SASCert\", \"invariant\": ");
            try writeJsonString(w, try inv.toOwnedSlice());
        },
    }
    try w.writeAll(" },\n    \"obligations\": [");
    for (c.closure.obligations, 0..) |ob, i| {
        if (i > 0) try w.writeAll(", ");
        try w.print("{{ \"id\": {d}, \"discharged_by\": \"{s}\" }}", .{ ob.id, @tagName(ob.discharged_by) });
    }
    try w.writeAll("],\n    \"artifacts\": {\n      \"smt2_sha256\": ");
    try writeSha(w, o.smt);
    try w.writeAll(",\n      \"lean_sha256\": ");
    try writeSha(w, o.lean_src);
    try w.writeAll(",\n      \"cuda_sha256\": ");
    try writeSha(w, c.cuda);
    try w.writeAll("\n    }\n  }");
}

const testing = std.testing;

test "pcc: derivations and validity" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const p: ast.Formula = .{ .Atomic = .{ .Predicate = .{ .name = "p", .args = &.{} } } };
    const q: ast.Formula = .{ .Atomic = .{ .Predicate = .{ .name = "q", .args = &.{} } } };
    const imp: ast.Formula = .{ .Implies = .{ .lhs = &p, .rhs = &q } };
    const d_imp = try Derivation.axiom(a, .S0, imp);
    const d_p = try Derivation.axiom(a, .S0, p);
    const d_q = try Derivation.modusPonens(a, .S0, imp, d_imp, d_p);
    try testing.expect(d_q.formula.Atomic.Predicate.name[0] == 'q');
    try testing.expect(d_q.isValid());
    const upd = try Derivation.stateUpdate(a, d_q, .{ .var_ = "x", .value = .{ .Const = .{ .Number = 1 } }, .kind = .Assign });
    try testing.expect(upd.state == .Bind);
    const cs = try omegaToDerivation(a, .S0, p, .Proved);
    try testing.expect(cs.isProved());
    const c = try compose(a, cs.proof);
    try testing.expect(c.Compose.b.* == .Reflect);
}
