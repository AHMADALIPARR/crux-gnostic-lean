// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! OMEGA smasher (port of omega.rs / Crux.Omega): dispatch to Z3, then Lean,
//! then SAS, and build the proof closure for the result.

const std = @import("std");
const ast = @import("ast.zig");
const z3 = @import("z3.zig");
const sas = @import("sas.zig");
const lean = @import("lean.zig");

pub const OmegaResult = union(enum) {
    Sat,
    Unsat,
    Model: []const ast.ModelEntry,
    Unknown,
    Timeout,
    Alarm: struct { location: []const u8, formula: ast.Formula },
    Proved,

    pub fn toFinal(self: OmegaResult) ast.FinalResult {
        return switch (self) {
            .Sat => .Sat,
            .Unsat => .Unsat,
            .Model => |m| .{ .Model = m },
            .Unknown => .Unknown,
            .Timeout => .Timeout,
            .Alarm => |a| .{ .Alarm = .{ .location = a.location, .formula = a.formula } },
            .Proved => .Proved,
        };
    }
};

/// Hooks for the external provers. The CLI fills these in when `z3` / `lean`
/// are available; the library leaves them empty.
pub const Externals = struct {
    ctx: ?*anyopaque = null,
    /// Run z3 on an SMT-LIB script; null when z3 is unavailable.
    run_z3: ?*const fn (ctx: ?*anyopaque, arena: std.mem.Allocator, smt: []const u8) ?[]const u8 = null,
    /// Elaborate a Lean file; null when Lean is unavailable, else whether it compiled.
    run_lean: ?*const fn (ctx: ?*anyopaque, arena: std.mem.Allocator, src: []const u8) ?bool = null,
};

pub const Decider = enum { z3, lean, sas };

/// Everything the smasher produced, kept for certificates and reports.
pub const Outcome = struct {
    result: OmegaResult,
    decided_by: Decider,
    smt: ?[]const u8 = null,
    z3_output: ?[]const u8 = null,
    lean_src: ?[]const u8 = null,
    lean_checked: ?bool = null,
    sas_query: ast.SASQuery,
    sas_result: sas.Result,
    sas_trace: sas.Trace,
};

pub const Smasher = struct {
    arena: std.mem.Allocator,
    z3_solver: z3.Solver = .{},
    sas_analyzer: sas.Analyzer = .{},
    ext: Externals = .{},

    pub fn smtFor(self: *Smasher, state: ast.State, f: ast.Formula) !?[]const u8 {
        const built = self.z3_solver.buildQuery(self.arena, state, f) catch |e| switch (e) {
            error.Unsupported => return null,
            else => return e,
        };
        return try z3.smtlibAlloc(self.arena, built.query);
    }

    fn smashZ3(self: *Smasher, smt: ?[]const u8, out: *Outcome) OmegaResult {
        const script = smt orelse return .Unknown;
        const run = self.ext.run_z3 orelse return .Unknown;
        const reply = run(self.ext.ctx, self.arena, script) orelse return .Unknown;
        out.z3_output = reply;
        const r = z3.parseZ3Output(self.arena, reply) catch return .Unknown;
        return switch (r) {
            .Sat => .Sat,
            .Unsat => .Unsat,
            .Model => |m| .{ .Model = m },
            .Unknown => .Unknown,
            .Timeout => .Timeout,
        };
    }

    fn smashLean(self: *Smasher, goal: ast.LeanGoal, out: *Outcome) OmegaResult {
        if (lean.prove(goal) == .Proved) return .Proved;
        const run = self.ext.run_lean orelse return .Unknown;
        const src = out.lean_src orelse return .Unknown;
        const ok = run(self.ext.ctx, self.arena, src) orelse return .Unknown;
        out.lean_checked = ok;
        return if (ok) .Proved else .Unknown;
    }

    /// Source `smash_auto`: Z3, then Lean, then SAS.
    pub fn smashAuto(self: *Smasher, goal_kind: ast.LeanGoalKind, goal_name: []const u8, state: ast.State, f: ast.Formula) !Outcome {
        const q = try self.sas_analyzer.buildQuery(self.arena, state, f);
        var trace: sas.Trace = undefined;
        const sres = try self.sas_analyzer.analyze(self.arena, q, &trace);
        const goal = try lean.buildGoal(self.arena, goal_kind, goal_name, state, f);
        var out: Outcome = .{
            .result = .Unknown,
            .decided_by = .z3,
            .smt = try self.smtFor(state, f),
            .lean_src = lean.goalFileAlloc(self.arena, goal) catch |e| switch (e) {
                error.Unsupported => null,
                else => return e,
            },
            .sas_query = q,
            .sas_result = sres,
            .sas_trace = trace,
        };
        const rz = self.smashZ3(out.smt, &out);
        if (rz != .Unknown) {
            out.result = rz;
            return out;
        }
        const rl = self.smashLean(goal, &out);
        if (rl != .Unknown) {
            out.result = rl;
            out.decided_by = .lean;
            return out;
        }
        out.decided_by = .sas;
        out.result = switch (sres) {
            .Proved => .Proved,
            .Alarm => |a| .{ .Alarm = .{ .location = a.location, .formula = a.formula } },
            .Unknown => .Unknown,
        };
        return out;
    }
};

/// Source `omega_macro_definitions`.
pub const omega_macro_definitions = [_]struct { []const u8, []const u8 }{
    .{ "sila_auto", "simp [Sila.*, Eq.*, State.*] <;> try (first | omega | linarith | nlinarith | ring) <;> try decide <;> try aesop" },
    .{ "omega_smash", "first | omega | linarith (config := {splitHypotheses := true}) | nlinarith | (ring_nf <;> omega)" },
    .{ "z3_decide", "native_decide (config := {kernel := false}) <|> (do let e <- Z3.prove (<- getMainTarget); exact e)" },
    .{ "sas_prove", "apply SAS.soundness <;> (first | exact abs_invariant | refine <?_, ?> <;> sas_prove)" },
    .{ "crux_close", "sila_auto <;> omega_smash <;> try z3_decide <;> try aesop <;> try (solve_by_elim [Sila.refl, Sila.trans, Sila.symm])" },
    .{ "rintro!", "rintro * <;> try (intros <;> simp_all)" },
    .{ "simp!", "simp (config := {zeta := true, beta := true, eta := true}) [*]" },
    .{ "aesop!", "aesop (config := {enableSimp := true, enableUnfold := true})" },
    .{ "linarith!", "linarith (config := {splitNe := true, splitHypotheses := true})" },
    .{ "blast", "repeat (first | constructor | intro | apply And.intro | apply Or.inl | apply Or.inr | assumption | contradiction | exfalso)" },
    .{ "finish", "try sila_auto <;> try blast <;> try omega_smash <;> try decide" },
    .{ "crush", "sila_auto <;> finish <;> try (exact (by decide))" },
};

/// Source `omega_smash_pipeline`: one obligation `Сила(state, φ)` discharged
/// by the method matching the result.
pub fn closureFor(arena: std.mem.Allocator, state: ast.State, f: ast.Formula, r: OmegaResult) !ast.ProofClosure {
    const method: ast.DischargeMethod = switch (r) {
        .Sat, .Unsat, .Model => .Z3Check,
        .Proved => .CruxClose,
        .Alarm => .SASProve,
        else => .CruxClose,
    };
    const inner = try ast.box(arena, f);
    return .{ .obligations = try arena.dupe(ast.Obligation, &.{.{
        .id = 0,
        .formula = .{ .Sila = .{ .state = state, .formula = inner } },
        .discharged_by = method,
    }}) };
}

const testing = std.testing;
const parser = @import("parser.zig");

test "omega: priority Z3 -> Lean -> SAS" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    var sm: Smasher = .{ .arena = a };
    // No external provers: ground formula is decided by Lean's decide.
    const o1 = try sm.smashAuto(.Theorem, "g", .S0, (try parser.parseFormula(a, "2 + 2 = 4")).ok);
    try testing.expect(o1.result == .Proved);
    try testing.expectEqual(Decider.lean, o1.decided_by);
    // Symbolic formula falls through to SAS.
    const o2 = try sm.smashAuto(.Theorem, "g", .S0, (try parser.parseFormula(a, "x + 1 = 1 + x")).ok);
    try testing.expectEqual(Decider.sas, o2.decided_by);
    try testing.expect(o2.result == .Proved);
    // A stub z3 that answers unsat decides first.
    const Stub = struct {
        fn run(_: ?*anyopaque, _: std.mem.Allocator, _: []const u8) ?[]const u8 {
            return "unsat\n";
        }
    };
    sm.ext = .{ .run_z3 = Stub.run };
    const o3 = try sm.smashAuto(.Theorem, "g", .S0, (try parser.parseFormula(a, "x < 0")).ok);
    try testing.expect(o3.result == .Unsat);
    try testing.expectEqual(Decider.z3, o3.decided_by);
    const c = try closureFor(a, .S0, ast.true_formula, o3.result);
    try testing.expect(c.obligations[0].discharged_by == .Z3Check);
}
