// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! Pipeline driver (port of pipeline.rs / Crux.Pipeline):
//! parse -> lower -> select backend -> OMEGA smash -> proof closure -> result,
//! for every item of a CRUX source file, plus the artifact emitters used by
//! the CLI and the C ABI: tokens, AST, SMT-LIB 2, Lean 4, SAS reports, CUDA,
//! PCC certificates, the stage report, and finite-domain solving.

const std = @import("std");
const ast = @import("ast.zig");
const lexer = @import("lexer.zig");
const parser = @import("parser.zig");
const z3 = @import("z3.zig");
const sas = @import("sas.zig");
const lean = @import("lean.zig");
const omega = @import("omega.zig");
const pcc = @import("pcc.zig");
const cuda = @import("cuda.zig");
const dom = @import("domain.zig");
const arith = @import("arithmetic.zig");
const search = @import("search.zig");
const susp = @import("suspension.zig");

pub const Options = struct {
    source_name: []const u8 = "<input>",
    ext: omega.Externals = .{},
    z3_timeout: ?u32 = null,
};

/// Text output, or a diagnostic `file:line:col: error: message`.
pub const Output = union(enum) { ok: []const u8, err: []const u8 };

pub const Unit = struct {
    item: parser.Item,
    name: []const u8,
    goal_kind: ast.LeanGoalKind,
    state: ast.State,
    formula: ast.Formula,
    backend: ast.Backend,
    outcome: omega.Outcome,
    closure: ast.ProofClosure,
    certified: pcc.CertifiedState,
};

pub const Lowered = struct { state: ast.State, formula: ast.Formula, backend: ast.Backend };

/// Source `lower_russian_form`.
pub fn lowerRussianForm(arena: std.mem.Allocator, form: ast.RussianForm) !Lowered {
    const kani: ast.Backend = .{ .Kani = ast.defaultKani() };
    return switch (form) {
        .Ravnostvo => |r| .{ .state = .S0, .formula = .{ .Eq = .{ .lhs = r.lhs, .rhs = r.rhs } }, .backend = kani },
        .Implikatsiya => |r| .{ .state = .S0, .formula = .{ .Implies = .{ .lhs = try ast.box(arena, r.lhs), .rhs = try ast.box(arena, r.rhs) } }, .backend = kani },
        .Konyunktsiya => |r| .{ .state = .S0, .formula = .{ .And = try arena.dupe(ast.Formula, &.{ r.lhs, r.rhs }) }, .backend = kani },
        .Dizyunktsiya => |r| .{ .state = .S0, .formula = .{ .Or = try arena.dupe(ast.Formula, &.{ r.lhs, r.rhs }) }, .backend = kani },
        .Otritsanie => |a| .{ .state = .S0, .formula = .{ .Not = try ast.box(arena, a) }, .backend = kani },
        .DlyaVsekh => |q| .{ .state = .S0, .formula = .{ .Forall = .{ .var_ = q.var_, .sort = q.sort, .body = try ast.box(arena, q.body) } }, .backend = kani },
        .Sushchestvuet => |q| .{ .state = .S0, .formula = .{ .Exists = .{ .var_ = q.var_, .sort = q.sort, .body = try ast.box(arena, q.body) } }, .backend = kani },
        .Sila => |s| .{ .state = s.state, .formula = s.formula, .backend = kani },
        .Omega => |o| .{ .state = o.state, .formula = o.formula, .backend = o.backend },
        .Sostoyanie => |s| .{ .state = s, .formula = ast.true_formula, .backend = kani },
        .Rekursiya => |r| .{ .state = .S0, .formula = .{ .Mu = .{ .var_ = r.var_, .body = try ast.box(arena, r.body) } }, .backend = kani },
        .Dokazatelstvo => .{ .state = .S0, .formula = ast.true_formula, .backend = kani },
        .Bare => |f| .{ .state = .S0, .formula = f, .backend = kani },
    };
}

fn diag(arena: std.mem.Allocator, opts: Options, e: lexer.Error) ![]const u8 {
    return std.fmt.allocPrint(arena, "{s}:{d}:{d}: error: {s}", .{ opts.source_name, e.line, e.col, e.message });
}

pub fn parse(arena: std.mem.Allocator, src: []const u8, opts: Options) !union(enum) { ok: []const parser.Item, err: []const u8 } {
    return switch (try parser.parseProgram(arena, src)) {
        .ok => |items| .{ .ok = items },
        .err => |e| .{ .err = try diag(arena, opts, e) },
    };
}

pub fn compile(arena: std.mem.Allocator, src: []const u8, opts: Options) !union(enum) { ok: []const Unit, err: []const u8 } {
    const items = switch (try parse(arena, src, opts)) {
        .ok => |i| i,
        .err => |e| return .{ .err = e },
    };
    var sm: omega.Smasher = .{ .arena = arena, .ext = opts.ext };
    sm.z3_solver.context.timeout = opts.z3_timeout;
    var units: std.ArrayList(Unit) = .empty;
    for (items, 0..) |item, i| {
        const low = try lowerRussianForm(arena, item.form);
        const name = item.name orelse try lean.defaultGoalName(arena, low.state, i);
        const kind: ast.LeanGoalKind = switch (item.kind) {
            .Lemma => .Lemma,
            .Example => .Example,
            else => .Theorem,
        };
        const outcome = try sm.smashAuto(kind, name, low.state, low.formula);
        try units.append(arena, .{
            .item = item,
            .name = name,
            .goal_kind = kind,
            .state = low.state,
            .formula = low.formula,
            .backend = low.backend,
            .outcome = outcome,
            .closure = try omega.closureFor(arena, low.state, low.formula, outcome.result),
            .certified = try pcc.omegaToDerivation(arena, low.state, low.formula, outcome.result),
        });
    }
    return .{ .ok = try units.toOwnedSlice(arena) };
}

fn unitsOrErr(arena: std.mem.Allocator, src: []const u8, opts: Options) !union(enum) { ok: []const Unit, err: []const u8 } {
    return compile(arena, src, opts);
}

// ---------------------------------------------------------------- emitters

pub fn emitTokens(arena: std.mem.Allocator, src: []const u8, opts: Options) !Output {
    const toks = switch (try lexer.tokenize(arena, src)) {
        .ok => |t| t,
        .err => |e| return .{ .err = try diag(arena, opts, e) },
    };
    var aw: ast.W.Allocating = .init(arena);
    const w = &aw.writer;
    for (toks) |t| {
        try w.print("{d}:{d}\t{s}", .{ t.line, t.col, @tagName(t.tag) });
        switch (t.tag) {
            .Ident, .StringLit => try w.print("\t{s}", .{t.text}),
            .Number => try w.print("\t{d}", .{t.number}),
            .BoolLit => try w.print("\t{s}", .{if (t.boolean) "true" else "false"}),
            .Eof => {},
            else => try w.print("\t{s}", .{t.text}),
        }
        try w.writeByte('\n');
    }
    return .{ .ok = try aw.toOwnedSlice() };
}

pub fn emitAst(arena: std.mem.Allocator, src: []const u8, opts: Options) !Output {
    const items = switch (try parse(arena, src, opts)) {
        .ok => |i| i,
        .err => |e| return .{ .err = e },
    };
    var aw: ast.W.Allocating = .init(arena);
    const w = &aw.writer;
    for (items) |it| {
        try w.print("{d}:{d} {s}", .{ it.line, it.col, @tagName(it.kind) });
        if (it.name) |n| try w.print(" {s}", .{n});
        try w.writeAll(": ");
        try ast.dump(w, it.form);
        try w.writeByte('\n');
    }
    return .{ .ok = try aw.toOwnedSlice() };
}

pub fn emitLowered(arena: std.mem.Allocator, src: []const u8, opts: Options) !Output {
    const items = switch (try parse(arena, src, opts)) {
        .ok => |i| i,
        .err => |e| return .{ .err = e },
    };
    var aw: ast.W.Allocating = .init(arena);
    const w = &aw.writer;
    for (items) |it| {
        const low = try lowerRussianForm(arena, it.form);
        try w.writeAll("state=");
        try ast.dump(w, low.state);
        try w.writeAll(" formula=");
        try ast.dump(w, low.formula);
        try w.writeAll(" backend=");
        try ast.dump(w, low.backend);
        try w.writeByte('\n');
    }
    return .{ .ok = try aw.toOwnedSlice() };
}

pub fn emitSmt(arena: std.mem.Allocator, src: []const u8, opts: Options) !Output {
    const units = switch (try compile(arena, src, opts)) {
        .ok => |u| u,
        .err => |e| return .{ .err = e },
    };
    var aw: ast.W.Allocating = .init(arena);
    const w = &aw.writer;
    try w.print("; SMT-LIB 2 generated by `crux emit-smt {s}`\n", .{opts.source_name});
    for (units, 0..) |u, i| {
        const smt = u.outcome.smt orelse return .{ .err = try std.fmt.allocPrint(arena, "{s}:{d}:{d}: error: goal {s} has terms the SMT backend does not support", .{ opts.source_name, u.item.line, u.item.col, u.name }) };
        if (i > 0) try w.writeAll("(reset)\n");
        try w.print("; goal {s}\n", .{u.name});
        try w.writeAll(smt);
    }
    return .{ .ok = try aw.toOwnedSlice() };
}

pub fn emitLean(arena: std.mem.Allocator, src: []const u8, opts: Options) !Output {
    const items = switch (try parse(arena, src, opts)) {
        .ok => |i| i,
        .err => |e| return .{ .err = e },
    };
    var aw: ast.W.Allocating = .init(arena);
    const w = &aw.writer;
    try w.print("-- Lean 4 generated by `crux emit-lean {s}` (Lean 4 core, no Mathlib).\n\n", .{opts.source_name});
    try w.writeAll(lean.prelude);
    for (items, 0..) |it, i| {
        const low = try lowerRussianForm(arena, it.form);
        const name = it.name orelse try lean.defaultGoalName(arena, low.state, i);
        const kind: ast.LeanGoalKind = switch (it.kind) {
            .Lemma => .Lemma,
            .Example => .Example,
            else => .Theorem,
        };
        const goal = try lean.buildGoal(arena, kind, name, low.state, low.formula);
        lean.writeGoal(arena, w, goal) catch |e| switch (e) {
            error.Unsupported => return .{ .err = try std.fmt.allocPrint(arena, "{s}:{d}:{d}: error: goal {s} has terms the Lean backend does not support", .{ opts.source_name, it.line, it.col, name }) },
            else => return e,
        };
    }
    try w.writeAll(lean.epilogue);
    return .{ .ok = try aw.toOwnedSlice() };
}

pub fn emitSas(arena: std.mem.Allocator, src: []const u8, opts: Options) !Output {
    const units = switch (try compile(arena, src, opts)) {
        .ok => |u| u,
        .err => |e| return .{ .err = e },
    };
    var aw: ast.W.Allocating = .init(arena);
    const w = &aw.writer;
    try w.print("SAS analysis of {s}\n", .{opts.source_name});
    for (units) |u| try sas.writeReport(w, u.name, u.outcome.sas_query, u.outcome.sas_result, u.outcome.sas_trace);
    return .{ .ok = try aw.toOwnedSlice() };
}

fn cudaFromUnits(arena: std.mem.Allocator, units: []const Unit, opts: Options) ![]u8 {
    const qs = try arena.alloc(cuda.Query, units.len);
    for (units, 0..) |u, i| qs[i] = .{ .name = u.name, .query = u.outcome.sas_query };
    return cuda.cudaAlloc(arena, opts.source_name, qs);
}

pub fn emitCuda(arena: std.mem.Allocator, src: []const u8, opts: Options) !Output {
    const units = switch (try compile(arena, src, opts)) {
        .ok => |u| u,
        .err => |e| return .{ .err = e },
    };
    return .{ .ok = try cudaFromUnits(arena, units, opts) };
}

pub fn emitCert(arena: std.mem.Allocator, src: []const u8, opts: Options) !Output {
    const units = switch (try compile(arena, src, opts)) {
        .ok => |u| u,
        .err => |e| return .{ .err = e },
    };
    const cu = try cudaFromUnits(arena, units, opts);
    var aw: ast.W.Allocating = .init(arena);
    const w = &aw.writer;
    try w.writeAll("{\n  \"source\": ");
    try w.print("\"{s}\",\n  \"certificates\": [\n  ", .{opts.source_name});
    for (units, 0..) |u, i| {
        if (i > 0) try w.writeAll(",\n  ");
        try pcc.writeCertJson(arena, w, .{ .name = u.name, .outcome = u.outcome, .certified = u.certified, .closure = u.closure, .cuda = cu });
    }
    try w.writeAll("\n  ]\n}\n");
    return .{ .ok = try aw.toOwnedSlice() };
}

/// `crux check`: one verdict line per goal.
pub fn check(arena: std.mem.Allocator, src: []const u8, opts: Options) !Output {
    const units = switch (try compile(arena, src, opts)) {
        .ok => |u| u,
        .err => |e| return .{ .err = e },
    };
    var aw: ast.W.Allocating = .init(arena);
    const w = &aw.writer;
    for (units) |u| {
        try w.print("{s}: ", .{u.name});
        try ast.writeFinal(w, u.outcome.result.toFinal());
        try w.print(" [{s}]\n", .{@tagName(u.outcome.decided_by)});
    }
    return .{ .ok = try aw.toOwnedSlice() };
}

/// `crux run`: the five-stage report of the source pipeline, per goal.
pub fn run(arena: std.mem.Allocator, src: []const u8, opts: Options) !Output {
    const units = switch (try compile(arena, src, opts)) {
        .ok => |u| u,
        .err => |e| return .{ .err = e },
    };
    var aw: ast.W.Allocating = .init(arena);
    const w = &aw.writer;
    for (units) |u| {
        try w.print("=== CRUX · SILA · OMEGA-SMASHER Pipeline: {s} ===\n\n", .{u.name});
        try w.writeAll("Stage 0: Parsed → ");
        try ast.dump(w, u.item.form);
        try w.writeAll("\nStage 1: Lowered → state=");
        try ast.dump(w, u.state);
        try w.writeAll(", formula=");
        try ast.dump(w, u.formula);
        try w.writeAll("\nStage 2: Backend → ");
        try ast.dump(w, u.backend);
        try w.writeAll("\nStage 3: OMEGA → ");
        try ast.writeFinal(w, u.outcome.result.toFinal());
        try w.print(" (decided by {s})\n", .{@tagName(u.outcome.decided_by)});
        try w.print("Stage 4: ProofClosure → {d} obligations\n", .{u.closure.obligations.len});
        try w.writeAll("Stage 5: Result → ");
        try ast.writeFinal(w, u.outcome.result.toFinal());
        try w.writeAll("\n\nFinal: ");
        try ast.writeFinal(w, u.outcome.result.toFinal());
        try w.writeAll("\n\n");
    }
    return .{ .ok = try aw.toOwnedSlice() };
}

// ------------------------------------------------------------ crux solve

const Linear = struct { terms: std.ArrayList(arith.Constraint.LinTerm) = .empty, constant: i64 = 0 };

fn linearize(arena: std.mem.Allocator, t: ast.Term, sign: i64, out: *Linear) !bool {
    switch (t) {
        .Var => |v| try out.terms.append(arena, .{ .var_ = v, .coef = sign }),
        .Const => |l| {
            if (l != .Number) return false;
            out.constant += sign * l.Number;
        },
        .Paren => |p| return linearize(arena, p.*, sign, out),
        .BinOp => |b| switch (b.op) {
            .Add => return (try linearize(arena, b.lhs.*, sign, out)) and (try linearize(arena, b.rhs.*, sign, out)),
            .Sub => return (try linearize(arena, b.lhs.*, sign, out)) and (try linearize(arena, b.rhs.*, -sign, out)),
            .Mul => {
                if (lean.evalGround(b.lhs.*)) |k| return linearize(arena, b.rhs.*, sign * k, out);
                if (lean.evalGround(b.rhs.*)) |k| return linearize(arena, b.lhs.*, sign * k, out);
                return false;
            },
            else => return false,
        },
        else => return false,
    }
    return true;
}

const Problem = struct {
    constraints: std.ArrayList(arith.Constraint) = .empty,
    watch: std.ArrayList([]const []const u8) = .empty,
    lo: std.StringArrayHashMapUnmanaged(i64) = .empty,
    hi: std.StringArrayHashMapUnmanaged(i64) = .empty,
    vars: std.StringArrayHashMapUnmanaged(void) = .empty,

    fn bound(self: *Problem, a: std.mem.Allocator, v: []const u8, lo: ?i64, hi: ?i64) !void {
        try self.vars.put(a, v, {});
        if (lo) |l| {
            const g = try self.lo.getOrPut(a, v);
            g.value_ptr.* = if (g.found_existing) @max(g.value_ptr.*, l) else l;
        }
        if (hi) |h| {
            const g = try self.hi.getOrPut(a, v);
            g.value_ptr.* = if (g.found_existing) @min(g.value_ptr.*, h) else h;
        }
    }

    fn add(self: *Problem, a: std.mem.Allocator, c: arith.Constraint, vs: []const []const u8) !void {
        for (vs) |v| try self.vars.put(a, v, {});
        try self.constraints.append(a, c);
        try self.watch.append(a, try a.dupe([]const u8, vs));
    }
};

fn extract(a: std.mem.Allocator, p: *Problem, f: ast.Formula) !?[]const u8 {
    switch (f) {
        .And => |fs| for (fs) |s| if (try extract(a, p, s)) |e| return e,
        .Paren => |i| return extract(a, p, i.*),
        .Sila => |s| return extract(a, p, s.formula.*),
        .Atomic => |at| switch (at) {
            .True => {},
            .Predicate => |pr| {
                if (pr.args.len != 2) return "only comparisons, equations and disequations can be solved";
                const l = pr.args[0];
                const r = pr.args[1];
                const op = pr.name;
                const lv: ?[]const u8 = if (l == .Var) l.Var else null;
                const rv: ?[]const u8 = if (r == .Var) r.Var else null;
                const lk = lean.evalGround(l);
                const rk = lean.evalGround(r);
                const is = struct {
                    fn eq(s: []const u8, x: []const u8) bool {
                        return std.mem.eql(u8, s, x);
                    }
                }.eq;
                if (lv != null and rv != null) {
                    const c: arith.Constraint = if (is(op, "<")) arith.Constraint.lt(lv.?, rv.?) else if (is(op, "≤")) arith.Constraint.le(lv.?, rv.?) else if (is(op, ">")) arith.Constraint.gt(lv.?, rv.?) else arith.Constraint.ge(lv.?, rv.?);
                    try p.add(a, c, &.{ lv.?, rv.? });
                } else if (lv != null and rk != null) {
                    const k = rk.?;
                    if (is(op, "<")) try p.bound(a, lv.?, null, k - 1) else if (is(op, "≤")) try p.bound(a, lv.?, null, k) else if (is(op, ">")) try p.bound(a, lv.?, k + 1, null) else try p.bound(a, lv.?, k, null);
                } else if (lk != null and rv != null) {
                    const k = lk.?;
                    if (is(op, "<")) try p.bound(a, rv.?, k + 1, null) else if (is(op, "≤")) try p.bound(a, rv.?, k, null) else if (is(op, ">")) try p.bound(a, rv.?, null, k - 1) else try p.bound(a, rv.?, null, k);
                } else return "comparisons must relate a variable to a variable or a constant";
            },
            else => return "unsupported atom",
        },
        .Not => |inner| {
            if (inner.* == .Eq and inner.Eq.lhs == .Var) if (lean.evalGround(inner.Eq.rhs)) |k| {
                try p.add(a, arith.Constraint.neq(inner.Eq.lhs.Var, k), &.{inner.Eq.lhs.Var});
                return null;
            };
            return "only `x ≠ constant` negations can be solved";
        },
        .Eq => |e| {
            if (e.lhs == .Var) if (lean.evalGround(e.rhs)) |k| {
                try p.add(a, arith.Constraint.eq(e.lhs.Var, k), &.{e.lhs.Var});
                return null;
            };
            var lin: Linear = .{};
            if (!(try linearize(a, e.lhs, 1, &lin)) or !(try linearize(a, e.rhs, -1, &lin))) return "equations must be linear";
            var vs: std.ArrayList([]const u8) = .empty;
            for (lin.terms.items) |t| try vs.append(a, t.var_);
            try p.add(a, .{ .Linear = .{ .terms = lin.terms.items, .rhs = -lin.constant } }, vs.items);
        },
        else => return "only conjunctions of comparisons and linear equations can be solved",
    }
    return null;
}

const CheckCtx = struct {
    arena: std.mem.Allocator,
    p: *const Problem,

    fn consistent(ctx: *anyopaque, store: *dom.DomainStore) bool {
        const self: *CheckCtx = @ptrCast(@alignCast(ctx));
        var ss = susp.SuspensionStore.init(self.arena);
        for (self.p.constraints.items, self.p.watch.items, 0..) |c, w, i| _ = ss.suspendGoal(c, @intCast(i), w) catch return false;
        susp.propagateStore(&ss, store) catch return false;
        if (ss.anyFailed()) return false;
        // At a complete assignment every constraint must be entailed.
        if (store.allFixed() and ss.activeCount() > 0) return false;
        return true;
    }
};

/// `crux solve`: finite-domain search for each goal that is a conjunction of
/// bounds, comparisons, disequations and linear equations over integers.
pub fn solve(arena: std.mem.Allocator, src: []const u8, opts: Options) !Output {
    const items = switch (try parse(arena, src, opts)) {
        .ok => |i| i,
        .err => |e| return .{ .err = e },
    };
    var aw: ast.W.Allocating = .init(arena);
    const w = &aw.writer;
    for (items, 0..) |it, idx| {
        const low = try lowerRussianForm(arena, it.form);
        const name = it.name orelse try lean.defaultGoalName(arena, low.state, idx);
        var p: Problem = .{};
        if (try extract(arena, &p, low.formula)) |why|
            return .{ .err = try std.fmt.allocPrint(arena, "{s}:{d}:{d}: error: goal {s}: {s}", .{ opts.source_name, it.line, it.col, name, why }) };
        var store = dom.DomainStore.init(arena);
        for (p.vars.keys()) |v| {
            const lo = p.lo.get(v);
            const hi = p.hi.get(v);
            if (lo == null or hi == null)
                return .{ .err = try std.fmt.allocPrint(arena, "{s}:{d}:{d}: error: goal {s}: variable {s} needs a lower and an upper bound", .{ opts.source_name, it.line, it.col, name, v }) };
            try store.setDomain(v, if (lo.? == hi.?) .{ .Fixed = lo.? } else dom.Domain.range(lo.?, hi.?));
        }
        var ctx: CheckCtx = .{ .arena = arena, .p = &p };
        var empty = false;
        for (store.vars()) |v| if (store.getDomain(v).size() == 0) {
            empty = true;
        };
        const r: search.SearchResult = if (empty) .Unsat else try search.searchVars(&store, .FirstFail, p.vars.count() + 2, .{ .ctx = &ctx, .consistent = CheckCtx.consistent });
        try w.print("{s}: ", .{name});
        switch (r) {
            .Sat => |m| {
                try w.writeAll("SAT");
                for (m, 0..) |asg, i| try w.print("{s}{s} = {d}", .{ if (i == 0) " " else ", ", asg.var_, asg.val });
            },
            .Unsat => try w.writeAll("UNSAT"),
            .Unknown => try w.writeAll("UNKNOWN"),
        }
        try w.writeByte('\n');
    }
    return .{ .ok = try aw.toOwnedSlice() };
}

// ------------------------------------------------------------------- tests

const testing = std.testing;

const sample =
    \\-- CRUX sample
    \\theorem comm : равенство(x + 1, 1 + x);
    \\сила(S2[x := 2 + 3], x = 5);
    \\example : 2 * 3 = 6
;

test "pipeline: compile and report end to end" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const units = (try compile(a, sample, .{})).ok;
    try testing.expectEqual(@as(usize, 3), units.len);
    try testing.expectEqualStrings("comm", units[0].name);
    try testing.expectEqualStrings("sila_goal_S2_1", units[1].name);
    try testing.expect(units[1].outcome.result == .Proved);
    try testing.expectEqual(omega.Decider.sas, units[1].outcome.decided_by);
    try testing.expectEqual(omega.Decider.lean, units[2].outcome.decided_by);
    const rep = (try run(a, sample, .{})).ok;
    try testing.expect(std.mem.indexOf(u8, rep, "Stage 4: ProofClosure → 1 obligations") != null);
    const chk = (try check(a, sample, .{})).ok;
    try testing.expectEqualStrings("comm: PROVED [sas]\nsila_goal_S2_1: PROVED [sas]\nsila_goal_S0_2: PROVED [lean]\n", chk);
}

test "pipeline: every emitter produces its artifact" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const smt = (try emitSmt(a, sample, .{ .source_name = "s.crux" })).ok;
    try testing.expect(std.mem.indexOf(u8, smt, "(reset)\n; goal sila_goal_S2_1\n") != null);
    const ln = (try emitLean(a, sample, .{})).ok;
    try testing.expect(std.mem.indexOf(u8, ln, "theorem comm (x : Int) :") != null);
    try testing.expect(std.mem.endsWith(u8, ln, "end CruxGenerated\n"));
    const sr = (try emitSas(a, sample, .{})).ok;
    try testing.expect(std.mem.indexOf(u8, sr, "initial: { iter ∈ [0, 2], x ∈ [5, 5] }") != null);
    const cu = (try emitCuda(a, sample, .{})).ok;
    try testing.expect(std.mem.indexOf(u8, cu, "crux_analyze_2(&iterations)") != null);
    const ce = (try emitCert(a, sample, .{})).ok;
    try testing.expect(std.mem.indexOf(u8, ce, "\"kind\": \"SASCert\"") != null);
    const tk = (try emitTokens(a, "сила", .{})).ok;
    try testing.expectEqualStrings("1:1\tSila\tсила\n1:5\tEof\n", tk);
    const bad = try emitSmt(a, "сила(S1 x)", .{ .source_name = "bad.crux" });
    try testing.expectEqualStrings("bad.crux:1:9: error: expected Comma, got Ident 'x'", bad.err);
}

test "pipeline: solve with domains, search and suspensions" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const out = (try solve(a, "0 ≤ x ∧ x ≤ 9 ∧ 0 ≤ y ∧ y ≤ 9 ∧ x < y ∧ x + y = 10 ∧ x ≠ 1; 0 ≤ z ∧ z ≤ 3 ∧ z > 5", .{})).ok;
    try testing.expectEqualStrings("sila_goal_S0_0: SAT x = 2, y = 8\nsila_goal_S0_1: UNSAT\n", out);
}
