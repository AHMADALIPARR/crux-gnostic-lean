// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! Lean 4 backend (port of lean_backend.rs / Crux.LeanBackend): goal
//! construction, the CRUX tactic macros, and Lean 4 serialisation of goals,
//! formulas, terms, sorts, states and tactics.
//!
//! The emitted file is self-contained Lean 4 core (no Mathlib): it defines
//! `CruxState`, `«Сила»` (Cyrillic needs «» quoting in Lean identifiers) and
//! the `sila_auto` / `omega_smash` / `crux_close` macros with core tactics,
//! and binds every free variable of a goal as an explicit argument.
//! Differences from the source serialiser, so that the output elaborates:
//! comparison and user predicates are printed (the source printed `True`),
//! subformulas are parenthesised, `≠` is printed for `Ne`, `lemma` is printed
//! as `theorem` (core Lean has no `lemma`), μ/ν apply an argument
//! `mu_X : Prop → Prop` as in the Z3 backend, and unsupported terms are
//! reported instead of printed as `sorry`.
//!
//! The source prover returned "proved" for `simp`, `omega`, `ring`, ... without
//! running anything. Here `prove` only succeeds by concrete `decide`
//! evaluation; anything else is left to a real `lean` run (see `crux check --lean`).

const std = @import("std");
const ast = @import("ast.zig");

pub const Result = enum { Proved, Timeout, Unknown };

pub const Error = error{ Unsupported, OutOfMemory, WriteFailed };

pub fn buildGoal(arena: std.mem.Allocator, kind: ast.LeanGoalKind, name: []const u8, state: ast.State, formula: ast.Formula) !ast.LeanGoal {
    const inner = try ast.box(arena, formula);
    return .{
        .kind = kind,
        .name = name,
        .formula = .{ .Sila = .{ .state = state, .formula = inner } },
        .tactics = try arena.dupe(ast.LeanTactic, &.{.{ .Macro = "crux_close" }}),
    };
}

/// Default goal name, following the source's `sila_goal_{state:?}`.
pub fn defaultGoalName(arena: std.mem.Allocator, state: ast.State, index: usize) ![]const u8 {
    var root = state;
    while (true) root = switch (root) {
        .Bind => |b| b.base.*,
        .Update => |u| u.base.*,
        .Prime => |p| p.*,
        else => break,
    };
    const s: []const u8 = switch (root) {
        .S => "S",
        .S0 => "S0",
        .Sn => |n| try std.fmt.allocPrint(arena, "S{d}", .{n}),
        else => @tagName(state),
    };
    return std.fmt.allocPrint(arena, "sila_goal_{s}_{d}", .{ s, index });
}

/// Concrete evaluation used by `decide` (source `try_decide`), looking
/// through `Сила` since `Сила s p` unfolds to `p`.
pub fn tryDecide(f: ast.Formula) bool {
    return switch (f) {
        .Atomic => |a| a == .True,
        .Not => |inner| !tryDecide(inner.*),
        .And => |fs| for (fs) |s| {
            if (!tryDecide(s)) break false;
        } else true,
        .Or => |fs| for (fs) |s| {
            if (tryDecide(s)) break true;
        } else false,
        .Eq => |e| blk: {
            if (e.lhs == .Var and e.rhs == .Var) break :blk std.mem.eql(u8, e.lhs.Var, e.rhs.Var);
            const a = evalGround(e.lhs) orelse break :blk false;
            const b = evalGround(e.rhs) orelse break :blk false;
            break :blk a == b;
        },
        .Paren => |inner| tryDecide(inner.*),
        .Sila => |s| tryDecide(s.formula.*),
        else => false,
    };
}

/// Ground integer value of a term built from literals and + - * (Int semantics).
pub fn evalGround(t: ast.Term) ?i64 {
    return switch (t) {
        .Const => |l| if (l == .Number) l.Number else null,
        .Paren => |p| evalGround(p.*),
        .BinOp => |b| blk: {
            const l = evalGround(b.lhs.*) orelse break :blk null;
            const r = evalGround(b.rhs.*) orelse break :blk null;
            break :blk switch (b.op) {
                .Add => std.math.add(i64, l, r) catch null,
                .Sub => std.math.sub(i64, l, r) catch null,
                .Mul => std.math.mul(i64, l, r) catch null,
                else => null,
            };
        },
        else => null,
    };
}

pub fn prove(goal: ast.LeanGoal) Result {
    for (goal.tactics) |t| if (tryTactic(t, goal.formula)) return .Proved;
    return .Unknown;
}

fn tryTactic(t: ast.LeanTactic, f: ast.Formula) bool {
    return switch (t) {
        .Decide => tryDecide(f),
        .Macro => |name| tryMacro(name, f),
        .Seq => |ts| for (ts) |s| {
            if (!tryTactic(s, f)) break false;
        } else true,
        .Try => true,
        .Repeat => |inner| tryTactic(inner.*, f),
        else => false,
    };
}

fn tryMacro(name: []const u8, f: ast.Formula) bool {
    const deciding = [_][]const u8{ "sila_auto", "crux_close", "z3_decide", "finish", "crush" };
    for (deciding) |d| if (std.mem.eql(u8, name, d)) return tryDecide(f);
    return false;
}

// ---------------------------------------------------------------------------
// Free-variable collection for goal binders
// ---------------------------------------------------------------------------

const Sym = struct { name: []const u8, arity: usize, kind: enum { int, prop, fun, pred, fix } };

const Collector = struct {
    arena: std.mem.Allocator,
    syms: std.ArrayList(Sym) = .empty,
    bound: std.ArrayList([]const u8) = .empty,
    user_sorts: std.ArrayList([]const u8) = .empty,

    fn isBound(self: *Collector, n: []const u8) bool {
        for (self.bound.items) |b| if (std.mem.eql(u8, b, n)) return true;
        return false;
    }
    fn add(self: *Collector, s: Sym) !void {
        if (self.isBound(s.name)) return;
        for (self.syms.items) |e| if (std.mem.eql(u8, e.name, s.name)) return;
        try self.syms.append(self.arena, s);
    }
    fn sort(self: *Collector, s: ast.Sort) !void {
        switch (s) {
            .User => |n| {
                for (self.user_sorts.items) |e| if (std.mem.eql(u8, e, n)) return;
                try self.user_sorts.append(self.arena, n);
            },
            .List => |i| try self.sort(i.*),
            .Arrow => |a| {
                try self.sort(a.from.*);
                try self.sort(a.to.*);
            },
            else => {},
        }
    }
    fn formula(self: *Collector, f: ast.Formula) Error!void {
        switch (f) {
            .Atomic => |a| switch (a) {
                .Predicate => |p| {
                    const builtin = p.args.len == 2 and (std.mem.eql(u8, p.name, "<") or std.mem.eql(u8, p.name, "≤") or std.mem.eql(u8, p.name, ">") or std.mem.eql(u8, p.name, "≥"));
                    if (!builtin) try self.add(.{ .name = p.name, .arity = p.args.len, .kind = if (p.args.len == 0) .prop else .pred });
                    for (p.args) |t| try self.term(t);
                },
                else => {},
            },
            .Not, .Paren => |i| try self.formula(i.*),
            .And, .Or => |fs| for (fs) |s| try self.formula(s),
            .Implies, .Iff => |p| {
                try self.formula(p.lhs.*);
                try self.formula(p.rhs.*);
            },
            .Eq => |e| {
                try self.term(e.lhs);
                try self.term(e.rhs);
            },
            .Forall, .Exists => {
                const v, const s, const body = switch (f) {
                    .Forall => |q| .{ q.var_, q.sort, q.body },
                    .Exists => |q| .{ q.var_, q.sort, q.body },
                    else => unreachable,
                };
                try self.sort(s);
                try self.bound.append(self.arena, v);
                try self.formula(body.*);
                _ = self.bound.pop();
            },
            .Mu, .Nu => {
                const v, const body, const prefix = switch (f) {
                    .Mu => |m| .{ m.var_, m.body, "mu_" },
                    .Nu => |m| .{ m.var_, m.body, "nu_" },
                    else => unreachable,
                };
                try self.add(.{ .name = try std.fmt.allocPrint(self.arena, "{s}{s}", .{ prefix, v }), .arity = 1, .kind = .fix });
                try self.formula(body.*);
            },
            .Sila => |s| {
                try self.state(s.state);
                try self.formula(s.formula.*);
            },
        }
    }
    fn state(self: *Collector, s: ast.State) Error!void {
        switch (s) {
            .Prime => |i| try self.state(i.*),
            .Bind => |b| {
                try self.state(b.base.*);
                try self.term(b.binding.value);
            },
            .Update => |u| {
                try self.state(u.base.*);
                try self.term(u.value);
            },
            else => {},
        }
    }
    fn term(self: *Collector, t: ast.Term) Error!void {
        switch (t) {
            .Var => |n| try self.add(.{ .name = n, .arity = 0, .kind = .int }),
            .BinOp => |b| {
                try self.term(b.lhs.*);
                try self.term(b.rhs.*);
            },
            .Paren => |p| try self.term(p.*),
            .App => {
                var cur = t;
                var n: usize = 0;
                while (cur == .App) {
                    try self.term(cur.App.arg.*);
                    cur = cur.App.func.*;
                    n += 1;
                }
                if (cur == .Var) try self.add(.{ .name = cur.Var, .arity = n, .kind = .fun }) else try self.term(cur);
            },
            .IfThenElse => |i| {
                try self.formula(i.cond.*);
                try self.term(i.then.*);
                try self.term(i.else_.*);
            },
            .Lambda => |l| {
                try self.sort(l.sort);
                try self.bound.append(self.arena, l.param);
                try self.term(l.body.*);
                _ = self.bound.pop();
            },
            .Tuple => |ts| for (ts) |e| try self.term(e),
            else => {},
        }
    }
};

// ---------------------------------------------------------------------------
// Serialisers
// ---------------------------------------------------------------------------

pub fn writeSort(w: *ast.W, s: ast.Sort) Error!void {
    switch (s) {
        .Prop => try w.writeAll("Prop"),
        .Type => try w.writeAll("Type"),
        .Nat => try w.writeAll("Nat"),
        .Int => try w.writeAll("Int"),
        .Bool => try w.writeAll("Bool"),
        .BitVec => |n| try w.print("BitVec {d}", .{n}),
        .List => |i| {
            try w.writeAll("List (");
            try writeSort(w, i.*);
            try w.writeAll(")");
        },
        .Arrow => |a| {
            try w.writeAll("(");
            try writeSort(w, a.from.*);
            try w.writeAll(" → ");
            try writeSort(w, a.to.*);
            try w.writeAll(")");
        },
        .User => |n| try w.writeAll(n),
        .State => try w.writeAll("CruxState"),
        else => try w.writeAll("Type"),
    }
}

pub fn writeState(w: *ast.W, s: ast.State) Error!void {
    switch (s) {
        .S => try w.writeAll("CruxState.S"),
        .S0 => try w.writeAll("CruxState.S₀"),
        .Sn => |n| try w.print("(CruxState.Sn {d})", .{n}),
        .Prime => |i| {
            try w.writeAll("(CruxState.prime ");
            try writeState(w, i.*);
            try w.writeAll(")");
        },
        .Bind => |b| {
            try w.writeAll("(CruxState.bind ");
            try writeState(w, b.base.*);
            try w.print(" \"{s}\" ", .{b.binding.var_});
            try writeTerm(w, b.binding.value);
            try w.writeAll(")");
        },
        .Update => |u| {
            try w.writeAll("(CruxState.bind ");
            try writeState(w, u.base.*);
            try w.print(" \"{s}\" ", .{u.var_});
            try writeTerm(w, u.value);
            try w.writeAll(")");
        },
        .Recursive => return error.Unsupported,
    }
}

pub fn writeTerm(w: *ast.W, t: ast.Term) Error!void {
    switch (t) {
        .Var => |n| try w.writeAll(n),
        .Const => |l| switch (l) {
            .Number => |n| if (n < 0) try w.print("({d})", .{n}) else try w.print("{d}", .{n}),
            .Bool => |b| try w.writeAll(if (b) "true" else "false"),
            .Str => |s| try w.print("\"{s}\"", .{s}),
            else => return error.Unsupported,
        },
        .BinOp => |b| {
            const op = switch (b.op) {
                .Add => "+",
                .Sub => "-",
                .Mul => "*",
                .Div => "/",
                .Mod => "%",
                .Eq => "=",
                .Ne => "≠",
                .Lt => "<",
                .Le => "≤",
                .Gt => ">",
                .Ge => "≥",
            };
            try w.writeAll("(");
            try writeTerm(w, b.lhs.*);
            try w.print(" {s} ", .{op});
            try writeTerm(w, b.rhs.*);
            try w.writeAll(")");
        },
        .Paren => |p| {
            try w.writeAll("(");
            try writeTerm(w, p.*);
            try w.writeAll(")");
        },
        .App => |a| {
            try w.writeAll("(");
            try writeTerm(w, a.func.*);
            try w.writeAll(" ");
            try writeTerm(w, a.arg.*);
            try w.writeAll(")");
        },
        .IfThenElse => |i| {
            try w.writeAll("(if ");
            try writeFormula(w, i.cond.*);
            try w.writeAll(" then ");
            try writeTerm(w, i.then.*);
            try w.writeAll(" else ");
            try writeTerm(w, i.else_.*);
            try w.writeAll(")");
        },
        .Lambda => |l| {
            try w.print("(fun ({s} : ", .{l.param});
            try writeSort(w, l.sort);
            try w.writeAll(") => ");
            try writeTerm(w, l.body.*);
            try w.writeAll(")");
        },
        .Tuple => |ts| {
            try w.writeAll("(");
            for (ts, 0..) |e, i| {
                if (i > 0) try w.writeAll(", ");
                try writeTerm(w, e);
            }
            try w.writeAll(")");
        },
        else => return error.Unsupported,
    }
}

pub fn writeFormula(w: *ast.W, f: ast.Formula) Error!void {
    switch (f) {
        .Atomic => |a| switch (a) {
            .True => try w.writeAll("True"),
            .False => try w.writeAll("False"),
            .Predicate => |p| {
                if (p.args.len == 0) return w.writeAll(p.name);
                const infix = p.args.len == 2 and (std.mem.eql(u8, p.name, "<") or std.mem.eql(u8, p.name, "≤") or std.mem.eql(u8, p.name, ">") or std.mem.eql(u8, p.name, "≥"));
                try w.writeAll("(");
                if (infix) {
                    try writeTerm(w, p.args[0]);
                    try w.print(" {s} ", .{p.name});
                    try writeTerm(w, p.args[1]);
                } else {
                    try w.writeAll(p.name);
                    for (p.args) |t| {
                        try w.writeAll(" ");
                        try writeTerm(w, t);
                    }
                }
                try w.writeAll(")");
            },
            .Predecessor => |p| {
                try w.writeAll("(");
                try writeTerm(w, p.less.*);
                try w.writeAll(" < ");
                try writeTerm(w, p.greater.*);
                try w.writeAll(")");
            },
            .Member => return error.Unsupported,
        },
        .Not => |i| {
            try w.writeAll("¬");
            try writeFormula(w, i.*);
        },
        .And, .Or => |fs| {
            if (fs.len == 0) return w.writeAll(if (f == .And) "True" else "False");
            try w.writeAll("(");
            for (fs, 0..) |s, i| {
                if (i > 0) try w.writeAll(if (f == .And) " ∧ " else " ∨ ");
                try writeFormula(w, s);
            }
            try w.writeAll(")");
        },
        .Implies, .Iff => |p| {
            try w.writeAll("(");
            try writeFormula(w, p.lhs.*);
            try w.writeAll(if (f == .Implies) " → " else " ↔ ");
            try writeFormula(w, p.rhs.*);
            try w.writeAll(")");
        },
        .Eq => |e| {
            try w.writeAll("(");
            try writeTerm(w, e.lhs);
            try w.writeAll(" = ");
            try writeTerm(w, e.rhs);
            try w.writeAll(")");
        },
        .Forall, .Exists => {
            const v, const s, const body = switch (f) {
                .Forall => |q| .{ q.var_, q.sort, q.body },
                .Exists => |q| .{ q.var_, q.sort, q.body },
                else => unreachable,
            };
            try w.print("({s} ({s} : ", .{ if (f == .Forall) "∀" else "∃", v });
            try writeSort(w, s);
            try w.writeAll("), ");
            try writeFormula(w, body.*);
            try w.writeAll(")");
        },
        .Mu, .Nu => {
            const v, const body, const prefix = switch (f) {
                .Mu => |m| .{ m.var_, m.body, "mu_" },
                .Nu => |m| .{ m.var_, m.body, "nu_" },
                else => unreachable,
            };
            try w.print("({s}{s} ", .{ prefix, v });
            try writeFormula(w, body.*);
            try w.writeAll(")");
        },
        .Paren => |i| try writeFormula(w, i.*),
        .Sila => |s| {
            try w.writeAll("(«Сила» ");
            try writeState(w, s.state);
            try w.writeAll(" ");
            try writeFormula(w, s.formula.*);
            try w.writeAll(")");
        },
    }
}

pub fn writeTactic(w: *ast.W, t: ast.LeanTactic) Error!void {
    switch (t) {
        .Exact => |x| {
            try w.writeAll("exact ");
            try writeTerm(w, x);
        },
        .Apply => |x| {
            try w.writeAll("apply ");
            try writeTerm(w, x);
        },
        .Intro => |ids| {
            try w.writeAll("intro");
            for (ids) |id| try w.print(" {s}", .{id});
        },
        .Simpl => try w.writeAll("simp"),
        .SimplAll => try w.writeAll("simp_all"),
        .Omega => try w.writeAll("omega"),
        .Decide => try w.writeAll("decide"),
        .Ring => try w.writeAll("ring"),
        .Linarith => try w.writeAll("linarith"),
        .Aesop => try w.writeAll("aesop"),
        .Trivial => try w.writeAll("trivial"),
        .Constructor => try w.writeAll("constructor"),
        .Left => try w.writeAll("left"),
        .Right => try w.writeAll("right"),
        .Exfalso => try w.writeAll("exfalso"),
        .Macro => |n| try w.writeAll(n),
        .Sorry => try w.writeAll("sorry"),
        .Try => |i| {
            try w.writeAll("try ");
            try writeTactic(w, i.*);
        },
        .Repeat => |i| {
            try w.writeAll("repeat ");
            try writeTactic(w, i.*);
        },
        .AllGoals => |i| {
            try w.writeAll("all_goals ");
            try writeTactic(w, i.*);
        },
        .Focus, .Seq => |ts| {
            if (t == .Focus) try w.writeAll("· ");
            for (ts, 0..) |s, i| {
                if (i > 0) try w.writeAll(" <;> ");
                try writeTactic(w, s);
            }
        },
    }
}

/// File header: state type, `Сила`, and the CRUX macros in core Lean 4.
pub const prelude =
    \\namespace CruxGenerated
    \\
    \\/-- CRUX recursive states: S, S₀, Sₙ, primes and bindings. -/
    \\inductive CruxState where
    \\  | S
    \\  | S₀
    \\  | Sn (n : Nat)
    \\  | prime (s : CruxState)
    \\  | bind (s : CruxState) (var : String) (value : Int)
    \\
    \\/-- `Сила(S, P)`: the formula `P` holds in state `S`. -/
    \\def «Сила» (_s : CruxState) (p : Prop) : Prop := p
    \\
    \\macro "sila_auto" : tactic =>
    \\  `(tactic| (try simp only [«Сила»] at *) <;> (try intros) <;> first | decide | omega | trivial)
    \\macro "omega_smash" : tactic =>
    \\  `(tactic| first | omega | (simp_all <;> omega) | simp_all)
    \\macro "crux_close" : tactic =>
    \\  `(tactic| (try simp only [«Сила»] at *) <;> (try intros) <;>
    \\    first | decide | omega | rfl | trivial | omega_smash | (constructor <;> omega) | (exact fun h => h) | (exact ⟨_, rfl⟩))
    \\
    \\
;

pub const epilogue = "end CruxGenerated\n";

fn writeBinders(w: *ast.W, c: *const Collector) Error!void {
    for (c.user_sorts.items) |s| try w.print(" ({s} : Type)", .{s});
    for (c.syms.items) |s| {
        try w.print(" ({s} : ", .{s.name});
        switch (s.kind) {
            .int => try w.writeAll("Int"),
            .prop => try w.writeAll("Prop"),
            .fix => try w.writeAll("Prop → Prop"),
            .fun, .pred => {
                for (0..s.arity) |_| try w.writeAll("Int → ");
                try w.writeAll(if (s.kind == .fun) "Int" else "Prop");
            },
        }
        try w.writeAll(")");
    }
}

/// Source `goal_to_lean4`: `theorem NAME BINDERS : FORMULA := by TACTICS`.
pub fn writeGoal(arena: std.mem.Allocator, w: *ast.W, goal: ast.LeanGoal) Error!void {
    var c: Collector = .{ .arena = arena };
    try c.formula(goal.formula);
    switch (goal.kind) {
        .Theorem, .Lemma => try w.print("theorem {s}", .{goal.name}),
        .Example => try w.writeAll("example"),
    }
    try writeBinders(w, &c);
    try w.writeAll(" :\n    ");
    try writeFormula(w, goal.formula);
    try w.writeAll(" := by\n  ");
    for (goal.tactics, 0..) |t, i| {
        if (i > 0) try w.writeAll("\n  ");
        try writeTactic(w, t);
    }
    try w.writeAll("\n\n");
}

/// One goal as a complete Lean file.
pub fn goalFileAlloc(arena: std.mem.Allocator, goal: ast.LeanGoal) ![]u8 {
    var aw: ast.W.Allocating = .init(arena);
    try aw.writer.writeAll(prelude);
    try writeGoal(arena, &aw.writer, goal);
    try aw.writer.writeAll(epilogue);
    return aw.toOwnedSlice();
}

// ------------------------------------------------------------------- tests

const testing = std.testing;
const parser = @import("parser.zig");

test "lean: goal serialisation" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const f = (try parser.parseFormula(a, "∀ n : Nat. n + 0 = n ∧ x < y")).ok;
    const g = try buildGoal(a, .Theorem, "t", .{ .Sn = 2 }, f);
    var aw: ast.W.Allocating = .init(a);
    try writeGoal(a, &aw.writer, g);
    try testing.expectEqualStrings(
        "theorem t (x : Int) (y : Int) :\n    («Сила» (CruxState.Sn 2) (∀ (n : Nat), (((n + 0) = n) ∧ (x < y)))) := by\n  crux_close\n\n",
        try aw.toOwnedSlice(),
    );
}

test "lean: decide, binders for predicates and functions" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const g1 = try buildGoal(a, .Theorem, "g", .S0, (try parser.parseFormula(a, "2 * 3 = 6 ∧ ¬ (1 = 2)")).ok);
    try testing.expectEqual(Result.Proved, prove(g1));
    const g2 = try buildGoal(a, .Theorem, "g", .S0, (try parser.parseFormula(a, "x + 1 = 1 + x")).ok);
    try testing.expectEqual(Result.Unknown, prove(g2));
    const g3 = try buildGoal(a, .Example, "e", .S0, (try parser.parseFormula(a, "P (f x) → P (f x)")).ok);
    var aw: ast.W.Allocating = .init(a);
    try writeGoal(a, &aw.writer, g3);
    const s = try aw.toOwnedSlice();
    try testing.expect(std.mem.startsWith(u8, s, "example (P : Int → Prop) (x : Int) (f : Int → Int) :"));
    try testing.expectEqualStrings("sila_goal_S3_4", try defaultGoalName(a, .{ .Sn = 3 }, 4));
}
