// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! Z3 backend: CRUX AST -> Z3 query -> SMT-LIB 2 (port of z3_backend.rs /
//! Crux.Z3Backend). Integers are 32-bit bit-vectors, as in the source
//! (`declare-const v (_ BitVec 32)`, `bvadd`, `bvult`, ...).
//!
//! The source left several cases as `true`/`nil` placeholders; here they are
//! translated so that the emitted file is accepted by z3:
//! - `<`, `≤`, `>`, `≥` predicates become `bvult`/`bvule`/`bvugt`/`bvuge`
//!   (the comparison operators the source maps `BinOp::Lt` etc. to);
//! - other predicates and applied functions become `declare-fun` symbols;
//! - quantified variables are bound only by their quantifier, and their body
//!   is scanned for free variables (the source declared the bound name and
//!   skipped the body); numeric binder sorts use the same bit-vector sort;
//! - `μX. P` / `νX. P` apply an uninterpreted `mu_X` / `nu_X : Bool -> Bool`
//!   to the body (the source applied `X` itself);
//! - `if c then a else b` becomes `ite`; unsupported terms are reported.
//! `check` runs z3 when it is on PATH (the source fell back to Unknown).

const std = @import("std");
const ast = @import("ast.zig");

pub const CheckResult = union(enum) {
    Sat,
    Unsat,
    Model: []const ast.ModelEntry,
    Unknown,
    Timeout,
};

pub const BuildError = error{ Unsupported, OutOfMemory };

pub const Builder = struct {
    arena: std.mem.Allocator,
    consts: std.ArrayList([]const u8) = .empty,
    bool_consts: std.ArrayList([]const u8) = .empty,
    funs: std.ArrayList(struct { name: []const u8, arity: usize, ret_bool: bool }) = .empty,
    bound: std.ArrayList([]const u8) = .empty,
    unsupported: ?[]const u8 = null,

    fn isBound(self: *Builder, name: []const u8) bool {
        var i = self.bound.items.len;
        while (i > 0) {
            i -= 1;
            if (std.mem.eql(u8, self.bound.items[i], name)) return true;
        }
        return false;
    }

    fn addUnique(self: *Builder, list: *std.ArrayList([]const u8), name: []const u8) !void {
        for (list.items) |n| if (std.mem.eql(u8, n, name)) return;
        try list.append(self.arena, name);
    }

    fn addFun(self: *Builder, name: []const u8, arity: usize, ret_bool: bool) !void {
        for (self.funs.items) |f| if (std.mem.eql(u8, f.name, name) and f.arity == arity) return;
        try self.funs.append(self.arena, .{ .name = name, .arity = arity, .ret_bool = ret_bool });
    }

    fn box(self: *Builder, e: ast.Z3Expr) BuildError!*const ast.Z3Expr {
        return ast.box(self.arena, e);
    }

    fn bin(self: *Builder, comptime tag: std.meta.Tag(ast.Z3Expr), a: ast.Z3Expr, b: ast.Z3Expr) BuildError!ast.Z3Expr {
        const pa = try self.box(a);
        const pb = try self.box(b);
        return @unionInit(ast.Z3Expr, @tagName(tag), .{ .lhs = pa, .rhs = pb });
    }

    pub fn formula(self: *Builder, f: ast.Formula) BuildError!ast.Z3Expr {
        switch (f) {
            .Atomic => |a| return self.atomic(a),
            .Not => |inner| return .{ .Not = try self.box(try self.formula(inner.*)) },
            .And, .Or => |fs| {
                const out = try self.arena.alloc(ast.Z3Expr, fs.len);
                for (fs, 0..) |sub, i| out[i] = try self.formula(sub);
                return if (f == .And) .{ .And = out } else .{ .Or = out };
            },
            .Implies => |p| return self.bin(.Implies, try self.formula(p.lhs.*), try self.formula(p.rhs.*)),
            .Iff => |p| {
                const la = try self.formula(p.lhs.*);
                const lb = try self.formula(p.rhs.*);
                const out = try self.arena.alloc(ast.Z3Expr, 2);
                out[0] = try self.bin(.Implies, la, lb);
                out[1] = try self.bin(.Implies, lb, la);
                return .{ .And = out };
            },
            .Eq => |e| return self.bin(.Eq, try self.term(e.lhs), try self.term(e.rhs)),
            .Forall, .Exists => {
                const v, const sort, const body = switch (f) {
                    .Forall => |q| .{ q.var_, q.sort, q.body },
                    .Exists => |q| .{ q.var_, q.sort, q.body },
                    else => unreachable,
                };
                try self.bound.append(self.arena, v);
                const b = try self.formula(body.*);
                _ = self.bound.pop();
                const vars = try self.arena.dupe(ast.Z3Binder, &.{.{ .name = v, .sort = sort }});
                const pb = try self.box(b);
                return if (f == .Forall) .{ .Forall = .{ .vars = vars, .body = pb } } else .{ .Exists = .{ .vars = vars, .body = pb } };
            },
            .Paren => |inner| return self.formula(inner.*),
            .Sila => |s| return self.formula(s.formula.*),
            .Mu, .Nu => {
                const v, const body, const prefix = switch (f) {
                    .Mu => |m| .{ m.var_, m.body, "mu_" },
                    .Nu => |m| .{ m.var_, m.body, "nu_" },
                    else => unreachable,
                };
                const name = try std.fmt.allocPrint(self.arena, "{s}{s}", .{ prefix, v });
                try self.addFun(name, 1, true);
                const args = try self.arena.dupe(ast.Z3Expr, &.{try self.formula(body.*)});
                return .{ .App = .{ .func = name, .args = args } };
            },
        }
    }

    fn atomic(self: *Builder, a: ast.Atomic) BuildError!ast.Z3Expr {
        switch (a) {
            .True => return .{ .Const = "true" },
            .False => return .{ .Const = "false" },
            .Predicate => |p| {
                if (p.args.len == 2) {
                    const l = p.args[0];
                    const r = p.args[1];
                    if (std.mem.eql(u8, p.name, "<")) return self.bin(.Lt, try self.term(l), try self.term(r));
                    if (std.mem.eql(u8, p.name, "≤")) return self.bin(.Le, try self.term(l), try self.term(r));
                    if (std.mem.eql(u8, p.name, ">")) return self.bin(.Gt, try self.term(l), try self.term(r));
                    if (std.mem.eql(u8, p.name, "≥")) return self.bin(.Ge, try self.term(l), try self.term(r));
                }
                if (p.args.len == 0) {
                    if (!self.isBound(p.name)) try self.addUnique(&self.bool_consts, p.name);
                    return .{ .Const = p.name };
                }
                try self.addFun(p.name, p.args.len, true);
                const args = try self.arena.alloc(ast.Z3Expr, p.args.len);
                for (p.args, 0..) |t, i| args[i] = try self.term(t);
                return .{ .App = .{ .func = p.name, .args = args } };
            },
            .Predecessor => |p| return self.bin(.Lt, try self.term(p.less.*), try self.term(p.greater.*)),
            .Member => {
                self.unsupported = "set membership";
                return error.Unsupported;
            },
        }
    }

    pub fn term(self: *Builder, t: ast.Term) BuildError!ast.Z3Expr {
        switch (t) {
            .Var => |name| {
                if (!self.isBound(name)) try self.addUnique(&self.consts, name);
                return .{ .Const = name };
            },
            .Const => |lit| switch (lit) {
                .Number => |n| return .{ .Lit = .{ .value = n, .sort = .{ .BitVec = 32 } } },
                .Bool => |b| return .{ .Const = if (b) "true" else "false" },
                else => {
                    self.unsupported = "string, nil or unit literal";
                    return error.Unsupported;
                },
            },
            .BinOp => |b| {
                const l = try self.term(b.lhs.*);
                const r = try self.term(b.rhs.*);
                return switch (b.op) {
                    .Add => self.bin(.BvAdd, l, r),
                    .Sub => self.bin(.BvSub, l, r),
                    .Mul => self.bin(.BvMul, l, r),
                    .Eq => self.bin(.Eq, l, r),
                    .Ne => .{ .Distinct = try self.arena.dupe(ast.Z3Expr, &.{ l, r }) },
                    .Lt => self.bin(.Lt, l, r),
                    .Le => self.bin(.Le, l, r),
                    .Gt => self.bin(.Gt, l, r),
                    .Ge => self.bin(.Ge, l, r),
                    .Div => .{ .App = .{ .func = "bvudiv", .args = try self.arena.dupe(ast.Z3Expr, &.{ l, r }) } },
                    .Mod => .{ .App = .{ .func = "bvurem", .args = try self.arena.dupe(ast.Z3Expr, &.{ l, r }) } },
                };
            },
            .App => {
                var args: std.ArrayList(ast.Z3Expr) = .empty;
                var cur = t;
                while (cur == .App) {
                    try args.insert(self.arena, 0, try self.term(cur.App.arg.*));
                    cur = cur.App.func.*;
                }
                if (cur != .Var) {
                    self.unsupported = "application of a non-identifier";
                    return error.Unsupported;
                }
                try self.addFun(cur.Var, args.items.len, false);
                return .{ .App = .{ .func = cur.Var, .args = try args.toOwnedSlice(self.arena) } };
            },
            .Paren => |inner| return self.term(inner.*),
            .IfThenElse => |ite| {
                const c = try self.box(try self.formula(ite.cond.*));
                const a = try self.box(try self.term(ite.then.*));
                const b = try self.box(try self.term(ite.else_.*));
                return .{ .Ite = .{ .cond = c, .then = a, .else_ = b } };
            },
            else => {
                self.unsupported = @tagName(t);
                return error.Unsupported;
            },
        }
    }
};

pub const Solver = struct {
    context: ast.Z3Context = .{},

    /// Rust `Z3Solver::build_query`: declarations, `(assert φ)`, `(check-sat)`, `(get-model)`.
    pub fn buildQuery(self: Solver, arena: std.mem.Allocator, state: ast.State, f: ast.Formula) BuildError!struct { query: ast.Z3Query, builder: Builder } {
        _ = state;
        var b: Builder = .{ .arena = arena };
        const e = try b.formula(f);
        var cmds: std.ArrayList(ast.Z3Command) = .empty;
        for (b.consts.items) |v| try cmds.append(arena, .{ .DeclareConst = .{ .name = v, .sort = .{ .BitVec = 32 } } });
        for (b.bool_consts.items) |v| try cmds.append(arena, .{ .DeclareConst = .{ .name = v, .sort = .Bool } });
        for (b.funs.items) |fun| {
            const args = try arena.alloc(ast.Sort, fun.arity);
            const is_fixpoint = std.mem.startsWith(u8, fun.name, "mu_") or std.mem.startsWith(u8, fun.name, "nu_");
            for (args) |*s| s.* = if (is_fixpoint) .Bool else .{ .BitVec = 32 };
            try cmds.append(arena, .{ .DeclareFun = .{ .name = fun.name, .arg_sorts = args, .ret_sort = if (fun.ret_bool) .Bool else .{ .BitVec = 32 } } });
        }
        try cmds.append(arena, .{ .Assert = try ast.box(arena, e) });
        try cmds.append(arena, .CheckSat);
        if (self.context.model) try cmds.append(arena, .GetModel);
        return .{ .query = .{ .context = self.context, .commands = try cmds.toOwnedSlice(arena) }, .builder = b };
    }
};

fn sortToSmt(s: ast.Sort) []const u8 {
    return switch (s) {
        .Bool, .Prop => "Bool",
        .BitVec => |w| if (w == 64) "(_ BitVec 64)" else "(_ BitVec 32)",
        else => "(_ BitVec 32)",
    };
}

pub fn writeExpr(w: *ast.W, e: ast.Z3Expr) ast.W.Error!void {
    switch (e) {
        .Const => |n| try w.writeAll(n),
        .Lit => |l| switch (l.sort) {
            .BitVec => |width| {
                const mask: u64 = if (width >= 64) std.math.maxInt(u64) else (@as(u64, 1) << @intCast(width)) - 1;
                try w.print("(_ bv{d} {d})", .{ @as(u64, @bitCast(l.value)) & mask, width });
            },
            else => try w.print("{d}", .{l.value}),
        },
        .And, .Or, .Distinct => |es| {
            try w.writeAll(switch (e) {
                .And => "(and",
                .Or => "(or",
                else => "(distinct",
            });
            if (es.len == 0) {
                try w.writeAll(if (e == .And) " true" else " false");
            }
            for (es) |sub| {
                try w.writeByte(' ');
                try writeExpr(w, sub);
            }
            try w.writeByte(')');
        },
        .Not => |inner| {
            try w.writeAll("(not ");
            try writeExpr(w, inner.*);
            try w.writeByte(')');
        },
        .BvNot => |inner| {
            try w.writeAll("(bvnot ");
            try writeExpr(w, inner.*);
            try w.writeByte(')');
        },
        .Implies, .Eq, .Lt, .Le, .Gt, .Ge, .BvAdd, .BvSub, .BvMul => |p| {
            const op = switch (e) {
                .Implies => "=>",
                .Eq => "=",
                .Lt => "bvult",
                .Le => "bvule",
                .Gt => "bvugt",
                .Ge => "bvuge",
                .BvAdd => "bvadd",
                .BvSub => "bvsub",
                .BvMul => "bvmul",
                else => unreachable,
            };
            try w.print("({s} ", .{op});
            try writeExpr(w, p.lhs.*);
            try w.writeByte(' ');
            try writeExpr(w, p.rhs.*);
            try w.writeByte(')');
        },
        .Ite => |i| {
            try w.writeAll("(ite ");
            try writeExpr(w, i.cond.*);
            try w.writeByte(' ');
            try writeExpr(w, i.then.*);
            try w.writeByte(' ');
            try writeExpr(w, i.else_.*);
            try w.writeByte(')');
        },
        .App => |a| {
            try w.print("({s}", .{a.func});
            for (a.args) |sub| {
                try w.writeByte(' ');
                try writeExpr(w, sub);
            }
            try w.writeByte(')');
        },
        .Forall, .Exists => |q| {
            try w.writeAll(if (e == .Forall) "(forall (" else "(exists (");
            for (q.vars, 0..) |v, i| {
                if (i > 0) try w.writeByte(' ');
                try w.print("({s} {s})", .{ v.name, sortToSmt(v.sort) });
            }
            try w.writeAll(") ");
            try writeExpr(w, q.body.*);
            try w.writeByte(')');
        },
    }
}

/// Rust `query_to_smtlib`. The logic is QF_BV as in the source, widened to
/// BV / QF_UFBV / UFBV when quantifiers or uninterpreted symbols occur.
pub fn writeSmtlib(w: *ast.W, q: ast.Z3Query) ast.W.Error!void {
    var quantified = false;
    var uninterpreted = false;
    for (q.commands) |c| switch (c) {
        .Assert => |e| if (hasQuantifier(e.*)) {
            quantified = true;
        },
        .DeclareFun => uninterpreted = true,
        else => {},
    };
    try w.print("(set-logic {s}{s}BV)\n", .{ if (quantified) "" else "QF_", if (uninterpreted) "UF" else "" });
    if (q.context.timeout) |t| try w.print("(set-option :timeout {d})\n", .{t});
    if (q.context.model) try w.writeAll("(set-option :produce-models true)\n");
    if (q.context.unsat_core) try w.writeAll("(set-option :produce-unsat-cores true)\n");
    for (q.commands) |c| switch (c) {
        .DeclareConst => |d| try w.print("(declare-const {s} {s})\n", .{ d.name, sortToSmt(d.sort) }),
        .DeclareFun => |d| {
            try w.print("(declare-fun {s} (", .{d.name});
            for (d.arg_sorts, 0..) |s, i| {
                if (i > 0) try w.writeByte(' ');
                try w.writeAll(sortToSmt(s));
            }
            try w.print(") {s})\n", .{sortToSmt(d.ret_sort)});
        },
        .Assert => |e| {
            try w.writeAll("(assert ");
            try writeExpr(w, e.*);
            try w.writeAll(")\n");
        },
        .CheckSat => try w.writeAll("(check-sat)\n"),
        .GetModel => try w.writeAll("(get-model)\n"),
        .GetUnsatCore => try w.writeAll("(get-unsat-core)\n"),
        .GetProof => try w.writeAll("(get-proof)\n"),
        .Push => |n| try w.print("(push {d})\n", .{n}),
        .Pop => |n| try w.print("(pop {d})\n", .{n}),
    };
}

fn hasQuantifier(e: ast.Z3Expr) bool {
    return switch (e) {
        .Forall, .Exists => true,
        .And, .Or, .Distinct => |es| for (es) |s| {
            if (hasQuantifier(s)) break true;
        } else false,
        .App => |a| for (a.args) |s| {
            if (hasQuantifier(s)) break true;
        } else false,
        .Not, .BvNot => |i| hasQuantifier(i.*),
        .Implies, .Eq, .Lt, .Le, .Gt, .Ge, .BvAdd, .BvSub, .BvMul => |p| hasQuantifier(p.lhs.*) or hasQuantifier(p.rhs.*),
        .Ite => |i| hasQuantifier(i.cond.*) or hasQuantifier(i.then.*) or hasQuantifier(i.else_.*),
        else => false,
    };
}

pub fn smtlibAlloc(arena: std.mem.Allocator, q: ast.Z3Query) ![]u8 {
    var aw: ast.W.Allocating = .init(arena);
    try writeSmtlib(&aw.writer, q);
    return aw.toOwnedSlice();
}

/// Parse z3's reply to `(check-sat)(get-model)`.
pub fn parseZ3Output(arena: std.mem.Allocator, out: []const u8) !CheckResult {
    var lines = std.mem.tokenizeAny(u8, out, "\r\n");
    const first = std.mem.trim(u8, lines.next() orelse return .Unknown, " \t");
    if (std.mem.eql(u8, first, "unsat")) return .Unsat;
    if (std.mem.eql(u8, first, "unknown")) return .Unknown;
    if (std.mem.eql(u8, first, "timeout")) return .Timeout;
    if (!std.mem.eql(u8, first, "sat")) return .Unknown;
    var entries: std.ArrayList(ast.ModelEntry) = .empty;
    const rest = out[@min(out.len, (std.mem.indexOf(u8, out, "sat") orelse 0) + 3)..];
    var i: usize = 0;
    while (std.mem.indexOfPos(u8, rest, i, "(define-fun ")) |p| {
        var j = p + "(define-fun ".len;
        const name_end = std.mem.indexOfAnyPos(u8, rest, j, " \n") orelse break;
        const name = rest[j..name_end];
        j = name_end;
        // Only nullary definitions are model values.
        const after = std.mem.trimStart(u8, rest[j..], " ");
        if (!std.mem.startsWith(u8, after, "()")) {
            i = name_end;
            continue;
        }
        var depth: usize = 0;
        var close = p;
        while (close < rest.len) : (close += 1) {
            if (rest[close] == '(') depth += 1;
            if (rest[close] == ')') {
                depth -= 1;
                if (depth == 0) break;
            }
        }
        if (close >= rest.len) break;
        // Value is the last whitespace-separated token before the closing paren.
        const body = std.mem.trimEnd(u8, rest[j..close], " \t\r\n");
        const sp = std.mem.lastIndexOfAny(u8, body, " \n\t") orelse 0;
        const tok = std.mem.trim(u8, body[sp..], " \t\r\n");
        var value: ast.Term = .{ .Var = try arena.dupe(u8, tok) };
        if (std.mem.startsWith(u8, tok, "#x")) {
            if (std.fmt.parseInt(u64, tok[2..], 16)) |v| value = .{ .Const = .{ .Number = @bitCast(v) } } else |_| {}
        } else if (std.mem.startsWith(u8, tok, "#b")) {
            if (std.fmt.parseInt(u64, tok[2..], 2)) |v| value = .{ .Const = .{ .Number = @bitCast(v) } } else |_| {}
        } else if (std.mem.eql(u8, tok, "true") or std.mem.eql(u8, tok, "false")) {
            value = .{ .Const = .{ .Bool = tok[0] == 't' } };
        }
        try entries.append(arena, .{ .name = try arena.dupe(u8, name), .value = value });
        i = close;
    }
    if (entries.items.len == 0) return .Sat;
    return .{ .Model = try entries.toOwnedSlice(arena) };
}

// ------------------------------------------------------------------- tests

const testing = std.testing;
const parser = @import("parser.zig");

fn emit(a: std.mem.Allocator, src: []const u8) ![]u8 {
    const f = (try parser.parseFormula(a, src)).ok;
    const r = try (Solver{}).buildQuery(a, .S0, f);
    return smtlibAlloc(a, r.query);
}

test "z3: query for x + 1 = 1 + x" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    try testing.expectEqualStrings(
        \\(set-logic QF_BV)
        \\(set-option :produce-models true)
        \\(declare-const x (_ BitVec 32))
        \\(assert (= (bvadd x (_ bv1 32)) (bvadd (_ bv1 32) x)))
        \\(check-sat)
        \\(get-model)
        \\
    , try emit(a, "x + 1 = 1 + x"));
}

test "z3: predicates, quantifiers, functions, fixed points" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const s1 = try emit(a, "x < y ∧ y ≤ 10");
    try testing.expect(std.mem.indexOf(u8, s1, "(and (bvult x y) (bvule y (_ bv10 32)))") != null);
    const s2 = try emit(a, "∀ n : Int. n * 2 = n + n");
    try testing.expect(std.mem.indexOf(u8, s2, "(set-logic BV)") != null);
    try testing.expect(std.mem.indexOf(u8, s2, "declare-const n") == null);
    try testing.expect(std.mem.indexOf(u8, s2, "(forall ((n (_ BitVec 32))) (= (bvmul n (_ bv2 32)) (bvadd n n)))") != null);
    const s3 = try emit(a, "f x = g x y");
    try testing.expect(std.mem.startsWith(u8, s3, "(set-logic QF_UFBV)\n"));
    try testing.expect(std.mem.indexOf(u8, s3, "(declare-fun g ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))") != null);
    const s4 = try emit(a, "mu X. X ∨ P");
    try testing.expect(std.mem.indexOf(u8, s4, "(declare-fun mu_X (Bool) Bool)") != null);
    try testing.expect(std.mem.indexOf(u8, s4, "(assert (mu_X (or X P)))") != null);
}

test "z3: model parsing" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const out = "sat\n(\n  (define-fun y () (_ BitVec 32)\n    #x00000007)\n  (define-fun x () (_ BitVec 32)\n    #x00000003)\n)\n";
    const r = try parseZ3Output(a, out);
    try testing.expectEqual(@as(usize, 2), r.Model.len);
    try testing.expectEqualStrings("y", r.Model[0].name);
    try testing.expectEqual(@as(i64, 7), r.Model[0].value.Const.Number);
    try testing.expect((try parseZ3Output(a, "unsat\n")) == .Unsat);
}
