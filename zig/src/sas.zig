// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! SAS backend: interval abstract interpretation (port of sas_backend.rs /
//! Crux.SasBackend). The transfer function is the identity and widening jumps
//! to i64 min/max, as in the source. Interval arithmetic saturates at the i64
//! bounds (the source used plain i64 operators, which overflow).

const std = @import("std");
const ast = @import("ast.zig");

pub const Result = union(enum) {
    Proved,
    Alarm: struct { location: []const u8, formula: ast.Formula },
    Unknown,
};

pub const Trace = struct {
    iterations: u32,
    fixpoint: bool,
    final_state: ast.SASState,
};

pub const Analyzer = struct {
    default_config: ast.SASConfig = .{},

    pub fn buildQuery(self: Analyzer, arena: std.mem.Allocator, state: ast.State, f: ast.Formula) !ast.SASQuery {
        return .{ .config = self.default_config, .state = try abstractState(arena, state), .property = .{ .Safe = f } };
    }

    pub fn analyze(self: Analyzer, arena: std.mem.Allocator, q: ast.SASQuery, trace: ?*Trace) !Result {
        _ = self;
        var current = q.state;
        var iterations: u32 = 0;
        const max_iter = q.config.loop_bound;
        while (true) {
            iterations += 1;
            if (iterations > max_iter) {
                if (trace) |t| t.* = .{ .iterations = iterations - 1, .fixpoint = false, .final_state = current };
                return .Unknown;
            }
            const next = transfer(current, q.property);
            if (leq(next, current)) {
                if (trace) |t| t.* = .{ .iterations = iterations, .fixpoint = true, .final_state = next };
                if (satisfies(next, q.property)) return .Proved;
                return .{ .Alarm = .{ .location = "fixpoint", .formula = extractViolation(q.property) } };
            }
            current = try widen(arena, current, next);
        }
    }
};

pub fn abstractState(arena: std.mem.Allocator, state: ast.State) !ast.SASState {
    return switch (state) {
        .S, .S0 => .{ .bindings = &.{} },
        .Sn => |n| .{ .bindings = try arena.dupe(ast.AbsBinding, &.{.{ .name = "iter", .val = .{ .Interval = .{ .low = 0, .high = n } } }}) },
        .Update => |u| .{ .bindings = try arena.dupe(ast.AbsBinding, &.{.{ .name = u.var_, .val = abstractTerm(u.value) }}) },
        .Prime => |inner| abstractState(arena, inner.*),
        .Bind => |b| blk: {
            const base = try abstractState(arena, b.base.*);
            const out = try arena.alloc(ast.AbsBinding, base.bindings.len + 1);
            @memcpy(out[0..base.bindings.len], base.bindings);
            out[base.bindings.len] = .{ .name = b.binding.var_, .val = abstractTerm(b.binding.value) };
            break :blk .{ .bindings = out };
        },
        .Recursive => |r| .{ .bindings = try arena.dupe(ast.AbsBinding, &.{.{ .name = r.var_, .val = .Top }}) },
    };
}

pub fn abstractTerm(t: ast.Term) ast.AbsVal {
    return switch (t) {
        .Const => |lit| switch (lit) {
            .Number => |n| .{ .Interval = .{ .low = n, .high = n } },
            .Bool => |b| if (b) .{ .Interval = .{ .low = 1, .high = 1 } } else .{ .Interval = .{ .low = 0, .high = 0 } },
            else => .Top,
        },
        .Var => .Top,
        .BinOp => |b| evalBinop(b.op, abstractTerm(b.lhs.*), abstractTerm(b.rhs.*)),
        .IfThenElse => |i| join(abstractTerm(i.then.*), abstractTerm(i.else_.*)),
        else => .Top,
    };
}

pub fn evalBinop(op: ast.BinOp, l: ast.AbsVal, r: ast.AbsVal) ast.AbsVal {
    switch (op) {
        .Lt, .Le, .Gt, .Ge, .Eq, .Ne => return .{ .Interval = .{ .low = 0, .high = 1 } },
        else => {},
    }
    if (l != .Interval or r != .Interval) return .Top;
    const ll = l.Interval.low;
    const lh = l.Interval.high;
    const rl = r.Interval.low;
    const rh = r.Interval.high;
    return switch (op) {
        .Add => .{ .Interval = .{ .low = ll +| rl, .high = lh +| rh } },
        .Sub => .{ .Interval = .{ .low = ll -| rh, .high = lh -| rl } },
        .Mul => blk: {
            const vals = [_]i64{ ll *| rl, ll *| rh, lh *| rl, lh *| rh };
            break :blk .{ .Interval = .{ .low = std.mem.min(i64, &vals), .high = std.mem.max(i64, &vals) } };
        },
        else => .Top,
    };
}

/// Identity transfer, as in the source.
pub fn transfer(state: ast.SASState, prop: ast.SASProperty) ast.SASState {
    _ = prop;
    return state;
}

fn find(state: ast.SASState, name: []const u8) ?ast.AbsVal {
    for (state.bindings) |b| if (std.mem.eql(u8, b.name, name)) return b.val;
    return null;
}

pub fn leq(a: ast.SASState, b: ast.SASState) bool {
    for (a.bindings) |ab| {
        const bval = find(b, ab.name) orelse return false;
        if (!subsumes(bval, ab.val)) return false;
    }
    return true;
}

pub fn subsumes(larger: ast.AbsVal, smaller: ast.AbsVal) bool {
    if (larger == .Top) return true;
    if (smaller == .Bottom) return true;
    if (larger == .Interval and smaller == .Interval)
        return larger.Interval.low <= smaller.Interval.low and larger.Interval.high >= smaller.Interval.high;
    return std.meta.activeTag(larger) == std.meta.activeTag(smaller);
}

pub fn satisfies(state: ast.SASState, prop: ast.SASProperty) bool {
    return switch (prop) {
        .Safe, .Invariant => |f| evalFormulaInState(f, state),
        else => true,
    };
}

pub fn evalFormulaInState(f: ast.Formula, state: ast.SASState) bool {
    return switch (f) {
        .Atomic => |a| switch (a) {
            .True => true,
            .False => false,
            else => true,
        },
        .Not => |inner| !evalFormulaInState(inner.*, state),
        .And => |fs| for (fs) |sub| {
            if (!evalFormulaInState(sub, state)) break false;
        } else true,
        .Or => |fs| for (fs) |sub| {
            if (evalFormulaInState(sub, state)) break true;
        } else false,
        .Eq => |e| blk: {
            if (e.lhs != .Var) break :blk true;
            if (e.rhs == .Var and std.mem.eql(u8, e.lhs.Var, e.rhs.Var)) break :blk true;
            const aval = find(state, e.lhs.Var) orelse break :blk true;
            break :blk subsumes(aval, abstractTerm(e.rhs));
        },
        .Paren => |inner| evalFormulaInState(inner.*, state),
        else => true,
    };
}

pub fn join(a: ast.AbsVal, b: ast.AbsVal) ast.AbsVal {
    if (a == .Top or b == .Top) return .Top;
    if (a == .Bottom) return b;
    if (b == .Bottom) return a;
    if (a == .Interval and b == .Interval)
        return .{ .Interval = .{ .low = @min(a.Interval.low, b.Interval.low), .high = @max(a.Interval.high, b.Interval.high) } };
    return .Top;
}

pub fn widen(arena: std.mem.Allocator, a: ast.SASState, b: ast.SASState) !ast.SASState {
    var out: std.ArrayList(ast.AbsBinding) = .empty;
    try out.appendSlice(arena, a.bindings);
    outer: for (b.bindings) |bb| {
        for (out.items) |*ab| if (std.mem.eql(u8, ab.name, bb.name)) {
            ab.val = widenVals(ab.val, bb.val);
            continue :outer;
        };
        try out.append(arena, bb);
    }
    return .{ .bindings = try out.toOwnedSlice(arena) };
}

pub fn widenVals(a: ast.AbsVal, b: ast.AbsVal) ast.AbsVal {
    if (a == .Interval and b == .Interval) {
        const low = if (b.Interval.low < a.Interval.low) std.math.minInt(i64) else b.Interval.low;
        const high = if (b.Interval.high > a.Interval.high) std.math.maxInt(i64) else b.Interval.high;
        return .{ .Interval = .{ .low = low, .high = high } };
    }
    return .Top;
}

pub fn extractViolation(prop: ast.SASProperty) ast.Formula {
    return switch (prop) {
        .Safe, .Assertion => |f| f,
        else => ast.true_formula,
    };
}

pub fn writeAbsVal(w: *ast.W, v: ast.AbsVal) ast.W.Error!void {
    switch (v) {
        .Interval => |i| try w.print("[{d}, {d}]", .{ i.low, i.high }),
        .Top => try w.writeAll("⊤"),
        .Bottom => try w.writeAll("⊥"),
        .PointsTo => |p| try w.print("→{s}", .{p}),
        .Null => try w.writeAll("null"),
        .Dangling => try w.writeAll("dangling"),
    }
}

pub fn writeState(w: *ast.W, s: ast.SASState) ast.W.Error!void {
    try w.writeAll("{");
    for (s.bindings, 0..) |b, i| {
        try w.writeAll(if (i == 0) " " else ", ");
        try w.print("{s} ∈ ", .{b.name});
        try writeAbsVal(w, b.val);
    }
    try w.writeAll(if (s.bindings.len == 0) "}" else " }");
}

pub fn resultName(r: Result) []const u8 {
    return switch (r) {
        .Proved => "PROVED",
        .Alarm => "ALARM",
        .Unknown => "UNKNOWN",
    };
}

/// The SAS analysis report written by `crux emit-sas`.
pub fn writeReport(w: *ast.W, name: []const u8, q: ast.SASQuery, r: Result, t: Trace) ast.W.Error!void {
    try w.print("query {s}\n", .{name});
    try w.print("  config: domain={s} widening={s} narrowing={d} threshold={d} loop_bound={d}\n", .{
        @tagName(q.config.domain), @tagName(q.config.widening), q.config.narrowing, q.config.threshold, q.config.loop_bound,
    });
    try w.writeAll("  initial: ");
    try writeState(w, q.state);
    try w.writeAll("\n  property: Safe(");
    try ast.dump(w, q.property.Safe);
    try w.writeAll(")\n");
    try w.print("  iterations: {d} ({s})\n  final: ", .{ t.iterations, if (t.fixpoint) "fixpoint" else "loop bound reached" });
    try writeState(w, t.final_state);
    try w.print("\n  result: {s}", .{resultName(r)});
    if (r == .Alarm) try w.print(" at {s}", .{r.Alarm.location});
    try w.writeAll("\n");
}

// ------------------------------------------------------------------- tests

const testing = std.testing;
const parser = @import("parser.zig");

test "sas: interval arithmetic and lattice operations" {
    const i = struct {
        fn iv(l: i64, h: i64) ast.AbsVal {
            return .{ .Interval = .{ .low = l, .high = h } };
        }
    }.iv;
    try testing.expectEqual(i(3, 7), evalBinop(.Add, i(1, 2), i(2, 5)));
    try testing.expectEqual(i(-4, 0), evalBinop(.Sub, i(1, 2), i(2, 5)));
    try testing.expectEqual(i(-10, 15), evalBinop(.Mul, i(-2, 3), i(1, 5)));
    try testing.expectEqual(i(std.math.maxInt(i64), std.math.maxInt(i64)), evalBinop(.Add, i(std.math.maxInt(i64), std.math.maxInt(i64)), i(1, 1)));
    try testing.expect(subsumes(i(0, 10), i(2, 3)));
    try testing.expect(!subsumes(i(2, 3), i(0, 10)));
    try testing.expect(subsumes(.Top, i(0, 1)));
    try testing.expectEqual(i(0, 9), join(i(0, 3), i(5, 9)));
    try testing.expectEqual(i(std.math.minInt(i64), std.math.maxInt(i64)), widenVals(i(0, 3), i(-1, 4)));
}

test "sas: analysis results" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const an: Analyzer = .{};
    // x bound to 2 + 3 = [5,5]; property x = 5 holds, x = 6 raises an alarm.
    const p = (try parser.parseProgram(a, "сила(S1[x := 2 + 3], x = 5); сила(S1[x := 2 + 3], x = 6); сила(S0, false)")).ok;
    var results: [3]Result = undefined;
    for (p, 0..) |item, k| {
        const s = item.form.Sila;
        const q = try an.buildQuery(a, s.state, s.formula);
        var t: Trace = undefined;
        results[k] = try an.analyze(a, q, &t);
        try testing.expectEqual(@as(u32, 1), t.iterations);
    }
    try testing.expect(results[0] == .Proved);
    try testing.expect(results[1] == .Alarm);
    try testing.expect(results[2] == .Alarm);
    const q = try an.buildQuery(a, (try parser.parseRussian(a, "сила(S1[x := 2 + 3], x = 5)")).ok.Sila.state, ast.true_formula);
    try testing.expectEqual(@as(usize, 2), q.state.bindings.len);
    try testing.expectEqualStrings("iter", q.state.bindings[0].name);
}
