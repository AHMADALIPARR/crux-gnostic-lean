// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! Constraint evaluation over the domain store (port of arithmetic.rs, formerly
//! constraint.rs, and Crux.Arithmetic).
//!
//! The source file ends inside the `Lt` arm (its last line is
//! `match dom_b.min()`), and the Lean port returns Unknown for every arm after
//! `Neq`. The arms are completed here with bounds reasoning that agrees with
//! both: fixed values decide exactly (the part of `Lt` the source has), and
//! otherwise a relation is Entailed or Failed only when the domain bounds
//! force it, else Unknown (so the Lean theorem `eval_constraint_lt_unknown`
//! still holds). `Linear` is decided once every variable is fixed; `Reified`
//! stays Unknown.

const std = @import("std");
const dom = @import("domain.zig");

pub const Constraint = union(enum) {
    Eq: struct { var_: []const u8, val: i64 },
    Neq: struct { var_: []const u8, val: i64 },
    Lt: Pair,
    Le: Pair,
    Gt: Pair,
    Ge: Pair,
    Linear: struct { terms: []const LinTerm, rhs: i64 },
    Reified: struct { c: *const Constraint, name: []const u8 },

    pub const Pair = struct { a: []const u8, b: []const u8 };
    pub const LinTerm = struct { var_: []const u8, coef: i64 };

    pub fn eq(v: []const u8, val: i64) Constraint {
        return .{ .Eq = .{ .var_ = v, .val = val } };
    }
    pub fn neq(v: []const u8, val: i64) Constraint {
        return .{ .Neq = .{ .var_ = v, .val = val } };
    }
    pub fn lt(a: []const u8, b: []const u8) Constraint {
        return .{ .Lt = .{ .a = a, .b = b } };
    }
    pub fn le(a: []const u8, b: []const u8) Constraint {
        return .{ .Le = .{ .a = a, .b = b } };
    }
    pub fn gt(a: []const u8, b: []const u8) Constraint {
        return .{ .Gt = .{ .a = a, .b = b } };
    }
    pub fn ge(a: []const u8, b: []const u8) Constraint {
        return .{ .Ge = .{ .a = a, .b = b } };
    }
};

pub const EvalResult = enum { Entailed, Failed, Unknown };

/// Bounds of a variable: its fixed value, else its domain's min/max.
fn bounds(store: *const dom.DomainStore, v: []const u8) struct { ?i64, ?i64 } {
    if (store.getValue(v)) |x| return .{ x, x };
    return store.getBounds(v);
}

/// a < b (strict) or a <= b, decided from bounds.
fn less(store: *const dom.DomainStore, a: []const u8, b: []const u8, strict: bool) EvalResult {
    const va = store.getValue(a);
    const vb = store.getValue(b);
    if (va != null and vb != null) {
        const holds = if (strict) va.? < vb.? else va.? <= vb.?;
        return if (holds) .Entailed else .Failed;
    }
    const amin, const amax = bounds(store, a);
    const bmin, const bmax = bounds(store, b);
    if (amax != null and bmin != null) {
        if (if (strict) amax.? < bmin.? else amax.? <= bmin.?) return .Entailed;
    }
    if (amin != null and bmax != null) {
        if (if (strict) amin.? >= bmax.? else amin.? > bmax.?) return .Failed;
    }
    return .Unknown;
}

pub fn evalConstraint(c: Constraint, store: *const dom.DomainStore) EvalResult {
    return switch (c) {
        .Eq => |e| if (store.getValue(e.var_)) |v|
            (if (v == e.val) .Entailed else .Failed)
        else if (!store.getDomain(e.var_).contains(e.val)) .Failed else .Unknown,
        .Neq => |e| if (store.getValue(e.var_)) |v|
            (if (v != e.val) .Entailed else .Failed)
        else if (store.getDomain(e.var_).eql(.{ .Fixed = e.val })) .Failed else .Unknown,
        .Lt => |p| less(store, p.a, p.b, true),
        .Le => |p| less(store, p.a, p.b, false),
        .Gt => |p| less(store, p.b, p.a, true),
        .Ge => |p| less(store, p.b, p.a, false),
        .Linear => |l| blk: {
            var sum: i64 = 0;
            for (l.terms) |t| {
                const v = store.getValue(t.var_) orelse break :blk .Unknown;
                sum = std.math.add(i64, sum, std.math.mul(i64, t.coef, v) catch break :blk .Unknown) catch break :blk .Unknown;
            }
            break :blk if (sum == l.rhs) .Entailed else .Failed;
        },
        .Reified => .Unknown,
    };
}

const testing = std.testing;

test "arithmetic: Eq/Neq arms (Lean port theorems)" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    var s = dom.DomainStore.init(st.allocator());
    try s.setValue("x", 5);
    try testing.expectEqual(EvalResult.Entailed, evalConstraint(Constraint.eq("x", 5), &s));
    try s.setValue("x", 6);
    try testing.expectEqual(EvalResult.Failed, evalConstraint(Constraint.eq("x", 5), &s));
    try testing.expectEqual(EvalResult.Entailed, evalConstraint(Constraint.neq("x", 5), &s));
}

test "arithmetic: completed Lt arm" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    var s = dom.DomainStore.init(st.allocator());
    try s.setDomain("x", dom.Domain.range(1, 10));
    try s.setDomain("y", dom.Domain.range(1, 10));
    // Lean theorem eval_constraint_lt_unknown.
    try testing.expectEqual(EvalResult.Unknown, evalConstraint(Constraint.lt("x", "y"), &s));
    try s.setValue("x", 0);
    try testing.expectEqual(EvalResult.Entailed, evalConstraint(Constraint.lt("x", "y"), &s));
    try s.setValue("x", 10);
    try testing.expectEqual(EvalResult.Failed, evalConstraint(Constraint.lt("x", "y"), &s));
    try testing.expectEqual(EvalResult.Unknown, evalConstraint(Constraint.le("x", "y"), &s));
    try s.setValue("y", 10);
    try testing.expectEqual(EvalResult.Entailed, evalConstraint(Constraint.ge("x", "y"), &s));
    const lin: Constraint = .{ .Linear = .{ .terms = &.{ .{ .var_ = "x", .coef = 2 }, .{ .var_ = "y", .coef = -1 } }, .rhs = 10 } };
    try testing.expectEqual(EvalResult.Entailed, evalConstraint(lin, &s));
}
