// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! Constraint search over the domain store (port of search.rs / Crux.Search):
//! first-fail variable selection, value enumeration, depth-limited search.
//! An optional `check` callback rejects partial assignments (the source search
//! never consulted constraints; `crux solve` passes the suspension store here).

const std = @import("std");
const dom = @import("domain.zig");

pub const Strategy = enum { Complete, FirstFail, DomOverDeg, AntiFirstFail };

pub const Assignment = struct { var_: []const u8, val: i64 };

pub const SearchResult = union(enum) {
    Sat: []const Assignment,
    Unsat,
    Unknown,
};

pub const Check = struct {
    ctx: *anyopaque,
    /// false when the current assignment is already inconsistent.
    consistent: *const fn (ctx: *anyopaque, store: *dom.DomainStore) bool,
};

pub fn firstFailSelect(store: *const dom.DomainStore, vars: []const []const u8) ?[]const u8 {
    var best: ?[]const u8 = null;
    var best_size: usize = 0;
    for (vars) |v| {
        const size = store.getDomain(v).size();
        if (size > 1 and (best == null or size < best_size)) {
            best = v;
            best_size = size;
        }
    }
    return best;
}

pub fn indomain(arena: std.mem.Allocator, store: *const dom.DomainStore, v: []const u8) ![]const i64 {
    return switch (store.getDomain(v)) {
        .Range => |r| blk: {
            var out: std.ArrayList(i64) = .empty;
            var x = r.lo;
            while (x <= r.hi) : (x += 1) try out.append(arena, x);
            break :blk out.toOwnedSlice(arena);
        },
        .Set => |vals| vals,
        .Fixed => |f| try arena.dupe(i64, &.{f}),
        .Free => &.{},
    };
}

fn model(store: *const dom.DomainStore) !SearchResult {
    var out: std.ArrayList(Assignment) = .empty;
    for (store.vars()) |v| if (store.getValue(v)) |val| try out.append(store.arena, .{ .var_ = v, .val = val });
    return .{ .Sat = try out.toOwnedSlice(store.arena) };
}

pub fn searchVars(store: *dom.DomainStore, strategy: Strategy, limit: usize, check: ?Check) !SearchResult {
    const vars = try store.arena.dupe([]const u8, store.vars());
    return searchRecursive(store, vars, strategy, limit, check);
}

fn searchRecursive(store: *dom.DomainStore, vars: []const []const u8, strategy: Strategy, limit: usize, check: ?Check) !SearchResult {
    if (limit == 0) return .Unknown;
    if (check) |c| if (!c.consistent(c.ctx, store)) return .Unsat;
    if (vars.len == 0 or store.allFixed()) return model(store);
    const chosen = switch (strategy) {
        .FirstFail, .Complete, .DomOverDeg => firstFailSelect(store, vars),
        .AntiFirstFail => vars[0],
    } orelse return model(store);
    const values = try indomain(store.arena, store, chosen);
    const old = store.getDomain(chosen);
    var remaining: std.ArrayList([]const u8) = .empty;
    for (vars) |v| if (!std.mem.eql(u8, v, chosen)) try remaining.append(store.arena, v);
    var saw_unknown = false;
    for (values) |val| {
        try store.setValue(chosen, val);
        const r = try searchRecursive(store, remaining.items, strategy, limit - 1, check);
        switch (r) {
            .Sat => return r,
            .Unknown => saw_unknown = true,
            .Unsat => {},
        }
        try store.restore(chosen, old);
    }
    return if (saw_unknown) .Unknown else .Unsat;
}

/// Source `minimize_cost`: search, then sum the cost variables of the model.
pub fn minimizeCost(store: *dom.DomainStore, cost_vars: []const []const u8, strategy: Strategy, limit: usize) !struct { result: SearchResult, cost: i64 } {
    const r = try searchVars(store, strategy, limit, null);
    var cost: i64 = 0;
    if (r == .Sat) for (cost_vars) |cv| for (r.Sat) |a| if (std.mem.eql(u8, a.var_, cv)) {
        cost += a.val;
    };
    return .{ .result = r, .cost = cost };
}

const testing = std.testing;

test "search: first fail" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    var s = dom.DomainStore.init(st.allocator());
    try s.setDomain("x", dom.Domain.range(1, 100));
    try s.setDomain("y", .{ .Set = &.{ 1, 2, 3 } });
    try s.setDomain("z", .{ .Fixed = 5 });
    try testing.expectEqualStrings("y", firstFailSelect(&s, &.{ "x", "y", "z" }).?);
}

test "search: simple and fixed" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    var s = dom.DomainStore.init(st.allocator());
    try s.setDomain("x", dom.Domain.range(1, 3));
    const r = try searchVars(&s, .Complete, 100, null);
    try testing.expect(r == .Sat and r.Sat.len > 0);
    var s2 = dom.DomainStore.init(st.allocator());
    try s2.setDomain("x", .{ .Fixed = 1 });
    const r2 = try searchVars(&s2, .Complete, 100, null);
    try testing.expectEqual(@as(i64, 1), r2.Sat[0].val);
}
