// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! Suspended constraints and propagation (port of suspension.rs / Crux.Suspension).

const std = @import("std");
const dom = @import("domain.zig");
const arith = @import("arithmetic.zig");

pub const Entry = struct {
    id: usize,
    constraint: arith.Constraint,
    priority: i32,
    watch_vars: []const []const u8,
    fired: bool,
    outcome: arith.EvalResult = .Unknown,
};

pub const SuspensionStore = struct {
    arena: std.mem.Allocator,
    entries: std.ArrayList(Entry) = .empty,
    next_id: usize = 0,

    pub fn init(arena: std.mem.Allocator) SuspensionStore {
        return .{ .arena = arena };
    }

    pub fn suspendGoal(self: *SuspensionStore, c: arith.Constraint, priority: i32, watch_vars: []const []const u8) !usize {
        const id = self.next_id;
        self.next_id += 1;
        try self.entries.append(self.arena, .{ .id = id, .constraint = c, .priority = priority, .watch_vars = watch_vars, .fired = false });
        return id;
    }

    /// Re-evaluate constraints watching `v`; those that become decided fire.
    pub fn wake(self: *SuspensionStore, v: []const u8, store: *const dom.DomainStore) ![]const usize {
        var fired: std.ArrayList(usize) = .empty;
        for (self.entries.items) |*e| {
            if (e.fired) continue;
            for (e.watch_vars) |w| if (std.mem.eql(u8, w, v)) {
                const r = arith.evalConstraint(e.constraint, store);
                if (r != .Unknown) {
                    e.fired = true;
                    e.outcome = r;
                    try fired.append(self.arena, e.id);
                }
                break;
            };
        }
        return fired.toOwnedSlice(self.arena);
    }

    pub fn activeCount(self: *const SuspensionStore) usize {
        var n: usize = 0;
        for (self.entries.items) |e| if (!e.fired) {
            n += 1;
        };
        return n;
    }

    pub fn anyFailed(self: *const SuspensionStore) bool {
        for (self.entries.items) |e| if (e.fired and e.outcome == .Failed) return true;
        return false;
    }

    pub fn clear(self: *SuspensionStore) void {
        self.entries.clearRetainingCapacity();
        self.next_id = 0;
    }
};

pub fn propagateStore(susp: *SuspensionStore, store: *const dom.DomainStore) !void {
    while (true) {
        var any = false;
        for (store.vars()) |v| {
            if ((try susp.wake(v, store)).len > 0) any = true;
        }
        if (!any) break;
    }
}

const testing = std.testing;

test "suspension: suspend and wake" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    var ss = SuspensionStore.init(a);
    var ds = dom.DomainStore.init(a);
    try ds.setDomain("x", dom.Domain.range(1, 10));
    const id = try ss.suspendGoal(arith.Constraint.eq("x", 5), 1, &.{"x"});
    try testing.expectEqual(@as(usize, 1), ss.activeCount());
    try ds.setValue("x", 5);
    const fired = try ss.wake("x", &ds);
    try testing.expect(std.mem.indexOfScalar(usize, fired, id) != null);
    try testing.expectEqual(@as(usize, 0), ss.activeCount());
}

test "suspension: propagate" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    var ss = SuspensionStore.init(a);
    var ds = dom.DomainStore.init(a);
    try ds.setDomain("x", dom.Domain.range(1, 10));
    try ds.setDomain("y", dom.Domain.range(1, 10));
    _ = try ss.suspendGoal(arith.Constraint.eq("x", 3), 1, &.{"x"});
    _ = try ss.suspendGoal(arith.Constraint.lt("x", "y"), 2, &.{ "x", "y" });
    try ds.setValue("x", 3);
    try propagateStore(&ss, &ds);
    try testing.expect(ss.activeCount() <= 1);
}
