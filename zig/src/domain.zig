// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! Constraint domains and the domain store (port of domain.rs / Crux.Domain).
//! The store keeps insertion order (the source used a HashMap).

const std = @import("std");

pub const Domain = union(enum) {
    Range: struct { lo: i64, hi: i64 },
    Set: []const i64,
    Fixed: i64,
    Free,

    pub fn range(lo: i64, hi: i64) Domain {
        return .{ .Range = .{ .lo = lo, .hi = hi } };
    }

    pub fn size(self: Domain) usize {
        return switch (self) {
            .Range => |r| if (r.hi < r.lo) 0 else @intCast(@as(i128, r.hi) - r.lo + 1),
            .Set => |v| v.len,
            .Fixed => 1,
            .Free => 0,
        };
    }

    pub fn contains(self: Domain, val: i64) bool {
        return switch (self) {
            .Range => |r| val >= r.lo and val <= r.hi,
            .Set => |v| std.mem.indexOfScalar(i64, v, val) != null,
            .Fixed => |f| f == val,
            .Free => true,
        };
    }

    pub fn eql(a: Domain, b: Domain) bool {
        if (std.meta.activeTag(a) != std.meta.activeTag(b)) return false;
        return switch (a) {
            .Range => |r| r.lo == b.Range.lo and r.hi == b.Range.hi,
            .Set => |v| std.mem.eql(i64, v, b.Set),
            .Fixed => |f| f == b.Fixed,
            .Free => true,
        };
    }

    pub fn intersect(self: Domain, arena: std.mem.Allocator, other: Domain) !?Domain {
        switch (self) {
            .Range => |a| switch (other) {
                .Range => |b| {
                    const lo = @max(a.lo, b.lo);
                    const hi = @min(a.hi, b.hi);
                    return if (lo <= hi) range(lo, hi) else null;
                },
                .Set => |vals| return filterSet(arena, vals, self),
                .Fixed => |v| return if (self.contains(v)) Domain{ .Fixed = v } else null,
                .Free => return null,
            },
            .Set => |vals| switch (other) {
                .Range, .Set => return filterSet(arena, vals, other),
                .Fixed => |v| return if (self.contains(v)) Domain{ .Fixed = v } else null,
                .Free => return null,
            },
            .Fixed => |v| return if (other.contains(v)) Domain{ .Fixed = v } else null,
            .Free => return switch (other) {
                .Fixed => |v| Domain{ .Fixed = v },
                else => null,
            },
        }
    }

    fn filterSet(arena: std.mem.Allocator, vals: []const i64, keep: Domain) !?Domain {
        var out: std.ArrayList(i64) = .empty;
        for (vals) |v| if (keep.contains(v)) try out.append(arena, v);
        if (out.items.len == 0) return null;
        return .{ .Set = try out.toOwnedSlice(arena) };
    }

    pub fn remove(self: Domain, arena: std.mem.Allocator, val: i64) !?Domain {
        switch (self) {
            .Range => |r| {
                if (val < r.lo or val > r.hi) return self;
                if (r.lo == r.hi) return null;
                if (val == r.lo) return range(r.lo + 1, r.hi);
                if (val == r.hi) return range(r.lo, r.hi - 1);
                var out: std.ArrayList(i64) = .empty;
                var v = r.lo;
                while (v <= r.hi) : (v += 1) if (v != val) try out.append(arena, v);
                return .{ .Set = try out.toOwnedSlice(arena) };
            },
            .Set => |vals| {
                var out: std.ArrayList(i64) = .empty;
                for (vals) |v| if (v != val) try out.append(arena, v);
                if (out.items.len == 0) return null;
                return .{ .Set = try out.toOwnedSlice(arena) };
            },
            .Fixed => |f| return if (f == val) null else self,
            .Free => return self,
        }
    }

    pub fn min(self: Domain) ?i64 {
        return switch (self) {
            .Range => |r| r.lo,
            .Set => |v| if (v.len == 0) null else std.mem.min(i64, v),
            .Fixed => |f| f,
            .Free => null,
        };
    }

    pub fn max(self: Domain) ?i64 {
        return switch (self) {
            .Range => |r| r.hi,
            .Set => |v| if (v.len == 0) null else std.mem.max(i64, v),
            .Fixed => |f| f,
            .Free => null,
        };
    }
};

pub const DomainStore = struct {
    arena: std.mem.Allocator,
    domains: std.StringArrayHashMapUnmanaged(Domain) = .empty,
    values: std.StringArrayHashMapUnmanaged(i64) = .empty,

    pub fn init(arena: std.mem.Allocator) DomainStore {
        return .{ .arena = arena };
    }

    pub fn setDomain(self: *DomainStore, v: []const u8, dom: Domain) !void {
        if (dom == .Fixed) try self.values.put(self.arena, v, dom.Fixed);
        try self.domains.put(self.arena, v, dom);
    }
    pub fn getDomain(self: *const DomainStore, v: []const u8) Domain {
        return self.domains.get(v) orelse .Free;
    }
    pub fn getValue(self: *const DomainStore, v: []const u8) ?i64 {
        return self.values.get(v);
    }
    pub fn setValue(self: *DomainStore, v: []const u8, val: i64) !void {
        try self.values.put(self.arena, v, val);
        try self.domains.put(self.arena, v, .{ .Fixed = val });
    }
    /// Restore a domain saved before `setValue` (search backtracking).
    pub fn restore(self: *DomainStore, v: []const u8, dom: Domain) !void {
        if (dom != .Fixed) _ = self.values.swapRemove(v);
        try self.setDomain(v, dom);
    }
    pub fn getBounds(self: *const DomainStore, v: []const u8) struct { ?i64, ?i64 } {
        const d = self.getDomain(v);
        return .{ d.min(), d.max() };
    }
    pub fn vars(self: *const DomainStore) []const []const u8 {
        return self.domains.keys();
    }
    pub fn anyEmpty(self: *const DomainStore) bool {
        for (self.domains.values()) |d| if (d == .Free) return true;
        return false;
    }
    pub fn allFixed(self: *const DomainStore) bool {
        for (self.domains.values()) |d| if (d != .Fixed) return false;
        return true;
    }
    /// No-op, as in the source.
    pub fn resetStatuses(self: *DomainStore) void {
        _ = self;
    }
};

const testing = std.testing;

test "domain: range" {
    const d = Domain.range(1, 10);
    try testing.expectEqual(@as(usize, 10), d.size());
    try testing.expect(d.contains(5));
    try testing.expect(!d.contains(11));
}

test "domain: intersect" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const r = (try Domain.range(1, 5).intersect(st.allocator(), Domain.range(3, 8))).?;
    try testing.expect(r.eql(Domain.range(3, 5)));
}

test "domain: remove" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const d = Domain.range(1, 3);
    try testing.expect((try d.remove(a, 2)).?.eql(.{ .Set = &.{ 1, 3 } }));
    try testing.expect((try d.remove(a, 1)).?.eql(Domain.range(2, 3)));
    try testing.expect((try d.remove(a, 4)).?.eql(Domain.range(1, 3)));
}

test "domain: store" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    var store = DomainStore.init(st.allocator());
    try store.setDomain("x", Domain.range(1, 10));
    try testing.expect(store.getDomain("x").eql(Domain.range(1, 10)));
    try store.setValue("x", 5);
    try testing.expectEqual(@as(?i64, 5), store.getValue("x"));
    try testing.expect(store.getDomain("x").eql(.{ .Fixed = 5 }));
}
