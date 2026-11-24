// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! SAS -> CUDA lowering. Each SAS query becomes CUDA C: the abstract state is
//! an array of intervals in device memory, one thread per binding runs the
//! transfer / inclusion test and the widening step, and a per-query device
//! function evaluates the property at the fixpoint. The host loop is the SAS
//! fixpoint iteration (`loop_bound` rounds), so the program prints the same
//! PROVED / ALARM / UNKNOWN verdicts as `crux emit-sas`.
//!
//! Without nvcc (`__CUDACC__` undefined) the same file compiles as C++: the
//! kernels run as host loops over `threadIdx.x`.

const std = @import("std");
const ast = @import("ast.zig");
const sas = @import("sas.zig");

pub const Query = struct {
    name: []const u8,
    query: ast.SASQuery,
};

const header =
    \\#include <stdio.h>
    \\#include <stdint.h>
    \\#include <stdlib.h>
    \\
    \\#ifdef __CUDACC__
    \\#define CRUX_HD __host__ __device__
    \\#define CRUX_LAUNCH(kernel, n, ...) do { kernel<<<1, (n)>>>(__VA_ARGS__); cudaDeviceSynchronize(); } while (0)
    \\#define CRUX_ALLOC(ptr, bytes) cudaMallocManaged((void **)&(ptr), (bytes))
    \\#define CRUX_FREE(ptr) cudaFree(ptr)
    \\#else
    \\/* Host build: kernels run as loops over threadIdx.x. */
    \\#define __global__
    \\#define CRUX_HD
    \\struct crux_dim3 { unsigned x; };
    \\static crux_dim3 threadIdx;
    \\#define CRUX_LAUNCH(kernel, n, ...) do { for (threadIdx.x = 0; threadIdx.x < (unsigned)(n); ++threadIdx.x) kernel(__VA_ARGS__); } while (0)
    \\#define CRUX_ALLOC(ptr, bytes) ((ptr) = (decltype(ptr))malloc(bytes))
    \\#define CRUX_FREE(ptr) free(ptr)
    \\#endif
    \\
    \\enum { CRUX_INTERVAL = 0, CRUX_TOP = 1, CRUX_BOTTOM = 2, CRUX_POINTS_TO = 3, CRUX_NULL = 4, CRUX_DANGLING = 5 };
    \\enum { CRUX_PROVED = 0, CRUX_ALARM = 1, CRUX_UNKNOWN = 2 };
    \\
    \\struct CruxAbsVal {
    \\    int kind;
    \\    long long low;
    \\    long long high;
    \\};
    \\
    \\#define CRUX_I64_MIN (-9223372036854775807LL - 1)
    \\#define CRUX_I64_MAX 9223372036854775807LL
    \\
    \\/* larger ⊒ smaller */
    \\CRUX_HD static inline bool crux_subsumes(CruxAbsVal larger, CruxAbsVal smaller) {
    \\    if (larger.kind == CRUX_TOP) return true;
    \\    if (smaller.kind == CRUX_BOTTOM) return true;
    \\    if (larger.kind == CRUX_INTERVAL && smaller.kind == CRUX_INTERVAL)
    \\        return larger.low <= smaller.low && larger.high >= smaller.high;
    \\    return larger.kind == smaller.kind;
    \\}
    \\
    \\/* Interval widening to the i64 bounds. */
    \\CRUX_HD static inline CruxAbsVal crux_widen(CruxAbsVal a, CruxAbsVal b) {
    \\    CruxAbsVal r;
    \\    if (a.kind == CRUX_INTERVAL && b.kind == CRUX_INTERVAL) {
    \\        r.kind = CRUX_INTERVAL;
    \\        r.low = b.low < a.low ? CRUX_I64_MIN : b.low;
    \\        r.high = b.high > a.high ? CRUX_I64_MAX : b.high;
    \\    } else {
    \\        r.kind = CRUX_TOP;
    \\        r.low = 0;
    \\        r.high = 0;
    \\    }
    \\    return r;
    \\}
    \\
    \\/* Identity transfer function, as in the SAS backend. */
    \\CRUX_HD static inline CruxAbsVal crux_transfer(CruxAbsVal v) { return v; }
    \\
    \\/* next = transfer(cur); not_leq is set when next ⋢ cur. One thread per binding. */
    \\__global__ void crux_sas_step(const CruxAbsVal *cur, CruxAbsVal *next, int n, int *not_leq) {
    \\    int i = (int)threadIdx.x;
    \\    if (i >= n) return;
    \\    next[i] = crux_transfer(cur[i]);
    \\    if (!crux_subsumes(cur[i], next[i])) *not_leq = 1;
    \\}
    \\
    \\/* cur = widen(cur, next). One thread per binding. */
    \\__global__ void crux_sas_widen(CruxAbsVal *cur, const CruxAbsVal *next, int n) {
    \\    int i = (int)threadIdx.x;
    \\    if (i >= n) return;
    \\    cur[i] = crux_widen(cur[i], next[i]);
    \\}
    \\
    \\static const char *crux_verdict(int r) {
    \\    return r == CRUX_PROVED ? "PROVED" : (r == CRUX_ALARM ? "ALARM" : "UNKNOWN");
    \\}
    \\
    \\
;

fn writeI64(w: *ast.W, v: i64) ast.W.Error!void {
    if (v == std.math.minInt(i64)) return w.writeAll("CRUX_I64_MIN");
    if (v == std.math.maxInt(i64)) return w.writeAll("CRUX_I64_MAX");
    try w.print("{d}LL", .{v});
}

fn writeVal(w: *ast.W, v: ast.AbsVal) ast.W.Error!void {
    switch (v) {
        .Interval => |i| {
            try w.writeAll("{CRUX_INTERVAL, ");
            try writeI64(w, i.low);
            try w.writeAll(", ");
            try writeI64(w, i.high);
            try w.writeAll("}");
        },
        .Top => try w.writeAll("{CRUX_TOP, 0LL, 0LL}"),
        .Bottom => try w.writeAll("{CRUX_BOTTOM, 0LL, 0LL}"),
        .PointsTo => try w.writeAll("{CRUX_POINTS_TO, 0LL, 0LL}"),
        .Null => try w.writeAll("{CRUX_NULL, 0LL, 0LL}"),
        .Dangling => try w.writeAll("{CRUX_DANGLING, 0LL, 0LL}"),
    }
}

fn indexOf(state: ast.SASState, name: []const u8) ?usize {
    for (state.bindings, 0..) |b, i| if (std.mem.eql(u8, b.name, name)) return i;
    return null;
}

/// Compile `eval_formula_in_state` for one property to a C expression over `st`.
fn writeProp(w: *ast.W, f: ast.Formula, state: ast.SASState) ast.W.Error!void {
    switch (f) {
        .Atomic => |a| try w.writeAll(if (a == .False) "false" else "true"),
        .Not => |inner| {
            try w.writeAll("!(");
            try writeProp(w, inner.*, state);
            try w.writeAll(")");
        },
        .And, .Or => |fs| {
            if (fs.len == 0) return w.writeAll(if (f == .And) "true" else "false");
            try w.writeAll("(");
            for (fs, 0..) |s, i| {
                if (i > 0) try w.writeAll(if (f == .And) " && " else " || ");
                try writeProp(w, s, state);
            }
            try w.writeAll(")");
        },
        .Eq => |e| {
            if (e.lhs != .Var) return w.writeAll("true");
            if (e.rhs == .Var and std.mem.eql(u8, e.lhs.Var, e.rhs.Var)) return w.writeAll("true");
            const idx = indexOf(state, e.lhs.Var) orelse return w.writeAll("true");
            const rhs = sas.abstractTerm(e.rhs);
            try w.print("crux_subsumes(st[{d}], CruxAbsVal", .{idx});
            try writeVal(w, rhs);
            try w.writeAll(")");
        },
        .Paren => |inner| try writeProp(w, inner.*, state),
        else => try w.writeAll("true"),
    }
}

fn writeComment(w: *ast.W, s: []const u8) ast.W.Error!void {
    for (s) |c| {
        if (c == '\n') try w.writeAll(" ") else try w.writeByte(c);
    }
}

pub fn writeCuda(arena: std.mem.Allocator, w: *ast.W, source_name: []const u8, queries: []const Query) !void {
    try w.print("/* CRUX SAS analysis lowered to CUDA by `crux emit-cuda {s}`. */\n", .{source_name});
    try w.writeAll(header);
    for (queries, 0..) |q, k| {
        const st = q.query.state;
        const n = st.bindings.len;
        try w.print("/* query {d}: {s}\n * property: Safe(", .{ k, q.name });
        try writeComment(w, try ast.dumpAlloc(arena, q.query.property.Safe));
        try w.writeAll(")\n * initial: ");
        var buf: ast.W.Allocating = .init(arena);
        try sas.writeState(&buf.writer, st);
        try writeComment(w, try buf.toOwnedSlice());
        try w.writeAll(" */\n");
        try w.print("static const CruxAbsVal crux_init_{d}[{d}] = {{", .{ k, @max(n, 1) });
        if (n == 0) try w.writeAll("{CRUX_BOTTOM, 0LL, 0LL}");
        for (st.bindings, 0..) |b, i| {
            if (i > 0) try w.writeAll(", ");
            try writeVal(w, b.val);
            try w.print(" /* {s} */", .{b.name});
        }
        try w.writeAll("};\n\n");
        try w.print("CRUX_HD static inline bool crux_prop_{d}(const CruxAbsVal *st) {{\n    (void)st;\n    return ", .{k});
        try writeProp(w, q.query.property.Safe, st);
        try w.writeAll(";\n}\n\n");
        try w.print(
            \\__global__ void crux_sas_check_{d}(const CruxAbsVal *st, int *ok) {{
            \\    if (threadIdx.x == 0) *ok = crux_prop_{d}(st) ? 1 : 0;
            \\}}
            \\
            \\static int crux_analyze_{d}(int *iterations) {{
            \\    const int n = {d};
            \\    const int loop_bound = {d};
            \\    CruxAbsVal *cur, *next;
            \\    int *flag;
            \\    CRUX_ALLOC(cur, sizeof(CruxAbsVal) * {d});
            \\    CRUX_ALLOC(next, sizeof(CruxAbsVal) * {d});
            \\    CRUX_ALLOC(flag, sizeof(int));
            \\    for (int i = 0; i < {d}; ++i) cur[i] = crux_init_{d}[i];
            \\    int verdict = CRUX_UNKNOWN;
            \\    *iterations = 0;
            \\    for (int it = 1; it <= loop_bound; ++it) {{
            \\        *iterations = it;
            \\        *flag = 0;
            \\        CRUX_LAUNCH(crux_sas_step, {d}, cur, next, n, flag);
            \\        if (*flag == 0) {{
            \\            CRUX_LAUNCH(crux_sas_check_{d}, 1, next, flag);
            \\            verdict = *flag ? CRUX_PROVED : CRUX_ALARM;
            \\            break;
            \\        }}
            \\        CRUX_LAUNCH(crux_sas_widen, {d}, cur, next, n);
            \\    }}
            \\    CRUX_FREE(cur);
            \\    CRUX_FREE(next);
            \\    CRUX_FREE(flag);
            \\    return verdict;
            \\}}
            \\
            \\
        , .{ k, k, k, n, q.query.config.loop_bound, @max(n, 1), @max(n, 1), @max(n, 1), k, @max(n, 1), k, @max(n, 1) });
    }
    try w.writeAll("int main(void) {\n    int iterations = 0;\n    int verdict;\n");
    for (queries, 0..) |q, k| {
        try w.print("    verdict = crux_analyze_{d}(&iterations);\n", .{k});
        try w.print("    printf(\"query %s: %s after %d iteration(s)\\n\", \"{s}\", crux_verdict(verdict), iterations);\n", .{q.name});
    }
    try w.writeAll("    return 0;\n}\n");
}

pub fn cudaAlloc(arena: std.mem.Allocator, source_name: []const u8, queries: []const Query) ![]u8 {
    var aw: ast.W.Allocating = .init(arena);
    try writeCuda(arena, &aw.writer, source_name, queries);
    return aw.toOwnedSlice();
}

const testing = std.testing;
const parser = @import("parser.zig");

test "cuda: kernels, initial state and compiled property" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const form = (try parser.parseRussian(a, "сила(S2[x := 2 + 3], x = 5 ∧ ¬ (x = 6))")).ok.Sila;
    const q = try (sas.Analyzer{}).buildQuery(a, form.state, form.formula);
    const src = try cudaAlloc(a, "t.crux", &.{.{ .name = "g", .query = q }});
    try testing.expect(std.mem.indexOf(u8, src, "__global__ void crux_sas_step(") != null);
    try testing.expect(std.mem.indexOf(u8, src, "static const CruxAbsVal crux_init_0[2] = {{CRUX_INTERVAL, 0LL, 2LL} /* iter */, {CRUX_INTERVAL, 5LL, 5LL} /* x */};") != null);
    try testing.expect(std.mem.indexOf(u8, src, "return (crux_subsumes(st[1], CruxAbsVal{CRUX_INTERVAL, 5LL, 5LL}) && !(crux_subsumes(st[1], CruxAbsVal{CRUX_INTERVAL, 6LL, 6LL})));") != null);
    try testing.expect(std.mem.indexOf(u8, src, "CRUX_LAUNCH(crux_sas_step, 2, cur, next, n, flag);") != null);
}
