// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! C ABI for libcrux (header: include/crux.h). Every text function takes a
//! UTF-8 source buffer and returns 0 with the artifact in `*out`, 1 with a
//! `file:line:col: error: ...` diagnostic in `*out`, or 2 on allocation
//! failure (`*out` is NULL). Strings returned in `*out` are NUL-terminated
//! and must be released with `crux_free`. The library never runs z3 or lean.

const std = @import("std");
const crux = @import("root.zig");
const pipeline = crux.pipeline;
const abjad = crux.abjad;

const gpa = std.heap.smp_allocator;

const Emitter = *const fn (std.mem.Allocator, []const u8, pipeline.Options) anyerror!pipeline.Output;

fn give(text: []const u8, out: *?[*:0]u8) bool {
    const buf = gpa.allocSentinel(u8, text.len, 0) catch return false;
    @memcpy(buf, text);
    out.* = buf.ptr;
    return true;
}

fn call(f: Emitter, src: ?[*]const u8, len: usize, out: *?[*:0]u8) c_int {
    out.* = null;
    var arena_state = std.heap.ArenaAllocator.init(gpa);
    defer arena_state.deinit();
    const text: []const u8 = if (src) |s| s[0..len] else "";
    const r = f(arena_state.allocator(), text, .{ .source_name = "<input>" }) catch return 2;
    return switch (r) {
        .ok => |t| if (give(t, out)) 0 else 2,
        .err => |t| if (give(t, out)) 1 else 2,
    };
}

export fn crux_version() [*:0]const u8 {
    return crux.version;
}
export fn crux_free(p: ?[*:0]u8) void {
    const ptr = p orelse return;
    const s = std.mem.span(ptr);
    gpa.free(ptr[0 .. s.len + 1]);
}
export fn crux_lex(src: ?[*]const u8, len: usize, out: *?[*:0]u8) c_int {
    return call(pipeline.emitTokens, src, len, out);
}
export fn crux_parse(src: ?[*]const u8, len: usize, out: *?[*:0]u8) c_int {
    return call(pipeline.emitAst, src, len, out);
}
export fn crux_lower(src: ?[*]const u8, len: usize, out: *?[*:0]u8) c_int {
    return call(pipeline.emitLowered, src, len, out);
}
export fn crux_emit_smt(src: ?[*]const u8, len: usize, out: *?[*:0]u8) c_int {
    return call(pipeline.emitSmt, src, len, out);
}
export fn crux_emit_lean(src: ?[*]const u8, len: usize, out: *?[*:0]u8) c_int {
    return call(pipeline.emitLean, src, len, out);
}
export fn crux_emit_sas(src: ?[*]const u8, len: usize, out: *?[*:0]u8) c_int {
    return call(pipeline.emitSas, src, len, out);
}
export fn crux_emit_cuda(src: ?[*]const u8, len: usize, out: *?[*:0]u8) c_int {
    return call(pipeline.emitCuda, src, len, out);
}
export fn crux_cert(src: ?[*]const u8, len: usize, out: *?[*:0]u8) c_int {
    return call(pipeline.emitCert, src, len, out);
}
export fn crux_check(src: ?[*]const u8, len: usize, out: *?[*:0]u8) c_int {
    return call(pipeline.check, src, len, out);
}
export fn crux_run(src: ?[*]const u8, len: usize, out: *?[*:0]u8) c_int {
    return call(pipeline.run, src, len, out);
}
export fn crux_solve(src: ?[*]const u8, len: usize, out: *?[*:0]u8) c_int {
    return call(pipeline.solve, src, len, out);
}

/// Abjad value of Arabic text: 0 ok, 1 invalid UTF-8 or a non-Arabic letter.
export fn crux_abjad_value(text: ?[*]const u8, len: usize, value: *u32) c_int {
    const t: []const u8 = if (text) |p| p[0..len] else "";
    const r = abjad.wordValue(t) catch return 1;
    value.* = r.value;
    return 0;
}
export fn crux_abjad_digit_root(n: u32) u8 {
    return abjad.digitRoot(n);
}
/// Value of letter `index` (0 = Alif ... 27 = Ghayn), 0 if out of range.
export fn crux_abjad_letter_value(index: c_int) u32 {
    if (index < 0 or index >= 28) return 0;
    return @as(abjad.ArabicLetter, @fromBackingInt(@intCast(index))).abjadValue();
}
export fn crux_wafq_allah_verify() bool {
    return abjad.WAFQ_ALLAH_3X3.verify();
}
/// Row sums, column sums, diagonal and anti-diagonal of WAFQ_ALLAH_3X3.
export fn crux_wafq_allah_sums(out: *[8]u32) void {
    const w = abjad.WAFQ_ALLAH_3X3;
    for (0..3) |i| out[i] = w.rowSum(i);
    for (0..3) |j| out[3 + j] = w.colSum(j);
    out[6] = w.diagSum();
    out[7] = w.antiDiagSum();
}

test "capi: round trip through the exported functions" {
    var out: ?[*:0]u8 = null;
    const src = "равенство(x + 1, 1 + x)";
    try std.testing.expectEqual(@as(c_int, 0), crux_emit_smt(src.ptr, src.len, &out));
    try std.testing.expect(std.mem.indexOf(u8, std.mem.span(out.?), "(bvadd x (_ bv1 32))") != null);
    crux_free(out);
    const bad = "сила(";
    try std.testing.expectEqual(@as(c_int, 1), crux_parse(bad.ptr, bad.len, &out));
    try std.testing.expect(std.mem.startsWith(u8, std.mem.span(out.?), "<input>:1:6: error:"));
    crux_free(out);
    var v: u32 = 0;
    const word = "الله";
    try std.testing.expectEqual(@as(c_int, 0), crux_abjad_value(word.ptr, word.len, &v));
    try std.testing.expectEqual(@as(u32, 66), v);
    var sums: [8]u32 = undefined;
    crux_wafq_allah_sums(&sums);
    try std.testing.expectEqualSlices(u32, &.{ 33, 33, 33, 33, 33, 33, 21, 45 }, &sums);
    try std.testing.expect(!crux_wafq_allah_verify());
}
