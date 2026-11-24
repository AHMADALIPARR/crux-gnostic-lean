// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! `crux` command-line compiler.

const std = @import("std");
const builtin = @import("builtin");
const crux = @import("root.zig");
const pipeline = crux.pipeline;
const abjad = crux.abjad;
const Io = std.Io;

const usage =
    \\usage: crux <command> [options] FILE
    \\
    \\commands:
    \\  lex        FILE   tokens with line:column
    \\  parse      FILE   AST of every item
    \\  lower      FILE   lowered state, formula and backend
    \\  emit-smt   FILE   SMT-LIB 2 for Z3
    \\  emit-lean  FILE   Lean 4 source
    \\  emit-sas   FILE   SAS abstract-interpretation report
    \\  emit-cuda  FILE   SAS analysis lowered to CUDA C
    \\  cert       FILE   proof-carrying certificates (JSON)
    \\  check      FILE   OMEGA verdict per goal (Z3 -> Lean -> SAS)
    \\  run        FILE   full pipeline report per goal
    \\  solve      FILE   finite-domain search over integer constraints
    \\  macros            OMEGA and Lean tactic macro tables
    \\  abjad      letters | value WORD... | digit-root N | wafq | constants | quadrant STEP
    \\  version
    \\
    \\options:
    \\  -o PATH           write the output to PATH
    \\  --no-z3           do not run z3 even if it is on PATH
    \\  --lean[=TOOLCHAIN] run `lean` (optionally `lean +TOOLCHAIN`) on goals Z3 leaves open
    \\  --timeout MS      z3 timeout in milliseconds
    \\
;

const Ctx = struct {
    gpa: std.mem.Allocator,
    io: Io,
    tmpdir: []const u8,
    use_z3: bool,
    z3_missing: bool = false,
    lean_toolchain: ?[]const u8,
    use_lean: bool,
    counter: u32 = 0,

    fn tempPath(self: *Ctx, arena: std.mem.Allocator, ext: []const u8) ![]const u8 {
        self.counter += 1;
        const pid: i64 = if (builtin.os.tag == .linux) std.os.linux.getpid() else 0;
        return std.fmt.allocPrint(arena, "{s}/crux_{d}_{d}.{s}", .{ self.tmpdir, pid, self.counter, ext });
    }

    fn runTool(self: *Ctx, arena: std.mem.Allocator, argv: []const []const u8) ?std.process.RunResult {
        return std.process.run(arena, self.io, .{ .argv = argv }) catch null;
    }

    fn runZ3(ctx_opaque: ?*anyopaque, arena: std.mem.Allocator, smt: []const u8) ?[]const u8 {
        const self: *Ctx = @ptrCast(@alignCast(ctx_opaque.?));
        if (!self.use_z3 or self.z3_missing) return null;
        const path = self.tempPath(arena, "smt2") catch return null;
        Io.Dir.cwd().writeFile(self.io, .{ .sub_path = path, .data = smt }) catch return null;
        defer Io.Dir.cwd().deleteFile(self.io, path) catch {};
        const r = self.runTool(arena, &.{ "z3", "-smt2", path }) orelse {
            self.z3_missing = true;
            return null;
        };
        return r.stdout;
    }

    fn runLean(ctx_opaque: ?*anyopaque, arena: std.mem.Allocator, src: []const u8) ?bool {
        const self: *Ctx = @ptrCast(@alignCast(ctx_opaque.?));
        if (!self.use_lean) return null;
        const path = self.tempPath(arena, "lean") catch return null;
        Io.Dir.cwd().writeFile(self.io, .{ .sub_path = path, .data = src }) catch return null;
        defer Io.Dir.cwd().deleteFile(self.io, path) catch {};
        const r = if (self.lean_toolchain) |tc|
            self.runTool(arena, &.{ "lean", std.fmt.allocPrint(arena, "+{s}", .{tc}) catch return null, path })
        else
            self.runTool(arena, &.{ "lean", path });
        const res = r orelse return null;
        return res.term == .exited and res.term.exited == 0;
    }
};

fn fail(stderr: *Io.Writer, comptime fmt: []const u8, args: anytype) u8 {
    stderr.print(fmt, args) catch {};
    stderr.flush() catch {};
    return 1;
}

pub fn main(init: std.process.Init) !u8 {
    const gpa = init.gpa;
    const io = init.io;
    var arena_state = std.heap.ArenaAllocator.init(gpa);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var out_buf: [8192]u8 = undefined;
    var out_w = Io.File.stdout().writer(io, &out_buf);
    const stdout = &out_w.interface;
    var err_buf: [1024]u8 = undefined;
    var err_w = Io.File.stderr().writer(io, &err_buf);
    const stderr = &err_w.interface;

    const argv = try init.minimal.args.toSlice(arena);
    if (argv.len < 2) return fail(stderr, "{s}", .{usage});
    const cmd = argv[1];

    var ctx: Ctx = .{
        .gpa = gpa,
        .io = io,
        .tmpdir = init.environ_map.get("TMPDIR") orelse "/tmp",
        .use_z3 = true,
        .lean_toolchain = null,
        .use_lean = false,
    };
    var out_path: ?[]const u8 = null;
    var timeout: ?u32 = null;
    var positional: std.ArrayList([]const u8) = .empty;
    var i: usize = 2;
    while (i < argv.len) : (i += 1) {
        const a = argv[i];
        if (std.mem.eql(u8, a, "-o")) {
            i += 1;
            if (i >= argv.len) return fail(stderr, "crux: -o needs a path\n", .{});
            out_path = argv[i];
        } else if (std.mem.eql(u8, a, "--no-z3")) {
            ctx.use_z3 = false;
        } else if (std.mem.eql(u8, a, "--lean")) {
            ctx.use_lean = true;
        } else if (std.mem.startsWith(u8, a, "--lean=")) {
            ctx.use_lean = true;
            ctx.lean_toolchain = a["--lean=".len..];
        } else if (std.mem.eql(u8, a, "--timeout")) {
            i += 1;
            if (i >= argv.len) return fail(stderr, "crux: --timeout needs milliseconds\n", .{});
            timeout = std.fmt.parseInt(u32, argv[i], 10) catch return fail(stderr, "crux: bad timeout '{s}'\n", .{argv[i]});
        } else try positional.append(arena, a);
    }

    if (std.mem.eql(u8, cmd, "version") or std.mem.eql(u8, cmd, "--version")) {
        try stdout.print("crux {s} (zig {s})\n", .{ crux.version, builtin.zig_version_string });
        try stdout.flush();
        return 0;
    }
    if (std.mem.eql(u8, cmd, "help") or std.mem.eql(u8, cmd, "--help") or std.mem.eql(u8, cmd, "-h")) {
        try stdout.writeAll(usage);
        try stdout.flush();
        return 0;
    }

    var text: Io.Writer.Allocating = .init(arena);
    if (std.mem.eql(u8, cmd, "macros")) {
        try writeMacros(&text.writer);
    } else if (std.mem.eql(u8, cmd, "abjad")) {
        if (try abjadCommand(&text.writer, positional.items)) |msg| return fail(stderr, "crux abjad: {s}\n", .{msg});
    } else {
        const Fn = *const fn (std.mem.Allocator, []const u8, pipeline.Options) anyerror!pipeline.Output;
        const table = [_]struct { []const u8, Fn }{
            .{ "lex", pipeline.emitTokens },     .{ "parse", pipeline.emitAst },
            .{ "lower", pipeline.emitLowered },  .{ "emit-smt", pipeline.emitSmt },
            .{ "emit-lean", pipeline.emitLean }, .{ "emit-sas", pipeline.emitSas },
            .{ "emit-cuda", pipeline.emitCuda }, .{ "cert", pipeline.emitCert },
            .{ "check", pipeline.check },        .{ "run", pipeline.run },
            .{ "solve", pipeline.solve },
        };
        const f: Fn = for (table) |e| {
            if (std.mem.eql(u8, e[0], cmd)) break e[1];
        } else return fail(stderr, "crux: unknown command '{s}'\n\n{s}", .{ cmd, usage });
        if (positional.items.len != 1) return fail(stderr, "crux {s}: expected one FILE\n", .{cmd});
        const path = positional.items[0];
        const src = Io.Dir.cwd().readFileAlloc(io, path, arena, .limited(64 << 20)) catch |e|
            return fail(stderr, "crux: cannot read {s}: {s}\n", .{ path, @errorName(e) });
        const uses_provers = std.mem.eql(u8, cmd, "check") or std.mem.eql(u8, cmd, "run") or std.mem.eql(u8, cmd, "cert");
        const opts: pipeline.Options = .{
            .source_name = path,
            .z3_timeout = timeout,
            .ext = if (uses_provers) .{ .ctx = &ctx, .run_z3 = Ctx.runZ3, .run_lean = Ctx.runLean } else .{},
        };
        switch (try f(arena, src, opts)) {
            .ok => |t| try text.writer.writeAll(t),
            .err => |m| return fail(stderr, "{s}\n", .{m}),
        }
    }

    if (out_path) |p| {
        Io.Dir.cwd().writeFile(io, .{ .sub_path = p, .data = text.written() }) catch |e|
            return fail(stderr, "crux: cannot write {s}: {s}\n", .{ p, @errorName(e) });
    } else {
        try stdout.writeAll(text.written());
        try stdout.flush();
    }
    return 0;
}

fn writeMacros(w: *Io.Writer) !void {
    try w.writeAll("OMEGA macros (omega_macro_definitions):\n");
    for (crux.omega.omega_macro_definitions) |m| try w.print("  {s} := {s}\n", .{ m[0], m[1] });
    try w.writeAll("\nLean tactic macros (lean_tactic_macros):\n");
    for (crux.monad_stack.lean_tactic_macros) |m| try w.print("  {s} [{s}] := {s}\n", .{ m[0], m[1], m[2] });
    try w.writeAll("\nCore Lean macros emitted by emit-lean:\n");
    try w.writeAll(crux.lean.prelude);
}

fn abjadCommand(w: *Io.Writer, args: []const []const u8) !?[]const u8 {
    if (args.len == 0) return "expected letters, value, digit-root, wafq, constants or quadrant";
    const sub = args[0];
    if (std.mem.eql(u8, sub, "letters")) {
        for (std.enums.values(abjad.ArabicLetter)) |l| try w.print("{s}\t{d}\t{s}\n", .{ @tagName(l), l.abjadValue(), @tagName(l.polarity()) });
    } else if (std.mem.eql(u8, sub, "value")) {
        if (args.len < 2) return "value needs at least one Arabic word";
        for (args[1..]) |word| {
            const r = abjad.wordValue(word) catch |e| return switch (e) {
                error.InvalidUtf8 => "invalid UTF-8",
                error.UnknownLetter => "not an Arabic letter in input",
            };
            try w.print("{s}\t{d}\tletters={d}\tdigit_root={d}\n", .{ word, r.value, r.letters, abjad.digitRoot(r.value) });
        }
    } else if (std.mem.eql(u8, sub, "digit-root")) {
        if (args.len != 2) return "digit-root needs one number";
        const n = std.fmt.parseInt(u32, args[1], 10) catch return "digit-root needs a non-negative integer";
        try w.print("{d}\n", .{abjad.digitRoot(n)});
    } else if (std.mem.eql(u8, sub, "wafq")) {
        const wq = abjad.WAFQ_ALLAH_3X3;
        try w.writeAll("WAFQ_ALLAH_3X3\n");
        for (wq.matrix) |row| try w.print("  {d:>3} {d:>3} {d:>3}\n", .{ row[0], row[1], row[2] });
        try w.print("constant_sum {d}\nrows {d} {d} {d}\ncolumns {d} {d} {d}\ndiagonal {d}\nanti-diagonal {d}\nverify {s}\n", .{
            wq.constant_sum, wq.rowSum(0),     wq.rowSum(1),                         wq.rowSum(2), wq.colSum(0), wq.colSum(1), wq.colSum(2),
            wq.diagSum(),    wq.antiDiagSum(), if (wq.verify()) "true" else "false",
        });
    } else if (std.mem.eql(u8, sub, "constants")) {
        const C = struct { []const u8, u32 };
        const cs = [_]C{
            .{ "AL_HAMID_VALUE", abjad.AL_HAMID_VALUE },           .{ "MIRROR_DIMENSION", abjad.MIRROR_DIMENSION },
            .{ "BIFURCATION_ORDER", abjad.BIFURCATION_ORDER },     .{ "BIFURCATION_THRESHOLD", abjad.BIFURCATION_THRESHOLD },
            .{ "AL_HAMID_FULL_VALUE", abjad.AL_HAMID_FULL_VALUE }, .{ "AHMAD_VALUE", abjad.AHMAD_VALUE },
            .{ "ALI_VALUE", abjad.ALI_VALUE },                     .{ "MASTER_AGGREGATE", abjad.MASTER_AGGREGATE },
            .{ "MATRIX_DIMENSION", abjad.MATRIX_DIMENSION },       .{ "JAMAL_VECTOR", abjad.JAMAL_VECTOR },
            .{ "JALAL_VECTOR", abjad.JALAL_VECTOR },               .{ "POLARITY_DELTA", abjad.POLARITY_DELTA },
            .{ "WAFQ_16X16_MAGIC", abjad.WAFQ_16X16_MAGIC },
        };
        for (cs) |c| try w.print("{s}\t{d}\n", .{ c[0], c[1] });
        try w.print("AL_HAMID_MATRIX.verify_invariants\t{s}\n", .{if (abjad.AL_HAMID_MATRIX.verifyInvariants()) "true" else "false"});
    } else if (std.mem.eql(u8, sub, "quadrant")) {
        if (args.len != 2) return "quadrant needs one step";
        const s = std.fmt.parseInt(u64, args[1], 10) catch return "quadrant needs a non-negative integer";
        const q = abjad.DecoherenceQuadrant.fromStep(s);
        try w.print("{s}\t{s}\tkenoma={s}\tpleroma={s}\n", .{ @tagName(q), @tagName(q.polarity()), if (abjad.kenomaState(s)) "true" else "false", if (abjad.pleromaState(s)) "true" else "false" });
    } else return "unknown abjad subcommand";
    return null;
}
