// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! CRUX core AST: the recursive state IR.
//! Sorts, terms, formulas, states, backends (GHC | Kani), Z3 and SAS queries,
//! Lean 4 goals and tactics, proof closures, final results and Russian forms.
//! Every node is allocated in the caller's arena; nodes are never freed one by one.

const std = @import("std");

pub const Ident = []const u8;

pub const Literal = union(enum) {
    Number: i64,
    Str: []const u8,
    Bool: bool,
    BitVecLit: struct { value: u64, width: u32 },
    Nil,
    Unit,
};

pub const Sort = union(enum) {
    Prop,
    Type,
    Nat,
    Int,
    Bool,
    BitVec: u32,
    List: *const Sort,
    Array: struct { key: *const Sort, value: *const Sort },
    Arrow: struct { from: *const Sort, to: *const Sort },
    State,
    Formula,
    Term,
    MIR,
    Core,
    Haskell,
    Rust,
    Z3Expr,
    LeanTerm,
    SASAbs,
    User: Ident,
};

pub const BinOp = enum { Add, Sub, Mul, Div, Mod, Eq, Ne, Lt, Le, Gt, Ge };

pub const Term = union(enum) {
    Var: Ident,
    Const: Literal,
    Lambda: struct { param: Ident, sort: Sort, body: *const Term },
    App: struct { func: *const Term, arg: *const Term },
    BinOp: struct { op: BinOp, lhs: *const Term, rhs: *const Term },
    Cons: struct { head: *const Term, tail: *const Term },
    Nil,
    Concat: struct { lhs: *const Term, rhs: *const Term },
    IfThenElse: struct { cond: *const Formula, then: *const Term, else_: *const Term },
    Match: struct { scrutinee: *const Term, arms: []const MatchArm },
    Fold: struct { init: *const Term, step: *const Term },
    Rec: struct { name: Ident, body: *const Term },
    Tuple: []const Term,
    Field: struct { base: *const Term, name: Ident },
    Paren: *const Term,
};

pub const MatchArm = struct { pattern: Pattern, body: Term };

pub const Pattern = union(enum) {
    Var: Ident,
    Const: Literal,
    Wildcard,
    Cons: struct { head: *const Pattern, tail: *const Pattern },
    Tuple: []const Pattern,
};

pub const Formula = union(enum) {
    Atomic: Atomic,
    Not: *const Formula,
    And: []const Formula,
    Or: []const Formula,
    Implies: FBin,
    Iff: FBin,
    Forall: FQuant,
    Exists: FQuant,
    Mu: FFix,
    Nu: FFix,
    Eq: struct { lhs: Term, rhs: Term },
    Sila: struct { state: State, formula: *const Formula },
    Paren: *const Formula,
};

pub const FBin = struct { lhs: *const Formula, rhs: *const Formula };
pub const FQuant = struct { var_: Ident, sort: Sort, body: *const Formula };
pub const FFix = struct { var_: Ident, body: *const Formula };

pub const Atomic = union(enum) {
    Predicate: struct { name: Ident, args: []const Term },
    Member: struct { elem: *const Term, set: *const Term },
    Predecessor: struct { less: *const Term, greater: *const Term },
    True,
    False,
};

pub const BindingKind = enum { Assign, Arrow, Let };

pub const Binding = struct { var_: Ident, value: Term, kind: BindingKind };

pub const State = union(enum) {
    S,
    S0,
    Sn: u32,
    Prime: *const State,
    Update: struct { base: *const State, var_: Ident, value: Term },
    Bind: struct { base: *const State, binding: Binding },
    Recursive: struct { var_: Ident, body: *const Formula },
};

// ---------------------------------------------------------------------------
// Backends
// ---------------------------------------------------------------------------

pub const Backend = union(enum) {
    GHC: GHCIR,
    Kani: KaniMIR,
};

pub const GHCIR = struct { module_name: Ident, decls: []const GHCDecl };

pub const GHCDecl = union(enum) {
    Data: struct { name: Ident, constructors: []const GHCConstructor },
    Type: struct { name: Ident, target: Sort },
    Function: struct { name: Ident, sort: Sort, body: Term },
};

pub const GHCConstructor = struct { name: Ident, arg_sorts: []const Sort };

pub const Param = struct { name: Ident, sort: Sort };

pub const KaniMIR = struct {
    name: Ident,
    params: []const Param,
    return_sort: Sort,
    body: []const MIRStatement,
};

pub const MIRStatement = union(enum) {
    Let: struct { name: Ident, value: Term },
    AssertEq: struct { lhs: Term, rhs: Term },
    Assert: Formula,
    Expr: Term,
    Return: Term,
    IfThenElse: struct { cond: Formula, then: []const MIRStatement, else_: []const MIRStatement },
    Loop: []const MIRStatement,
    Unsafe: []const MIRStatement,
    KaniProof: []const MIRStatement,
    KaniUnwind: u32,
};

// ---------------------------------------------------------------------------
// OMEGA targets: Z3
// ---------------------------------------------------------------------------

pub const Z3Context = struct {
    timeout: ?u32 = null,
    model: bool = true,
    unsat_core: bool = false,
    proof: bool = false,
};

pub const Z3Command = union(enum) {
    DeclareConst: struct { name: Ident, sort: Sort },
    DeclareFun: struct { name: Ident, arg_sorts: []const Sort, ret_sort: Sort },
    Assert: *const Z3Expr,
    CheckSat,
    GetModel,
    GetUnsatCore,
    GetProof,
    Push: u32,
    Pop: u32,
};

pub const Z3Query = struct { context: Z3Context, commands: []const Z3Command };

pub const Z3Binder = struct { name: Ident, sort: Sort };
pub const Z3Bin = struct { lhs: *const Z3Expr, rhs: *const Z3Expr };
pub const Z3Quant = struct { vars: []const Z3Binder, body: *const Z3Expr };

pub const Z3Expr = union(enum) {
    Const: Ident,
    Lit: struct { value: i64, sort: Sort },
    App: struct { func: Ident, args: []const Z3Expr },
    And: []const Z3Expr,
    Or: []const Z3Expr,
    Not: *const Z3Expr,
    Implies: Z3Bin,
    Ite: struct { cond: *const Z3Expr, then: *const Z3Expr, else_: *const Z3Expr },
    Eq: Z3Bin,
    Distinct: []const Z3Expr,
    Lt: Z3Bin,
    Le: Z3Bin,
    Gt: Z3Bin,
    Ge: Z3Bin,
    BvAdd: Z3Bin,
    BvSub: Z3Bin,
    BvMul: Z3Bin,
    BvNot: *const Z3Expr,
    Forall: Z3Quant,
    Exists: Z3Quant,
};

// ---------------------------------------------------------------------------
// OMEGA targets: SAS (symbolic abstract semantics)
// ---------------------------------------------------------------------------

pub const AbsDomain = enum { Intervals, Octagons, Polyhedra, Zones, Congruences, Signs, Constants, Predicate, Shape, Heap };

pub const Widening = union(enum) { Standard, Delayed: u32, Threshold, Localized };

pub const SASConfig = struct {
    domain: AbsDomain = .Intervals,
    widening: Widening = .Standard,
    narrowing: u32 = 1,
    threshold: u32 = 16,
    loop_bound: u32 = 10,
    track_pointers: bool = true,
    track_arrays: bool = false,
    relational: bool = false,
};

pub const AbsVal = union(enum) {
    Interval: struct { low: i64, high: i64 },
    Top,
    Bottom,
    PointsTo: Ident,
    Null,
    Dangling,
};

pub const AbsBinding = struct { name: Ident, val: AbsVal };

pub const SASState = struct { bindings: []const AbsBinding };

pub const SASProperty = union(enum) {
    Safe: Formula,
    Reach: Formula,
    Invariant: Formula,
    Assertion: Formula,
    Termination,
    NonTermination,
};

pub const SASQuery = struct { config: SASConfig, state: SASState, property: SASProperty };

// ---------------------------------------------------------------------------
// OMEGA targets: Lean 4
// ---------------------------------------------------------------------------

pub const LeanGoalKind = enum { Theorem, Lemma, Example };

pub const LeanTactic = union(enum) {
    Exact: Term,
    Apply: Term,
    Intro: []const Ident,
    Simpl,
    SimplAll,
    Ring,
    Linarith,
    Omega,
    Decide,
    Aesop,
    Trivial,
    Constructor,
    Left,
    Right,
    Exfalso,
    Macro: Ident,
    Focus: []const LeanTactic,
    Seq: []const LeanTactic,
    Try: *const LeanTactic,
    Repeat: *const LeanTactic,
    AllGoals: *const LeanTactic,
    Sorry,
};

pub const LeanGoal = struct {
    kind: LeanGoalKind,
    name: Ident,
    formula: Formula,
    tactics: []const LeanTactic,
};

// ---------------------------------------------------------------------------
// Proof closure and final results
// ---------------------------------------------------------------------------

pub const DischargeMethod = union(enum) {
    Z3Check,
    SASProve,
    LeanTactic: LeanTactic,
    CruxClose,
    Assumption: Ident,
};

pub const Obligation = struct { id: u32, formula: Formula, discharged_by: DischargeMethod };

pub const ProofClosure = struct { obligations: []const Obligation };

pub const ModelEntry = struct { name: Ident, value: Term };

pub const FinalResult = union(enum) {
    Sat,
    Unsat,
    Model: []const ModelEntry,
    Unknown,
    Timeout,
    Alarm: struct { location: Ident, formula: Formula },
    Proved,
};

/// Russian surface forms, parsed then lowered to the AST above.
pub const RussianForm = union(enum) {
    Ravnostvo: struct { lhs: Term, rhs: Term }, // равенство(A, B)
    Implikatsiya: struct { lhs: Formula, rhs: Formula }, // импликация(A, B)
    Konyunktsiya: struct { lhs: Formula, rhs: Formula }, // конъюнкция(A, B)
    Dizyunktsiya: struct { lhs: Formula, rhs: Formula }, // дизъюнкция(A, B)
    Otritsanie: Formula, // отрицание(A)
    DlyaVsekh: struct { var_: Ident, sort: Sort, body: Formula }, // для_всех x : S. P
    Sushchestvuet: struct { var_: Ident, sort: Sort, body: Formula }, // существует x : S. P
    Rekursiya: struct { var_: Ident, body: Formula }, // рекурсия x. P
    Sostoyanie: State, // состояние S
    Sila: struct { state: State, formula: Formula }, // сила(S, P)
    Omega: struct { backend: Backend, state: State, formula: Formula }, // омега(B, S, P)
    Dokazatelstvo: ProofClosure, // доказательство
    /// A bare formula at top level (CRUX source-file extension).
    Bare: Formula,
};

// ---------------------------------------------------------------------------
// Small constructors
// ---------------------------------------------------------------------------

pub fn box(arena: std.mem.Allocator, value: anytype) !*const @TypeOf(value) {
    const p = try arena.create(@TypeOf(value));
    p.* = value;
    return p;
}

pub const true_formula: Formula = .{ .Atomic = .True };

pub fn defaultKani() KaniMIR {
    return .{ .name = "harness", .params = &.{}, .return_sort = .Bool, .body = &.{} };
}

// ---------------------------------------------------------------------------
// Rust-Debug-style printer, used by `crux parse` / `crux lower` and reports.
// ---------------------------------------------------------------------------

pub const W = std.Io.Writer;

pub fn dump(w: *W, value: anytype) W.Error!void {
    const T = @TypeOf(value);
    switch (@typeInfo(T)) {
        .bool => try w.writeAll(if (value) "true" else "false"),
        .int, .comptime_int => try w.print("{d}", .{value}),
        .@"enum" => try w.writeAll(@tagName(value)),
        .optional => if (value) |v| {
            try w.writeAll("Some(");
            try dump(w, v);
            try w.writeAll(")");
        } else try w.writeAll("None"),
        .pointer => |p| switch (p.size) {
            .one => try dump(w, value.*),
            .slice => {
                if (p.child == u8) {
                    try w.writeByte('"');
                    try w.writeAll(value);
                    try w.writeByte('"');
                } else {
                    try w.writeAll("[");
                    for (value, 0..) |item, i| {
                        if (i > 0) try w.writeAll(", ");
                        try dump(w, item);
                    }
                    try w.writeAll("]");
                }
            },
            else => @compileError("dump: unsupported pointer"),
        },
        .@"struct" => |s| {
            try w.writeAll("{ ");
            inline for (s.field_names, 0..) |fname, i| {
                if (i > 0) try w.writeAll(", ");
                const name = comptime if (std.mem.endsWith(u8, fname, "_")) fname[0 .. fname.len - 1] else fname;
                try w.writeAll(name ++ ": ");
                try dump(w, @field(value, fname));
            }
            try w.writeAll(" }");
        },
        .@"union" => |u| {
            const tag = std.meta.activeTag(value);
            inline for (u.field_names, u.field_types) |fname, ftype| {
                if (std.mem.eql(u8, fname, @tagName(tag))) {
                    try w.writeAll(fname);
                    if (ftype != void) {
                        const payload = @field(value, fname);
                        if (@typeInfo(ftype) == .@"struct") {
                            try w.writeAll(" ");
                            try dump(w, payload);
                        } else {
                            try w.writeAll("(");
                            try dump(w, payload);
                            try w.writeAll(")");
                        }
                    }
                }
            }
        },
        .void => {},
        else => @compileError("dump: unsupported type " ++ @typeName(T)),
    }
}

pub fn dumpAlloc(arena: std.mem.Allocator, value: anytype) ![]u8 {
    var aw: W.Allocating = .init(arena);
    try dump(&aw.writer, value);
    return aw.toOwnedSlice();
}

/// Rust `Display for FinalResult`.
pub fn writeFinal(w: *W, r: FinalResult) W.Error!void {
    switch (r) {
        .Sat => try w.writeAll("SAT"),
        .Unsat => try w.writeAll("UNSAT"),
        .Model => |m| {
            try w.writeAll("MODEL{ ");
            for (m, 0..) |e, i| {
                if (i > 0) try w.writeAll(", ");
                try dump(w, e.name);
                try w.writeAll(" \u{21A6} ");
                try dump(w, e.value);
            }
            try w.writeAll(" }");
        },
        .Unknown => try w.writeAll("UNKNOWN"),
        .Timeout => try w.writeAll("TIMEOUT"),
        .Alarm => |a| {
            try w.print("ALARM at {s}: ", .{a.location});
            try dump(w, a.formula);
        },
        .Proved => try w.writeAll("PROVED"),
    }
}

test "dump renders nested AST like Rust Debug" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const a = arena_state.allocator();
    const f: Formula = .{ .Eq = .{ .lhs = .{ .Var = "x" }, .rhs = .{ .Const = .{ .Number = 1 } } } };
    const s = try dumpAlloc(a, f);
    try std.testing.expectEqualStrings("Eq { lhs: Var(\"x\"), rhs: Const(Number(1)) }", s);
}
