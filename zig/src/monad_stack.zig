// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! Lean 4 monad-stack model (port of lean_monad_stack.rs and the tactic
//! infrastructure appended to lean_backend.rs / Crux.TacticInfra): monad
//! layers, tactic state and goal management, recursive goal stacks, macro
//! hygiene, and the MetaM / TacticM / MonadQuotation operation tables.

const std = @import("std");

pub const MonadLayer = enum { CoreM, MetaM, ElabM, TermElabM, TacticM, CommandElabM, MacroM, MacroT, QuotationM, IO };
pub const MVarId = u32;
pub const FVarId = u32;
pub const BinderInfo = enum { Default, Implicit, StrictImplicit, Instance, OutParam };
pub const TransparencyMode = enum { All, Default, Reducible, Instances, None };
pub const NewGoals = enum { GoalsFirst, GoalsLast, GoalsIndep };
pub const TacticLocation = enum { Everywhere, Target, Hypotheses, Wildcard };

pub const TacticConfig = struct {
    transparent: TransparencyMode = .Default,
    new_goals: NewGoals = .GoalsFirst,
    location: TacticLocation = .Everywhere,
};

pub const TacticContext = struct {
    main: ?MVarId = null,
    elaborator: []const u8 = "",
    recover: bool = true,
    config: TacticConfig = .{},
};

pub const TacticState = struct {
    goals: std.ArrayList(MVarId) = .empty,
    aux_goals: std.ArrayList(MVarId) = .empty,

    pub fn deinit(self: *TacticState, gpa: std.mem.Allocator) void {
        self.goals.deinit(gpa);
        self.aux_goals.deinit(gpa);
    }
    pub fn getGoals(self: *const TacticState) []const MVarId {
        return self.goals.items;
    }
    pub fn setGoals(self: *TacticState, gpa: std.mem.Allocator, goals: []const MVarId) !void {
        self.goals.clearRetainingCapacity();
        try self.goals.appendSlice(gpa, goals);
    }
    pub fn getMainGoal(self: *const TacticState) ?MVarId {
        return if (self.goals.items.len > 0) self.goals.items[0] else null;
    }
    /// Remove the main goal and put `new_goals` in front of the rest.
    pub fn replaceMainGoal(self: *TacticState, gpa: std.mem.Allocator, new_goals: []const MVarId) !void {
        if (self.goals.items.len == 0) return;
        _ = self.goals.orderedRemove(0);
        try self.goals.insertSlice(gpa, 0, new_goals);
    }
    pub fn done(self: *const TacticState) bool {
        return self.goals.items.len == 0;
    }
    /// No-op, as in the source (Lean checks mvar assignment here).
    pub fn pruneSolved(self: *TacticState) void {
        _ = self;
    }
};

/// `tactic_repeat`: run until the tactic fails or `max_iter` is reached.
pub fn tacticRepeat(ctx: anytype, comptime tactic: fn (@TypeOf(ctx)) bool, max_iter: usize) usize {
    var count: usize = 0;
    while (count < max_iter) : (count += 1) {
        if (!tactic(ctx)) break;
    }
    return count;
}

pub const RecGoal = struct {
    id: MVarId,
    parent: ?MVarId,
    layer: usize,
    tag: []const u8,
};

pub const RecTacticState = struct {
    focus_path: std.ArrayList(MVarId) = .empty,
    depth: usize = 0,

    pub fn pushFocus(self: *RecTacticState, gpa: std.mem.Allocator, goal: MVarId) !void {
        try self.focus_path.append(gpa, goal);
        self.depth += 1;
    }
    pub fn popFocus(self: *RecTacticState) void {
        _ = self.focus_path.pop();
        if (self.depth > 0) self.depth -= 1;
    }
};

pub fn makeRecGoal(id: MVarId, parent: ?MVarId, layer: usize, tag: []const u8) RecGoal {
    return .{ .id = id, .parent = parent, .layer = layer, .tag = tag };
}

pub const HygienicName = struct {
    base: []const u8,
    scopes: []const u64,

    pub fn erase(self: HygienicName) []const u8 {
        return self.base;
    }
    pub fn hasScopes(self: HygienicName) bool {
        return self.scopes.len > 0;
    }
};

pub fn addMacroScope(arena: std.mem.Allocator, base: []const u8, scope: u64) !HygienicName {
    return .{ .base = base, .scopes = try arena.dupe(u64, &.{scope}) };
}

pub const Entry2 = struct { []const u8, []const u8 };
pub const Entry3 = struct { []const u8, []const u8, []const u8 };

pub const lean_tactic_macros = [_]Entry3{
    .{ "sila_tac", "tactic", "withMainContext do let goal <- getMainTarget; let goal' <- liftMetaM (DUP goal); evalTactic (<- `(tactic| DUP <;> sila_auto <;> try omega))" },
    .{ "crux_tac", "tactic", "withFreshMacroScope do `(tactic| sila_tac <;> crux_dup <;> try z3_decide <;> try aesop)" },
    .{ "dup_at", "tactic", "evalTactic (<- `(tactic| DUP at loc))" },
    .{ "let!", "term", "do let x <- mkFreshIdent x; `(let $x := $v; $body)" },
    .{ "have!", "tactic", "withFreshMacroScope do let n <- mkFreshIdent n; `(tactic| have $n : $t := $v)" },
    .{ "quote_hygienic", "term", "do let stx <- Quote.quote t; let stx' <- withFreshMacroScope (quote stx); elabTerm stx'" },
};

pub const meta_m_operations = [_]Entry2{
    .{ "getLCtx", "MetaM LocalContext" },
    .{ "withLCtx", "LocalContext -> MetaM a -> MetaM a" },
    .{ "mkFreshExprMVar", "Option Expr -> MetaM Expr" },
    .{ "assignExprMVar", "MVarId -> Expr -> MetaM Unit" },
    .{ "isDefEq", "Expr -> Expr -> MetaM Bool" },
    .{ "whnf", "Expr -> MetaM Expr" },
    .{ "reduce", "Expr -> MetaM Expr" },
    .{ "inferType", "Expr -> MetaM Expr" },
    .{ "synthInstance", "Expr -> MetaM Expr" },
    .{ "isTypeCorrect", "Expr -> MetaM Bool" },
    .{ "instantiateMVars", "Expr -> MetaM Expr" },
    .{ "withMVarContext", "MVarId -> MetaM a -> MetaM a" },
    .{ "getEnv", "MetaM Environment" },
    .{ "modifyEnv", "(Environment -> Environment) -> MetaM Unit" },
    .{ "trace", "Name -> (Unit -> MessageData) -> MetaM Unit" },
    .{ "throwError", "MessageData -> MetaM a" },
    .{ "orElse", "MetaM a -> (Unit -> MetaM a) -> MetaM a" },
    .{ "tryCatch", "MetaM a -> (Exception -> MetaM a) -> MetaM a" },
};

pub const tactic_m_operations = [_]Entry2{
    .{ "getGoals", "TacticM (List MVarId)" },
    .{ "setGoals", "List MVarId -> TacticM Unit" },
    .{ "getMainGoal", "TacticM MVarId" },
    .{ "getMainTarget", "TacticM Expr" },
    .{ "replaceMainGoal", "List MVarId -> TacticM Unit" },
    .{ "done", "TacticM Unit" },
    .{ "intro", "Name -> TacticM Unit" },
    .{ "intros", "TacticM Unit" },
    .{ "apply", "Expr -> TacticM Unit" },
    .{ "exact", "Expr -> TacticM Unit" },
    .{ "assumption", "TacticM Unit" },
    .{ "cases", "Expr -> TacticM Unit" },
    .{ "induction", "Expr -> TacticM Unit" },
    .{ "simp", "SimpConfig -> List SimpArg -> Location -> TacticM Unit" },
    .{ "left", "TacticM Unit" },
    .{ "right", "TacticM Unit" },
    .{ "constructor", "TacticM Unit" },
    .{ "exfalso", "TacticM Unit" },
    .{ "decide", "TacticM Unit" },
    .{ "omega", "TacticM Unit" },
    .{ "ring", "TacticM Unit" },
    .{ "allGoals", "TacticM Unit -> TacticM Unit" },
    .{ "anyGoals", "TacticM Unit -> TacticM Unit" },
    .{ "focus", "TacticM a -> TacticM a" },
    .{ "try", "TacticM a -> TacticM (Option a)" },
    .{ "repeat'", "TacticM Unit -> TacticM Unit" },
    .{ "first", "List (TacticM a) -> TacticM a" },
    .{ "liftMetaM", "MetaM a -> TacticM a" },
    .{ "liftMetaTactic", "(MVarId -> MetaM (List MVarId)) -> TacticM Unit" },
    .{ "evalTactic", "Syntax -> TacticM Unit" },
    .{ "withMainContext", "TacticM a -> TacticM a" },
};

pub const monad_quotation_operations = [_]Entry2{
    .{ "getCurrMacroScope", "m MacroScope" },
    .{ "getMainModule", "m Name" },
    .{ "withFreshMacroScope", "m a -> m a" },
    .{ "quote", "Syntax -> m Syntax" },
    .{ "quoteTerm", "Expr -> m Syntax" },
    .{ "mkIdent", "Name -> m Syntax" },
    .{ "mkFreshIdent", "Syntax -> m Syntax" },
    .{ "withAntiquote", "m a -> m a" },
    .{ "withRef", "Syntax -> m a -> m a" },
};

const testing = std.testing;

test "monad stack: goal management and focus stack" {
    const gpa = testing.allocator;
    var s: TacticState = .{};
    defer s.deinit(gpa);
    try s.setGoals(gpa, &.{ 1, 2, 3 });
    try testing.expectEqual(@as(?MVarId, 1), s.getMainGoal());
    try s.replaceMainGoal(gpa, &.{ 10, 11 });
    try testing.expectEqualSlices(MVarId, &.{ 10, 11, 2, 3 }, s.getGoals());
    try s.setGoals(gpa, &.{});
    try testing.expect(s.done());
    var r: RecTacticState = .{};
    defer r.focus_path.deinit(gpa);
    try r.pushFocus(gpa, 7);
    try r.pushFocus(gpa, 8);
    r.popFocus();
    try testing.expectEqual(@as(usize, 1), r.depth);
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const h = try addMacroScope(arena.allocator(), "x", 42);
    try testing.expect(h.hasScopes());
    try testing.expectEqualStrings("x", h.erase());
    try testing.expectEqual(@as(usize, 31), tactic_m_operations.len);
}
