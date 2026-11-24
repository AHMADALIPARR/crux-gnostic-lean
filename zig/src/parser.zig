// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! Recursive-descent parser for the Russian syntax (port of russian.rs section 3
//! and Crux.Russian). Terms, sorts, formulas, states and Russian forms, plus a
//! source-file layer: a CRUX file is a list of items separated by `;`, each
//! optionally named with `theorem NAME :`, `lemma NAME :` or `example :`.
//!
//! Where the Rust parser was incomplete it is completed here:
//! - all twelve Russian forms parse (the Rust `parse_russian_form` handled four);
//!   the forms are also accepted in formula position;
//! - `омега(B, S, P)` parses its backend (`GHC` or `Kani`) instead of skipping a
//!   placeholder token;
//! - `∨`/`or` builds `Or` (the Rust builds `And`), `↔`/`iff` builds `Iff`;
//! - application is left-associative: `f x y` is `(f x) y`;
//! - `(term) = term` backtracks out of the parenthesised-formula branch;
//! - `S₀` is accepted as the state `S0`.

const std = @import("std");
const ast = @import("ast.zig");
const lexer = @import("lexer.zig");
const Tag = lexer.Tag;
const Token = lexer.Token;

pub const ItemKind = enum { Theorem, Lemma, Example, Plain };

pub const Item = struct {
    kind: ItemKind,
    /// Explicit name, or null when unnamed.
    name: ?[]const u8,
    form: ast.RussianForm,
    line: u32,
    col: u32,
};

pub const Error = lexer.Error;

pub fn Result(comptime T: type) type {
    return union(enum) { ok: T, err: Error };
}

const ParseError = error{ Syntax, OutOfMemory };

pub const Parser = struct {
    arena: std.mem.Allocator,
    toks: []const Token,
    pos: usize = 0,
    err: ?Error = null,
    depth: u32 = 0,

    const max_depth = 512;

    fn peek(self: *const Parser) Token {
        return if (self.pos < self.toks.len) self.toks[self.pos] else self.toks[self.toks.len - 1];
    }
    fn peekTag(self: *const Parser) Tag {
        return self.peek().tag;
    }
    fn advance(self: *Parser) Token {
        const t = self.peek();
        if (self.pos < self.toks.len) self.pos += 1;
        return t;
    }

    fn fail(self: *Parser, t: Token, comptime fmt: []const u8, args: anytype) ParseError {
        if (self.err == null) {
            self.err = .{ .message = std.fmt.allocPrint(self.arena, fmt, args) catch "out of memory", .line = t.line, .col = t.col };
        }
        return error.Syntax;
    }

    fn describe(t: Token) []const u8 {
        return if (t.tag == .Eof) "end of input" else t.text;
    }

    fn expect(self: *Parser, tag: Tag) ParseError!Token {
        const t = self.advance();
        if (t.tag != tag) return self.fail(t, "expected {s}, got {s} '{s}'", .{ @tagName(tag), @tagName(t.tag), describe(t) });
        return t;
    }

    fn enter(self: *Parser) ParseError!void {
        self.depth += 1;
        if (self.depth > max_depth) return self.fail(self.peek(), "recursion limit reached", .{});
    }
    fn leave(self: *Parser) void {
        self.depth -= 1;
    }

    fn box(self: *Parser, v: anytype) ParseError!*const @TypeOf(v) {
        return ast.box(self.arena, v) catch error.OutOfMemory;
    }

    fn expectIdent(self: *Parser, after: []const u8) ParseError![]const u8 {
        const t = self.advance();
        if (t.tag != .Ident) return self.fail(t, "expected ident after {s}, got {s} '{s}'", .{ after, @tagName(t.tag), describe(t) });
        return t.text;
    }

    // ---------------------------------------------------------------- terms

    pub fn parseTerm(self: *Parser) ParseError!ast.Term {
        return self.parseTermBinop(0);
    }

    fn binopPrec(op: ast.BinOp) u8 {
        return switch (op) {
            .Mul, .Div, .Mod => 7,
            .Add, .Sub => 6,
            .Lt, .Le, .Gt, .Ge => 4,
            .Eq, .Ne => 3,
        };
    }

    fn parseTermBinop(self: *Parser, min_prec: u8) ParseError!ast.Term {
        try self.enter();
        defer self.leave();
        var lhs = try self.parseTermApp();
        while (true) {
            const op: ast.BinOp = switch (self.peekTag()) {
                .Plus => .Add,
                .Minus => .Sub,
                .Star => .Mul,
                .Slash => .Div,
                .Percent => .Mod,
                else => break,
            };
            const prec = binopPrec(op);
            if (prec < min_prec) break;
            _ = self.advance();
            const rhs = try self.parseTermBinop(prec + 1);
            const lp = try self.box(lhs);
            const rp = try self.box(rhs);
            lhs = .{ .BinOp = .{ .op = op, .lhs = lp, .rhs = rp } };
        }
        return lhs;
    }

    fn startsAtom(tag: Tag) bool {
        return switch (tag) {
            .Ident, .Number, .LParen, .BoolLit, .StringLit => true,
            else => false,
        };
    }

    fn parseTermApp(self: *Parser) ParseError!ast.Term {
        const head_tag = self.peekTag();
        var t = try self.parseTermAtom();
        if (head_tag != .Ident) return t;
        while (startsAtom(self.peekTag())) {
            const arg = try self.parseTermAtom();
            const fp = try self.box(t);
            const ap = try self.box(arg);
            t = .{ .App = .{ .func = fp, .arg = ap } };
        }
        return t;
    }

    fn parseTermAtom(self: *Parser) ParseError!ast.Term {
        try self.enter();
        defer self.leave();
        const t = self.peek();
        switch (t.tag) {
            .Ident => {
                _ = self.advance();
                return .{ .Var = t.text };
            },
            .Number => {
                _ = self.advance();
                return .{ .Const = .{ .Number = t.number } };
            },
            .BoolLit => {
                _ = self.advance();
                return .{ .Const = .{ .Bool = t.boolean } };
            },
            .StringLit => {
                _ = self.advance();
                return .{ .Const = .{ .Str = t.text } };
            },
            .LParen => {
                _ = self.advance();
                if (self.peekTag() == .RParen) {
                    _ = self.advance();
                    return .Nil;
                }
                const first = try self.parseTerm();
                if (self.peekTag() == .Comma) {
                    var elems: std.ArrayList(ast.Term) = .empty;
                    try elems.append(self.arena, first);
                    while (self.peekTag() == .Comma) {
                        _ = self.advance();
                        try elems.append(self.arena, try self.parseTerm());
                    }
                    _ = try self.expect(.RParen);
                    return .{ .Tuple = try elems.toOwnedSlice(self.arena) };
                }
                _ = try self.expect(.RParen);
                return .{ .Paren = try self.box(first) };
            },
            .Fun => {
                _ = self.advance();
                const param = try self.expectIdent("fun");
                _ = try self.expect(.Colon);
                const sort = try self.parseSort();
                _ = try self.expect(.FatArrow);
                const body = try self.parseTerm();
                return .{ .Lambda = .{ .param = param, .sort = sort, .body = try self.box(body) } };
            },
            .If => {
                _ = self.advance();
                const cond = try self.parseFormula();
                _ = try self.expect(.Then);
                const then = try self.parseTerm();
                _ = try self.expect(.Else);
                const else_ = try self.parseTerm();
                return .{ .IfThenElse = .{ .cond = try self.box(cond), .then = try self.box(then), .else_ = try self.box(else_) } };
            },
            .Rec => {
                _ = self.advance();
                const name = try self.expectIdent("rec");
                _ = try self.expect(.Eq);
                const body = try self.parseTerm();
                return .{ .Rec = .{ .name = name, .body = try self.box(body) } };
            },
            else => return self.fail(t, "unexpected token in term: {s} '{s}'", .{ @tagName(t.tag), describe(t) }),
        }
    }

    // ---------------------------------------------------------------- sorts

    pub fn parseSort(self: *Parser) ParseError!ast.Sort {
        try self.enter();
        defer self.leave();
        const t = self.advance();
        var base: ast.Sort = switch (t.tag) {
            .Ident => blk: {
                const map = std.StaticStringMap(ast.Sort).initComptime(.{
                    .{ "Prop", .Prop },       .{ "Type", .Type },         .{ "Nat", .Nat },
                    .{ "Int", .Int },         .{ "Bool", .Bool },         .{ "State", .State },
                    .{ "Formula", .Formula }, .{ "Term", .Term },         .{ "MIR", .MIR },
                    .{ "Core", .Core },       .{ "Haskell", .Haskell },   .{ "Rust", .Rust },
                    .{ "Z3Expr", .Z3Expr },   .{ "LeanTerm", .LeanTerm }, .{ "SASAbs", .SASAbs },
                });
                break :blk map.get(t.text) orelse .{ .User = t.text };
            },
            .LParen => blk: {
                const s = try self.parseSort();
                _ = try self.expect(.RParen);
                break :blk s;
            },
            else => return self.fail(t, "unexpected token in sort: {s} '{s}'", .{ @tagName(t.tag), describe(t) }),
        };
        while (self.peekTag() == .Arrow) {
            _ = self.advance();
            const rhs = try self.parseSort();
            const bp = try self.box(base);
            const rp = try self.box(rhs);
            base = .{ .Arrow = .{ .from = bp, .to = rp } };
        }
        return base;
    }

    // ------------------------------------------------------------- formulas

    pub fn parseFormula(self: *Parser) ParseError!ast.Formula {
        try self.enter();
        defer self.leave();
        var lhs = try self.parseFormulaImplies();
        while (self.peekTag() == .Iff or self.peekTag() == .DoubleArrow) {
            _ = self.advance();
            const rhs = try self.parseFormulaImplies();
            const lp = try self.box(lhs);
            const rp = try self.box(rhs);
            lhs = .{ .Iff = .{ .lhs = lp, .rhs = rp } };
        }
        return lhs;
    }

    fn parseFormulaImplies(self: *Parser) ParseError!ast.Formula {
        var lhs = try self.parseFormulaOr();
        while (self.peekTag() == .Implies or self.peekTag() == .Arrow) {
            _ = self.advance();
            const rhs = try self.parseFormulaOr();
            const lp = try self.box(lhs);
            const rp = try self.box(rhs);
            lhs = .{ .Implies = .{ .lhs = lp, .rhs = rp } };
        }
        return lhs;
    }

    fn parseFormulaOr(self: *Parser) ParseError!ast.Formula {
        var lhs = try self.parseFormulaAnd();
        while (self.peekTag() == .Or) {
            _ = self.advance();
            const rhs = try self.parseFormulaAnd();
            const pair = try self.arena.dupe(ast.Formula, &.{ lhs, rhs });
            lhs = .{ .Or = pair };
        }
        return lhs;
    }

    fn parseFormulaAnd(self: *Parser) ParseError!ast.Formula {
        var lhs = try self.parseFormulaAtom();
        while (self.peekTag() == .And) {
            _ = self.advance();
            const rhs = try self.parseFormulaAtom();
            const pair = try self.arena.dupe(ast.Formula, &.{ lhs, rhs });
            lhs = .{ .And = pair };
        }
        return lhs;
    }

    fn binder(self: *Parser, what: []const u8) ParseError!struct { []const u8, ast.Sort, ast.Formula } {
        const v = try self.expectIdent(what);
        _ = try self.expect(.Colon);
        const sort = try self.parseSort();
        _ = try self.expect(.Dot);
        const body = try self.parseFormula();
        return .{ v, sort, body };
    }

    fn parseFormulaAtom(self: *Parser) ParseError!ast.Formula {
        try self.enter();
        defer self.leave();
        const t = self.peek();
        switch (t.tag) {
            .Not => {
                _ = self.advance();
                const f = try self.parseFormulaAtom();
                return .{ .Not = try self.box(f) };
            },
            .Forall, .Exists => {
                _ = self.advance();
                const b = try self.binder(if (t.tag == .Forall) "forall" else "exists");
                const body = try self.box(b[2]);
                return if (t.tag == .Forall)
                    .{ .Forall = .{ .var_ = b[0], .sort = b[1], .body = body } }
                else
                    .{ .Exists = .{ .var_ = b[0], .sort = b[1], .body = body } };
            },
            .Mu, .Nu => {
                _ = self.advance();
                const v = try self.expectIdent(if (t.tag == .Mu) "μ" else "ν");
                _ = try self.expect(.Dot);
                const body = try self.box(try self.parseFormula());
                return if (t.tag == .Mu) .{ .Mu = .{ .var_ = v, .body = body } } else .{ .Nu = .{ .var_ = v, .body = body } };
            },
            .LParen => {
                const save = self.pos;
                const save_err = self.err;
                _ = self.advance();
                if (self.parseFormula()) |f| {
                    if (self.peekTag() == .RParen) {
                        _ = self.advance();
                        // `(a + b) = c`: the parenthesis was a term after all.
                        if (!isRelation(self.peekTag())) return .{ .Paren = try self.box(f) };
                    }
                } else |e| if (e == error.OutOfMemory) return e;
                self.pos = save;
                self.err = save_err;
                return self.relational();
            },
            .BoolLit => {
                // `true = x` is a relation; a lone ⊤/⊥ is an atomic constant.
                if (isRelation(self.toks[@min(self.pos + 1, self.toks.len - 1)].tag)) return self.relational();
                _ = self.advance();
                return .{ .Atomic = if (t.boolean) .True else .False };
            },
            .Ravno, .Imply, .Conj, .Disj, .Neg, .DlyaVsekh, .Sushchestvuet, .Rekursiya, .Sila => {
                const form = try self.parseRussianForm();
                return lowerToFormula(self, form);
            },
            else => return self.relational(),
        }
    }

    fn isRelation(tag: Tag) bool {
        return switch (tag) {
            .Eq, .Ne, .Lt, .Le, .Gt, .Ge => true,
            else => false,
        };
    }

    fn relational(self: *Parser) ParseError!ast.Formula {
        const start = self.peek();
        const lhs = try self.parseTerm();
        const op = self.peekTag();
        if (!isRelation(op)) {
            // A bare identifier (or application of one) is a predicate.
            switch (lhs) {
                .Var => |name| return .{ .Atomic = .{ .Predicate = .{ .name = name, .args = &.{} } } },
                .App => {
                    var args: std.ArrayList(ast.Term) = .empty;
                    var cur = lhs;
                    while (cur == .App) {
                        try args.insert(self.arena, 0, cur.App.arg.*);
                        cur = cur.App.func.*;
                    }
                    if (cur == .Var) return .{ .Atomic = .{ .Predicate = .{ .name = cur.Var, .args = try args.toOwnedSlice(self.arena) } } };
                    return self.fail(start, "unexpected term in formula position", .{});
                },
                else => return self.fail(start, "unexpected term in formula position", .{}),
            }
        }
        _ = self.advance();
        const rhs = try self.parseTerm();
        const args = try self.arena.dupe(ast.Term, &.{ lhs, rhs });
        return switch (op) {
            .Eq => .{ .Eq = .{ .lhs = lhs, .rhs = rhs } },
            .Ne => .{ .Not = try self.box(ast.Formula{ .Eq = .{ .lhs = lhs, .rhs = rhs } }) },
            .Lt => .{ .Atomic = .{ .Predicate = .{ .name = "<", .args = args } } },
            .Le => .{ .Atomic = .{ .Predicate = .{ .name = "≤", .args = args } } },
            .Gt => .{ .Atomic = .{ .Predicate = .{ .name = ">", .args = args } } },
            .Ge => .{ .Atomic = .{ .Predicate = .{ .name = "≥", .args = args } } },
            else => unreachable,
        };
    }

    // ---------------------------------------------------------------- states

    pub fn parseState(self: *Parser) ParseError!ast.State {
        try self.enter();
        defer self.leave();
        const t = self.advance();
        var st: ast.State = blk: {
            if (t.tag == .Ident) {
                const s = t.text;
                if (std.mem.eql(u8, s, "S")) {
                    if (self.peekTag() == .Number) {
                        const n = self.advance();
                        break :blk .{ .Sn = std.math.cast(u32, n.number) orelse return self.fail(n, "state index out of range", .{}) };
                    }
                    break :blk .S;
                }
                if (std.mem.eql(u8, s, "S0") or std.mem.eql(u8, s, "S₀")) break :blk .S0;
                if (s.len > 1 and s[0] == 'S') {
                    const n = std.fmt.parseInt(u32, s[1..], 10) catch return self.fail(t, "invalid state name: {s}", .{s});
                    break :blk .{ .Sn = n };
                }
            }
            return self.fail(t, "unexpected token in state: {s} '{s}'", .{ @tagName(t.tag), describe(t) });
        };
        // Optional updates: S[x := 1] and primes S' are written in the IR,
        // the surface syntax for them is `S[x := t]`.
        while (self.peekTag() == .LBracket) {
            _ = self.advance();
            const v = try self.expectIdent("[");
            _ = try self.expect(.Colon);
            _ = try self.expect(.Eq);
            const val = try self.parseTerm();
            _ = try self.expect(.RBracket);
            const sp = try self.box(st);
            st = .{ .Bind = .{ .base = sp, .binding = .{ .var_ = v, .value = val, .kind = .Assign } } };
        }
        return st;
    }

    fn parseBackend(self: *Parser) ParseError!ast.Backend {
        const t = self.advance();
        if (t.tag == .Ident) {
            if (std.mem.eql(u8, t.text, "GHC")) return .{ .GHC = .{ .module_name = "Main", .decls = &.{} } };
            if (std.mem.eql(u8, t.text, "Kani")) return .{ .Kani = ast.defaultKani() };
        }
        return self.fail(t, "expected backend GHC or Kani, got '{s}'", .{describe(t)});
    }

    // ---------------------------------------------------------- Russian forms

    pub fn parseRussianForm(self: *Parser) ParseError!ast.RussianForm {
        try self.enter();
        defer self.leave();
        const t = self.peek();
        switch (t.tag) {
            .Ravno => {
                _ = self.advance();
                _ = try self.expect(.LParen);
                const a = try self.parseTerm();
                _ = try self.expect(.Comma);
                const b = try self.parseTerm();
                _ = try self.expect(.RParen);
                return .{ .Ravnostvo = .{ .lhs = a, .rhs = b } };
            },
            .Imply, .Conj, .Disj => {
                _ = self.advance();
                _ = try self.expect(.LParen);
                const a = try self.parseFormula();
                _ = try self.expect(.Comma);
                const b = try self.parseFormula();
                _ = try self.expect(.RParen);
                return switch (t.tag) {
                    .Imply => .{ .Implikatsiya = .{ .lhs = a, .rhs = b } },
                    .Conj => .{ .Konyunktsiya = .{ .lhs = a, .rhs = b } },
                    else => .{ .Dizyunktsiya = .{ .lhs = a, .rhs = b } },
                };
            },
            .Neg => {
                _ = self.advance();
                _ = try self.expect(.LParen);
                const a = try self.parseFormula();
                _ = try self.expect(.RParen);
                return .{ .Otritsanie = a };
            },
            .DlyaVsekh, .Sushchestvuet => {
                _ = self.advance();
                const b = try self.binder(if (t.tag == .DlyaVsekh) "для_всех" else "существует");
                return if (t.tag == .DlyaVsekh)
                    .{ .DlyaVsekh = .{ .var_ = b[0], .sort = b[1], .body = b[2] } }
                else
                    .{ .Sushchestvuet = .{ .var_ = b[0], .sort = b[1], .body = b[2] } };
            },
            .Rekursiya => {
                _ = self.advance();
                const v = try self.expectIdent("рекурсия");
                _ = try self.expect(.Dot);
                return .{ .Rekursiya = .{ .var_ = v, .body = try self.parseFormula() } };
            },
            .Sostoyanie => {
                _ = self.advance();
                return .{ .Sostoyanie = try self.parseState() };
            },
            .Sila => {
                _ = self.advance();
                _ = try self.expect(.LParen);
                const st = try self.parseState();
                _ = try self.expect(.Comma);
                const f = try self.parseFormula();
                _ = try self.expect(.RParen);
                return .{ .Sila = .{ .state = st, .formula = f } };
            },
            .Omega => {
                _ = self.advance();
                _ = try self.expect(.LParen);
                const b = try self.parseBackend();
                _ = try self.expect(.Comma);
                const st = try self.parseState();
                _ = try self.expect(.Comma);
                const f = try self.parseFormula();
                _ = try self.expect(.RParen);
                return .{ .Omega = .{ .backend = b, .state = st, .formula = f } };
            },
            .Dokazatelstvo => {
                _ = self.advance();
                return .{ .Dokazatelstvo = .{ .obligations = &.{} } };
            },
            else => return self.fail(t, "unexpected Russian form: {s} '{s}'", .{ @tagName(t.tag), describe(t) }),
        }
    }

    fn isFormKeyword(tag: Tag) bool {
        return switch (tag) {
            .Ravno, .Imply, .Conj, .Disj, .Neg, .DlyaVsekh, .Sushchestvuet, .Rekursiya, .Sostoyanie, .Sila, .Omega, .Dokazatelstvo => true,
            else => false,
        };
    }

    fn itemEnd(tag: Tag) bool {
        return tag == .Semicolon or tag == .Eof;
    }

    /// One top-level item body: a Russian form, or a bare formula.
    fn parseBody(self: *Parser) ParseError!ast.RussianForm {
        if (isFormKeyword(self.peekTag())) {
            const save = self.pos;
            const save_err = self.err;
            if (self.parseRussianForm()) |form| {
                if (itemEnd(self.peekTag())) return form;
            } else |e| {
                if (e == error.OutOfMemory) return e;
                const tag = self.toks[save].tag;
                if (tag == .Sostoyanie or tag == .Omega or tag == .Dokazatelstvo) return e;
            }
            self.pos = save;
            self.err = save_err;
        }
        return .{ .Bare = try self.parseFormula() };
    }

    pub fn parseProgram(self: *Parser) ParseError![]const Item {
        var items: std.ArrayList(Item) = .empty;
        while (true) {
            while (self.peekTag() == .Semicolon) _ = self.advance();
            if (self.peekTag() == .Eof) break;
            const start = self.peek();
            var kind: ItemKind = .Plain;
            var name: ?[]const u8 = null;
            switch (start.tag) {
                .Theorem, .Lemma, .Example => {
                    _ = self.advance();
                    kind = switch (start.tag) {
                        .Theorem => .Theorem,
                        .Lemma => .Lemma,
                        else => .Example,
                    };
                    if (self.peekTag() == .Ident) name = self.advance().text;
                    _ = try self.expect(.Colon);
                },
                else => {},
            }
            const form = try self.parseBody();
            try items.append(self.arena, .{ .kind = kind, .name = name, .form = form, .line = start.line, .col = start.col });
            const end = self.peek();
            if (end.tag == .Eof) break;
            if (end.tag != .Semicolon) return self.fail(end, "expected ';' or end of input after item, got {s} '{s}'", .{ @tagName(end.tag), describe(end) });
        }
        return items.toOwnedSlice(self.arena);
    }
};

/// The formula a Russian form denotes (same mapping as pipeline lowering).
fn lowerToFormula(p: *Parser, form: ast.RussianForm) ParseError!ast.Formula {
    return switch (form) {
        .Ravnostvo => |r| .{ .Eq = .{ .lhs = r.lhs, .rhs = r.rhs } },
        .Implikatsiya => |r| .{ .Implies = .{ .lhs = try p.box(r.lhs), .rhs = try p.box(r.rhs) } },
        .Konyunktsiya => |r| .{ .And = try p.arena.dupe(ast.Formula, &.{ r.lhs, r.rhs }) },
        .Dizyunktsiya => |r| .{ .Or = try p.arena.dupe(ast.Formula, &.{ r.lhs, r.rhs }) },
        .Otritsanie => |a| .{ .Not = try p.box(a) },
        .DlyaVsekh => |r| .{ .Forall = .{ .var_ = r.var_, .sort = r.sort, .body = try p.box(r.body) } },
        .Sushchestvuet => |r| .{ .Exists = .{ .var_ = r.var_, .sort = r.sort, .body = try p.box(r.body) } },
        .Rekursiya => |r| .{ .Mu = .{ .var_ = r.var_, .body = try p.box(r.body) } },
        .Sila => |r| .{ .Sila = .{ .state = r.state, .formula = try p.box(r.formula) } },
        else => ast.true_formula,
    };
}

fn run(comptime T: type, arena: std.mem.Allocator, src: []const u8, comptime f: fn (*Parser) ParseError!T) !Result(T) {
    const lx = try lexer.tokenize(arena, src);
    const toks = switch (lx) {
        .ok => |t| t,
        .err => |e| return .{ .err = e },
    };
    var p: Parser = .{ .arena = arena, .toks = toks };
    const v = f(&p) catch |e| switch (e) {
        error.OutOfMemory => return error.OutOfMemory,
        error.Syntax => return .{ .err = p.err.? },
    };
    return .{ .ok = v };
}

fn wholeForm(p: *Parser) ParseError!ast.RussianForm {
    const f = try p.parseRussianForm();
    if (p.peekTag() != .Eof) return p.fail(p.peek(), "trailing input after form: '{s}'", .{Parser.describe(p.peek())});
    return f;
}
fn wholeFormula(p: *Parser) ParseError!ast.Formula {
    const f = try p.parseFormula();
    if (p.peekTag() != .Eof) return p.fail(p.peek(), "trailing input after formula: '{s}'", .{Parser.describe(p.peek())});
    return f;
}
fn wholeTerm(p: *Parser) ParseError!ast.Term {
    const t = try p.parseTerm();
    if (p.peekTag() != .Eof) return p.fail(p.peek(), "trailing input after term: '{s}'", .{Parser.describe(p.peek())});
    return t;
}

/// Rust `parse_russian`.
pub fn parseRussian(arena: std.mem.Allocator, src: []const u8) !Result(ast.RussianForm) {
    return run(ast.RussianForm, arena, src, wholeForm);
}
/// Rust `parse_formula`.
pub fn parseFormula(arena: std.mem.Allocator, src: []const u8) !Result(ast.Formula) {
    return run(ast.Formula, arena, src, wholeFormula);
}
/// Rust `parse_term`.
pub fn parseTerm(arena: std.mem.Allocator, src: []const u8) !Result(ast.Term) {
    return run(ast.Term, arena, src, wholeTerm);
}
/// A whole CRUX source file.
pub fn parseProgram(arena: std.mem.Allocator, src: []const u8) !Result([]const Item) {
    return run([]const Item, arena, src, Parser.parseProgram);
}

// ------------------------------------------------------------------- tests

const testing = std.testing;

fn dumpStr(a: std.mem.Allocator, v: anytype) ![]u8 {
    return ast.dumpAlloc(a, v);
}

test "parser: равенство(x + 1, 1 + x)" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const r = try parseRussian(a, "равенство(x + 1, 1 + x)");
    try testing.expectEqualStrings(
        "Ravnostvo { lhs: BinOp { op: Add, lhs: Var(\"x\"), rhs: Const(Number(1)) }, rhs: BinOp { op: Add, lhs: Const(Number(1)), rhs: Var(\"x\") } }",
        try dumpStr(a, r.ok),
    );
}

test "parser: precedence, application, relations" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const t = try parseTerm(a, "1 + 2 * 3");
    try testing.expectEqualStrings("BinOp { op: Add, lhs: Const(Number(1)), rhs: BinOp { op: Mul, lhs: Const(Number(2)), rhs: Const(Number(3)) } }", try dumpStr(a, t.ok));
    const app = try parseTerm(a, "f x y");
    try testing.expectEqualStrings("App { func: App { func: Var(\"f\"), arg: Var(\"x\") }, arg: Var(\"y\") }", try dumpStr(a, app.ok));
    const f = try parseFormula(a, "x < y ∧ y ≤ z ∨ ¬ (x = z)");
    try testing.expect(f.ok == .Or);
    try testing.expect(f.ok.Or[0] == .And);
    const g = try parseFormula(a, "(x + 1) = 2");
    try testing.expect(g.ok == .Eq);
    const h = try parseFormula(a, "x ≠ 3");
    try testing.expect(h.ok == .Not);
}

test "parser: quantifiers, fixed points, iff" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const f = try parseFormula(a, "∀ x : Int. ∃ y : Int. y = x + 1");
    try testing.expect(f.ok == .Forall);
    try testing.expect(f.ok.Forall.body.* == .Exists);
    const m = try parseFormula(a, "mu X. X ↔ true");
    try testing.expect(m.ok == .Mu);
    try testing.expect(m.ok.Mu.body.* == .Iff);
    const s = try parseFormula(a, "∀ f : Int → Int. f 0 = f 0");
    try testing.expect(s.ok.Forall.sort == .Arrow);
}

test "parser: all twelve Russian forms" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const cases = [_]struct { []const u8, std.meta.Tag(ast.RussianForm) }{
        .{ "равенство(a, b)", .Ravnostvo },
        .{ "импликация(x = 1, x > 0)", .Implikatsiya },
        .{ "конъюнкция(true, x = x)", .Konyunktsiya },
        .{ "дизъюнкция(x = 1, x = 2)", .Dizyunktsiya },
        .{ "отрицание(x = 1)", .Otritsanie },
        .{ "для_всех x : Int. x = x", .DlyaVsekh },
        .{ "существует x : Int. x = 2", .Sushchestvuet },
        .{ "рекурсия X. X", .Rekursiya },
        .{ "состояние S3", .Sostoyanie },
        .{ "сила(S0, x = x)", .Sila },
        .{ "омега(Kani, S 2, x + 0 = x)", .Omega },
        .{ "доказательство", .Dokazatelstvo },
    };
    for (cases) |c| {
        const r = try parseRussian(a, c[0]);
        try testing.expectEqual(c[1], std.meta.activeTag(r.ok));
    }
    const s = try parseRussian(a, "состояние S 7");
    try testing.expectEqual(@as(u32, 7), s.ok.Sostoyanie.Sn);
}

test "parser: program items and errors with line:col" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const r = try parseProgram(a, "theorem t1 : равенство(1, 1);\nсила(S1, x = x);\nx + 1 = 1 + x");
    try testing.expectEqual(@as(usize, 3), r.ok.len);
    try testing.expectEqualStrings("t1", r.ok[0].name.?);
    try testing.expect(r.ok[2].form == .Bare);
    try testing.expectEqual(@as(u32, 2), r.ok[1].line);
    const e = try parseProgram(a, "равенство(1, 1);\nсила(S1 x = x)");
    try testing.expectEqual(@as(u32, 2), e.err.line);
    try testing.expectEqual(@as(u32, 9), e.err.col);
    const e2 = try parseProgram(a, "омега(Foo, S, true)");
    try testing.expectEqual(@as(u32, 7), e2.err.col);
}
