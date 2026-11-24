// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! Russian-syntax lexer (port of russian.rs section 2 / Crux.Russian tokenize).
//!
//! Keyword spellings: the Rust source arrived as mojibake (UTF-8 read as
//! Windows-1252, with the undefined bytes 0x81/0x8F/0x8D/0x90/0x9D dropped or
//! turned into spaces). Re-encoding each string to cp1252 and decoding as UTF-8
//! recovers every letter except the dropped ones; those were restored from the
//! surrounding Russian word, cross-checked against the Lean port:
//!   равенство импликация конъюнкция дизъюнкция отрицание для_всех
//!   существует рекурсия состояние сила омега доказательство
//! `для_всех` keeps the underscore that survives in the Rust bytes (the Lean
//! port's "для всех" contains a space and can never be produced by the lexer).

const std = @import("std");

pub const Tag = enum {
    // Russian keywords
    Ravno,
    Imply,
    Conj,
    Disj,
    Neg,
    DlyaVsekh,
    Sushchestvuet,
    Rekursiya,
    Sostoyanie,
    Sila,
    Omega,
    Dokazatelstvo,
    // English keywords
    Let,
    In,
    If,
    Then,
    Else,
    Match,
    With,
    Fold,
    Rec,
    Fun,
    Theorem,
    Lemma,
    Example,
    Proof,
    QED,
    By,
    Sorry,
    // Delimiters
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Semicolon,
    Dot,
    Colon,
    Pipe,
    Arrow,
    DoubleArrow,
    FatArrow,
    // Operators
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Cons,
    Concat,
    And,
    Or,
    Not,
    Implies,
    Iff,
    Forall,
    Exists,
    Mu,
    Nu,
    // Literals and identifiers
    Ident,
    Number,
    BoolLit,
    StringLit,
    Eof,
};

pub const Token = struct {
    tag: Tag,
    /// Identifier name, string literal contents, or source text of the token.
    text: []const u8 = "",
    number: i64 = 0,
    boolean: bool = false,
    line: u32 = 1,
    col: u32 = 1,
};

pub const Error = struct {
    message: []const u8,
    line: u32,
    col: u32,
};

pub const LexResult = union(enum) {
    ok: []const Token,
    err: Error,
};

const keywords = std.StaticStringMap(Tag).initComptime(.{
    .{ "равенство", .Ravno },
    .{ "импликация", .Imply },
    .{ "конъюнкция", .Conj },
    .{ "дизъюнкция", .Disj },
    .{ "отрицание", .Neg },
    .{ "для_всех", .DlyaVsekh },
    .{ "существует", .Sushchestvuet },
    .{ "рекурсия", .Rekursiya },
    .{ "состояние", .Sostoyanie },
    .{ "сила", .Sila },
    .{ "омега", .Omega },
    .{ "доказательство", .Dokazatelstvo },
    .{ "let", .Let },
    .{ "in", .In },
    .{ "if", .If },
    .{ "then", .Then },
    .{ "else", .Else },
    .{ "match", .Match },
    .{ "with", .With },
    .{ "fold", .Fold },
    .{ "rec", .Rec },
    .{ "fun", .Fun },
    .{ "theorem", .Theorem },
    .{ "lemma", .Lemma },
    .{ "example", .Example },
    .{ "proof", .Proof },
    .{ "QED", .QED },
    .{ "by", .By },
    .{ "sorry", .Sorry },
    .{ "and", .And },
    .{ "or", .Or },
    .{ "not", .Not },
    .{ "implies", .Implies },
    .{ "iff", .Iff },
    // From the Lean port's keyword table.
    .{ "forall", .Forall },
    .{ "exists", .Exists },
    .{ "mu", .Mu },
    .{ "nu", .Nu },
    .{ "μ", .Mu },
    .{ "ν", .Nu },
});

fn isAsciiDigit(c: u21) bool {
    return c >= '0' and c <= '9';
}

fn isLetter(c: u21) bool {
    return (c >= 'a' and c <= 'z') or (c >= 'A' and c <= 'Z') or
        (c >= 0x00C0 and c <= 0x024F and c != 0x00D7 and c != 0x00F7) or
        (c >= 0x0370 and c <= 0x03FF) or // Greek
        (c >= 0x0400 and c <= 0x04FF); // Cyrillic
}

/// Identifier continuation: Rust `is_alphanumeric() || '_' || '\''`, plus the
/// Greek and Cyrillic blocks; subscript digits ₀..₉ count as numeric.
fn isIdentChar(c: u21) bool {
    return isLetter(c) or isAsciiDigit(c) or c == '_' or c == '\'' or (c >= 0x2080 and c <= 0x2089);
}

pub const Lexer = struct {
    src: []const u8,
    pos: usize = 0,
    line: u32 = 1,
    col: u32 = 1,

    fn peekAt(self: *const Lexer, off: usize) ?u21 {
        var p = self.pos;
        var k: usize = 0;
        while (p < self.src.len) {
            const n = std.unicode.utf8ByteSequenceLength(self.src[p]) catch return null;
            if (p + n > self.src.len) return null;
            if (k == off) return std.unicode.utf8Decode(self.src[p .. p + n]) catch null;
            p += n;
            k += 1;
        }
        return null;
    }

    fn peek(self: *const Lexer) ?u21 {
        return self.peekAt(0);
    }

    fn advance(self: *Lexer) ?u21 {
        if (self.pos >= self.src.len) return null;
        const n = std.unicode.utf8ByteSequenceLength(self.src[self.pos]) catch 1;
        const c = self.peek();
        self.pos += @min(n, self.src.len - self.pos);
        if (c == '\n') {
            self.line += 1;
            self.col = 1;
        } else self.col += 1;
        return c;
    }

    fn skipTrivia(self: *Lexer) void {
        while (true) {
            while (self.peek()) |c| {
                if (c == ' ' or c == '\t' or c == '\n' or c == '\r' or c == 0x0B or c == 0x0C or c == 0x00A0) {
                    _ = self.advance();
                } else break;
            }
            // `--` line comment
            if (self.peek() == '-' and self.peekAt(1) == '-') {
                while (self.advance()) |c| if (c == '\n') break;
                continue;
            }
            break;
        }
    }

    pub fn tokenize(self: *Lexer, arena: std.mem.Allocator) !LexResult {
        var toks: std.ArrayList(Token) = .empty;
        if (!std.unicode.utf8ValidateSlice(self.src)) {
            return .{ .err = .{ .message = "source is not valid UTF-8", .line = 1, .col = 1 } };
        }
        while (true) {
            self.skipTrivia();
            const line = self.line;
            const col = self.col;
            const start = self.pos;
            const c = self.peek() orelse {
                try toks.append(arena, .{ .tag = .Eof, .line = line, .col = col });
                break;
            };
            var tok: Token = .{ .tag = .Eof, .line = line, .col = col };
            switch (c) {
                '(' => tok.tag = .LParen,
                ')' => tok.tag = .RParen,
                '[' => tok.tag = .LBracket,
                ']' => tok.tag = .RBracket,
                '{' => tok.tag = .LBrace,
                '}' => tok.tag = .RBrace,
                ',' => tok.tag = .Comma,
                ';' => tok.tag = .Semicolon,
                '.' => tok.tag = .Dot,
                ':' => tok.tag = .Colon,
                '|' => tok.tag = .Pipe,
                '+' => tok.tag = .Plus,
                '%' => tok.tag = .Percent,
                '*' => tok.tag = .Star,
                '/' => tok.tag = .Slash,
                0x2192 => tok.tag = .Arrow, // →
                0x2194 => tok.tag = .DoubleArrow, // ↔
                0x2200 => tok.tag = .Forall, // ∀
                0x2203 => tok.tag = .Exists, // ∃
                0x2227 => tok.tag = .And, // ∧
                0x2228 => tok.tag = .Or, // ∨
                0x00AC => tok.tag = .Not, // ¬
                0x2261 => tok.tag = .Eq, // ≡
                0x2264 => tok.tag = .Le, // ≤
                0x2265 => tok.tag = .Ge, // ≥
                0x2260 => tok.tag = .Ne, // ≠
                0x22A2, 0x22A8 => tok.tag = .Not, // ⊢ ⊨ (placeholders in the source)
                0x22A4 => {
                    tok.tag = .BoolLit;
                    tok.boolean = true;
                }, // ⊤
                0x22A5 => {
                    tok.tag = .BoolLit;
                    tok.boolean = false;
                }, // ⊥
                0x21A6 => tok.tag = .FatArrow, // ↦
                else => {},
            }
            if (tok.tag != .Eof) {
                _ = self.advance();
                tok.text = self.src[start..self.pos];
                try toks.append(arena, tok);
                continue;
            }
            switch (c) {
                '=' => {
                    _ = self.advance();
                    tok.tag = .Eq;
                    if (self.peek() == '=') {
                        _ = self.advance();
                    } else if (self.peek() == '>') {
                        _ = self.advance();
                        tok.tag = .FatArrow;
                    }
                },
                '!' => {
                    _ = self.advance();
                    tok.tag = .Not;
                    if (self.peek() == '=') {
                        _ = self.advance();
                        tok.tag = .Ne;
                    }
                },
                '<' => {
                    _ = self.advance();
                    tok.tag = .Lt;
                    if (self.peek() == '=') {
                        _ = self.advance();
                        tok.tag = .Le;
                    } else if (self.peek() == '-') {
                        _ = self.advance();
                        tok.tag = .Cons;
                    }
                },
                '>' => {
                    _ = self.advance();
                    tok.tag = .Gt;
                    if (self.peek() == '=') {
                        _ = self.advance();
                        tok.tag = .Ge;
                    }
                },
                '-' => {
                    _ = self.advance();
                    tok.tag = .Minus;
                    if (self.peek() == '>') {
                        _ = self.advance();
                        tok.tag = .Arrow;
                    }
                },
                '"' => {
                    _ = self.advance();
                    const s0 = self.pos;
                    var closed = false;
                    while (self.peek()) |ch| {
                        if (ch == '"') {
                            closed = true;
                            break;
                        }
                        _ = self.advance();
                    }
                    if (!closed) return .{ .err = .{ .message = "unterminated string literal", .line = line, .col = col } };
                    tok.tag = .StringLit;
                    tok.text = self.src[s0..self.pos];
                    _ = self.advance();
                    try toks.append(arena, tok);
                    continue;
                },
                else => {
                    if (isAsciiDigit(c)) {
                        var v: i64 = 0;
                        while (self.peek()) |d| {
                            if (!isAsciiDigit(d)) break;
                            _ = self.advance();
                            v = std.math.mul(i64, v, 10) catch return .{ .err = .{ .message = "integer literal out of range", .line = line, .col = col } };
                            v = std.math.add(i64, v, d - '0') catch return .{ .err = .{ .message = "integer literal out of range", .line = line, .col = col } };
                        }
                        tok.tag = .Number;
                        tok.number = v;
                    } else if (isLetter(c) or c == '_') {
                        while (self.peek()) |d| {
                            if (!isIdentChar(d)) break;
                            _ = self.advance();
                        }
                        const ident = self.src[start..self.pos];
                        tok.text = ident;
                        if (std.mem.eql(u8, ident, "true") or std.mem.eql(u8, ident, "false")) {
                            tok.tag = .BoolLit;
                            tok.boolean = ident[0] == 't';
                        } else {
                            tok.tag = keywords.get(ident) orelse .Ident;
                        }
                    } else {
                        var buf: [4]u8 = undefined;
                        const n = std.unicode.utf8Encode(c, &buf) catch 0;
                        const msg = try std.fmt.allocPrint(arena, "unexpected character '{s}' (U+{X:0>4})", .{ buf[0..n], c });
                        return .{ .err = .{ .message = msg, .line = line, .col = col } };
                    }
                },
            }
            if (tok.text.len == 0) tok.text = self.src[start..self.pos];
            try toks.append(arena, tok);
        }
        return .{ .ok = try toks.toOwnedSlice(arena) };
    }
};

pub fn tokenize(arena: std.mem.Allocator, src: []const u8) !LexResult {
    var lx: Lexer = .{ .src = src };
    return lx.tokenize(arena);
}

const testing = std.testing;

fn tagsOf(arena: std.mem.Allocator, src: []const u8) ![]Tag {
    const r = try tokenize(arena, src);
    const toks = r.ok;
    const out = try arena.alloc(Tag, toks.len);
    for (toks, 0..) |t, i| out[i] = t.tag;
    return out;
}

test "lexer: Russian keywords recovered from mojibake" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const tags = try tagsOf(a, "равенство импликация конъюнкция дизъюнкция отрицание для_всех существует рекурсия состояние сила омега доказательство");
    try testing.expectEqualSlices(Tag, &.{ .Ravno, .Imply, .Conj, .Disj, .Neg, .DlyaVsekh, .Sushchestvuet, .Rekursiya, .Sostoyanie, .Sila, .Omega, .Dokazatelstvo, .Eof }, tags);
}

test "lexer: unicode operators, ASCII operators, comments and positions" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const tags = try tagsOf(a, "→ ↔ ∀ ∃ ∧ ∨ ¬ ≡ ≤ ≥ ≠ ⊤ ⊥ ↦ -- comment\n == => != <= <- >= -> < > - + * / % ; : . , |");
    try testing.expectEqualSlices(Tag, &.{ .Arrow, .DoubleArrow, .Forall, .Exists, .And, .Or, .Not, .Eq, .Le, .Ge, .Ne, .BoolLit, .BoolLit, .FatArrow, .Eq, .FatArrow, .Ne, .Le, .Cons, .Ge, .Arrow, .Lt, .Gt, .Minus, .Plus, .Star, .Slash, .Percent, .Semicolon, .Colon, .Dot, .Comma, .Pipe, .Eof }, tags);
    const r = try tokenize(a, "x\n  сила");
    try testing.expectEqual(@as(u32, 2), r.ok[1].line);
    try testing.expectEqual(@as(u32, 3), r.ok[1].col);
    try testing.expectEqualStrings("x", r.ok[0].text);
}

test "lexer: literals and identifiers" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const r = try tokenize(a, "42 true false \"привет\" x' переменная S₀");
    const t = r.ok;
    try testing.expectEqual(Tag.Number, t[0].tag);
    try testing.expectEqual(@as(i64, 42), t[0].number);
    try testing.expect(t[1].boolean and !t[2].boolean);
    try testing.expectEqualStrings("привет", t[3].text);
    try testing.expectEqualStrings("x'", t[4].text);
    try testing.expectEqualStrings("переменная", t[5].text);
    try testing.expectEqualStrings("S₀", t[6].text);
}

test "lexer: errors carry line and column" {
    var st = std.heap.ArenaAllocator.init(testing.allocator);
    defer st.deinit();
    const a = st.allocator();
    const r = try tokenize(a, "x = 1\n  y @ 2");
    try testing.expectEqual(@as(u32, 2), r.err.line);
    try testing.expectEqual(@as(u32, 5), r.err.col);
    const r2 = try tokenize(a, "\"open");
    try testing.expectEqualStrings("unterminated string literal", r2.err.message);
}
