// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! Abjad matrix (port of GnosticArabic/AbjadMatrix.lean, with
//! rust/abjad_matrix.rs as reference): the 28 letters and their values,
//! Jamāl/Jalāl polarity, digit roots, the equilibrium constant, awfāq,
//! decoherence quadrants, the hieroglyph decoder, the Al-Ḥamīd master
//! constants and the Kenoma/Pleroma states. Names, values and functions follow
//! the source; WAFQ_ALLAH_3X3 and `verify` are kept as written there.
//!
//! `fromCodepoint` / `wordValue` (Arabic script to letters) are additions for
//! `crux abjad value`; the source has no text input.

const std = @import("std");

pub const ArabicLetter = enum {
    Alif,
    Ba,
    Jim,
    Dal,
    Ha,
    Waw,
    Zay,
    Ha_,
    Ta,
    Ya,
    Kaf,
    Lam,
    Mim,
    Nun,
    Sin,
    Ayn,
    Fa,
    Sad,
    Qaf,
    Ra,
    Shin,
    Ta_,
    Tha,
    Kha,
    Dhal,
    Dad,
    Za,
    Ghayn,

    pub fn abjadValue(self: ArabicLetter) u32 {
        return switch (self) {
            .Alif => 1,
            .Ba => 2,
            .Jim => 3,
            .Dal => 4,
            .Ha => 5,
            .Waw => 6,
            .Zay => 7,
            .Ha_ => 8,
            .Ta => 9,
            .Ya => 10,
            .Kaf => 20,
            .Lam => 30,
            .Mim => 40,
            .Nun => 50,
            .Sin => 60,
            .Ayn => 70,
            .Fa => 80,
            .Sad => 90,
            .Qaf => 100,
            .Ra => 200,
            .Shin => 300,
            .Ta_ => 400,
            .Tha => 500,
            .Kha => 600,
            .Dhal => 700,
            .Dad => 800,
            .Za => 900,
            .Ghayn => 1000,
        };
    }

    pub fn polarity(self: ArabicLetter) Polarity {
        return switch (self) {
            .Alif, .Waw, .Ya, .Lam, .Mim, .Nun, .Qaf => .Jamal,
            else => .Jalal,
        };
    }

    /// Arabic script letter -> abjad letter (alif forms map to Alif, ة to Ha, ى to Ya).
    pub fn fromCodepoint(c: u21) ?ArabicLetter {
        return switch (c) {
            0x0627, 0x0623, 0x0625, 0x0622, 0x0671 => .Alif, // ا أ إ آ ٱ
            0x0628 => .Ba, // ب
            0x062C => .Jim, // ج
            0x062F => .Dal, // د
            0x0647, 0x0629 => .Ha, // ه ة
            0x0648, 0x0624 => .Waw, // و ؤ
            0x0632 => .Zay, // ز
            0x062D => .Ha_, // ح
            0x0637 => .Ta, // ط
            0x064A, 0x0649, 0x0626 => .Ya, // ي ى ئ
            0x0643 => .Kaf, // ك
            0x0644 => .Lam, // ل
            0x0645 => .Mim, // م
            0x0646 => .Nun, // ن
            0x0633 => .Sin, // س
            0x0639 => .Ayn, // ع
            0x0641 => .Fa, // ف
            0x0635 => .Sad, // ص
            0x0642 => .Qaf, // ق
            0x0631 => .Ra, // ر
            0x0634 => .Shin, // ش
            0x062A => .Ta_, // ت
            0x062B => .Tha, // ث
            0x062E => .Kha, // خ
            0x0630 => .Dhal, // ذ
            0x0636 => .Dad, // ض
            0x0638 => .Za, // ظ
            0x063A => .Ghayn, // غ
            else => null,
        };
    }
};

pub const Polarity = enum(u8) {
    Jamal = 0, // جمال: Expansion, Mercy
    Jalal = 1, // جلال: Contraction, Rigor
};

// Al-Hamid: ح(8) + ا(1) + م(40) + د(4) = 53
pub const AL_HAMID = [_]ArabicLetter{ .Ha_, .Alif, .Mim, .Dal };
pub const AL_HAMID_VALUE: u32 = 8 + 1 + 40 + 4; // = 53
pub const MIRROR_DIMENSION: u32 = AL_HAMID_VALUE * 2; // = 106
pub const BIFURCATION_ORDER: u32 = 7; // digit_root(106) = 7
pub const BIFURCATION_THRESHOLD: u32 = BIFURCATION_ORDER * BIFURCATION_ORDER; // = 49

/// Digit root reduction (Hisāb al-Jummal).
pub fn digitRoot(n: u32) u8 {
    if (n == 0) return 0;
    const r: u8 = @intCast(n % 9);
    return if (r == 0) 9 else r;
}

/// Jamāl-Jalāl median.
pub fn equilibriumConstant(letters: []const ArabicLetter) u32 {
    var jamal: u32 = 0;
    var jalal: u32 = 0;
    for (letters) |l| switch (l.polarity()) {
        .Jamal => jamal += l.abjadValue(),
        .Jalal => jalal += l.abjadValue(),
    };
    return (jamal + jalal) / 2;
}

pub fn Wafq(comptime N: usize) type {
    return struct {
        matrix: [N][N]u32,
        constant_sum: u32,

        const Self = @This();

        pub fn rowSum(self: Self, i: usize) u32 {
            var s: u32 = 0;
            for (self.matrix[i]) |v| s += v;
            return s;
        }
        pub fn colSum(self: Self, j: usize) u32 {
            var s: u32 = 0;
            for (0..N) |i| s += self.matrix[i][j];
            return s;
        }
        pub fn diagSum(self: Self) u32 {
            var s: u32 = 0;
            for (0..N) |i| s += self.matrix[i][i];
            return s;
        }
        pub fn antiDiagSum(self: Self) u32 {
            var s: u32 = 0;
            for (0..N) |i| s += self.matrix[i][N - 1 - i];
            return s;
        }
        pub fn verify(self: Self) bool {
            const s = self.constant_sum;
            for (0..N) |i| if (self.rowSum(i) != s) return false;
            for (0..N) |j| if (self.colSum(j) != s) return false;
            if (self.diagSum() != s) return false;
            if (self.antiDiagSum() != s) return false;
            return true;
        }
    };
}

pub const WAFQ_ALLAH_3X3: Wafq(3) = .{
    .matrix = .{ .{ 8, 1, 24 }, .{ 15, 11, 7 }, .{ 10, 21, 2 } },
    .constant_sum = 33,
};

pub const DecoherenceQuadrant = enum(u8) {
    Q1_EnochianLTR = 0, // 0-90°: Jamāl
    Q2_LatinLTR = 1, // 90-180°: Jamāl
    Q3_HebrewRTL = 2, // 180-270°: Jalāl
    Q4_ArabicRTL = 3, // 270-360°: Jalāl

    pub fn fromStep(step: u64) DecoherenceQuadrant {
        return switch ((step / 12) % 4) {
            0 => .Q1_EnochianLTR,
            1 => .Q2_LatinLTR,
            2 => .Q3_HebrewRTL,
            else => .Q4_ArabicRTL,
        };
    }

    pub fn polarity(self: DecoherenceQuadrant) Polarity {
        return switch (self) {
            .Q1_EnochianLTR, .Q2_LatinLTR => .Jamal,
            .Q3_HebrewRTL, .Q4_ArabicRTL => .Jalal,
        };
    }
};

pub const Hieroglyph = enum(u8) {
    N5, // 𓂀 Sun/Ra (Source)
    G43, // 𓆎 Quail (w/Waw)
    X1, // 𓏏 Bread (t/Ta)
    D58, // 𓉐 Foot (w/Walk/Step)
    G31, // 𓊽 Bird/Ba (Soul)
    D21, // 𓂋 Mouth (r/Ra/Speech)
    Aa1, // 𓇓 Head (Qutb/Pole)
    M17, // 𓇋 Reed (i/y/Ya/Input)
    N35, // 𓈖 Water (n/Nun/Flow)
    D46, // 𓅓 Hand (d/Dal/Action)
    O29, // 𓊪 House (pr/State)
    G1, // 𓄿 Vulture (a/Alif/Origin)
    Aa5, // 𓃭 Child (New State)
    I10, // 𓆓 Cobra (Protection)
    D36, // 𓎛 Arm (Power)
    D54, // 𓆑 Legs (Walk)
    S29, // 𓋴 Pool (Mirror/Shin)
};

pub const Call49Constants = struct {
    source_count: u32 = 0,
    qutb_detected: bool = false,
    step_count: u32 = 0,
    mirror_ops: u32 = 0,
    state_vecs: u32 = 0,
    origin_count: u32 = 0,
    new_states: u32 = 0,
};

pub fn decodeHieroglyphProgram(program: []const Hieroglyph) Call49Constants {
    var c: Call49Constants = .{};
    for (program) |h| switch (h) {
        .N5 => c.source_count += 1,
        .Aa1 => c.qutb_detected = true,
        .D58, .D54 => c.step_count += 1,
        .S29 => c.mirror_ops += 1,
        .O29 => c.state_vecs += 1,
        .G1 => c.origin_count += 1,
        .Aa5 => c.new_states += 1,
        else => {},
    };
    return c;
}

// Al-Ḥamīd full form: ا(1)+ل(30)+ح(8)+م(40)+ي(10)+د(4) = 93
pub const AL_HAMID_FULL_VALUE: u32 = 1 + 30 + 8 + 40 + 10 + 4;
// Aḥmad: أ(1)+ح(8)+م(40)+د(4) = 53
pub const AHMAD_VALUE: u32 = 1 + 8 + 40 + 4;
// ʿAlī: ع(70)+ل(30)+ي(10) = 110
pub const ALI_VALUE: u32 = 70 + 30 + 10;
// Master aggregate: 93 + 53 + 110 = 256 = 16²
pub const MASTER_AGGREGATE: u32 = AL_HAMID_FULL_VALUE + AHMAD_VALUE + ALI_VALUE;
pub const MATRIX_DIMENSION: u32 = 16; // sqrt(256)
// Jamāl vector (expansion): Al-Ḥamīd + Aḥmad = 146
pub const JAMAL_VECTOR: u32 = AL_HAMID_FULL_VALUE + AHMAD_VALUE;
// Jalāl vector (contraction): ʿAlī = 110
pub const JALAL_VECTOR: u32 = ALI_VALUE;
// Polarity delta = |146 - 110| = 36 = one quadrant of the 360° cipher
pub const POLARITY_DELTA: u32 = JAMAL_VECTOR - JALAL_VECTOR;
// 16×16 Wafq magic constant: n*(n²+1)/2 = 16*257/2 = 2056
pub const WAFQ_16X16_MAGIC: u32 = MATRIX_DIMENSION * (MASTER_AGGREGATE + 1) / 2;

pub const Pillar = enum(u8) {
    I_SovereignFoundation, // Djed-Ra-Nesw: Jalāl anchor, ʿAlī(110)
    II_PropheticTransmission, // Ilyas lineage: Jamāl-Jalāl bridge, Al-Ḥamīd(93)
    III_GenesisOrigin, // Mst/Netjer: Jamāl origin, Aḥmad(53) locks
    IV_HistoricalConvergence, // Israel/Merneptah: Jalāl boundary, ʿAlī(110)

    pub fn constant(self: Pillar) u32 {
        return switch (self) {
            .I_SovereignFoundation => JALAL_VECTOR,
            .II_PropheticTransmission => JAMAL_VECTOR,
            .III_GenesisOrigin => AHMAD_VALUE,
            .IV_HistoricalConvergence => JALAL_VECTOR,
        };
    }
};

pub const AlHamidMatrix = struct {
    aggregate: u32, // 256
    dimension: u32, // 16
    jamal_vec: u32, // 146
    jalal_vec: u32, // 110
    magic_constant: u32, // 2056

    pub fn new() AlHamidMatrix {
        return .{
            .aggregate = MASTER_AGGREGATE,
            .dimension = MATRIX_DIMENSION,
            .jamal_vec = JAMAL_VECTOR,
            .jalal_vec = JALAL_VECTOR,
            .magic_constant = WAFQ_16X16_MAGIC,
        };
    }

    pub fn verifyInvariants(self: AlHamidMatrix) bool {
        return self.aggregate == 256 and
            self.dimension * self.dimension == self.aggregate and
            self.jamal_vec + self.jalal_vec == self.aggregate and
            self.jamal_vec - self.jalal_vec == 36; // one quadrant
    }
};

pub const AL_HAMID_MATRIX: AlHamidMatrix = AlHamidMatrix.new();

pub fn kenomaState(t: u64) bool {
    return t < BIFURCATION_THRESHOLD;
}
pub fn pleromaState(t: u64) bool {
    return t >= BIFURCATION_THRESHOLD;
}

/// Abjad value of Arabic text; harakat, tatweel and spaces are skipped.
pub fn wordValue(text: []const u8) error{ InvalidUtf8, UnknownLetter }!struct { value: u32, letters: u32 } {
    var view = std.unicode.Utf8View.init(text) catch return error.InvalidUtf8;
    var it = view.iterator();
    var sum: u32 = 0;
    var n: u32 = 0;
    while (it.nextCodepoint()) |c| {
        if (c == ' ' or c == 0x0640 or (c >= 0x064B and c <= 0x065F) or c == 0x0670) continue;
        const l = ArabicLetter.fromCodepoint(c) orelse return error.UnknownLetter;
        sum += l.abjadValue();
        n += 1;
    }
    return .{ .value = sum, .letters = n };
}

// --------------------------------------------- tests (the 7 Rust tests)

const testing = std.testing;

fn sumValues(letters: []const ArabicLetter) u32 {
    var s: u32 = 0;
    for (letters) |l| s += l.abjadValue();
    return s;
}

test "test_al_hamid" {
    const sum = sumValues(&AL_HAMID);
    try testing.expectEqual(@as(u32, 53), sum);
    try testing.expectEqual(@as(u32, 106), sum * 2);
    try testing.expectEqual(@as(u8, 7), digitRoot(106));
}

test "test_allah_equilibrium" {
    const allah = [_]ArabicLetter{ .Alif, .Lam, .Lam, .Ha };
    try testing.expectEqual(@as(u32, 66), sumValues(&allah));
    try testing.expectEqual(@as(u32, 33), equilibriumConstant(&allah));
    try testing.expectEqual(@as(u32, 9), 33 % 12);
}

// The Rust test asserts WAFQ_ALLAH_3X3.verify(); executing it, rows and
// columns sum to 33 but the diagonals sum to 21 and 45, so verify is false.
// Stated as the Lean file states it: rows/columns, then diagonals.
test "test_wafq_allah" {
    const w = WAFQ_ALLAH_3X3;
    try testing.expectEqual(@as(u32, 33), w.constant_sum);
    for (0..3) |i| try testing.expectEqual(@as(u32, 33), w.rowSum(i));
    for (0..3) |j| try testing.expectEqual(@as(u32, 33), w.colSum(j));
    try testing.expectEqual(@as(u32, 21), w.diagSum());
    try testing.expectEqual(@as(u32, 45), w.antiDiagSum());
    try testing.expect(!w.verify());
}

test "test_decoherence_quadrants" {
    try testing.expectEqual(Polarity.Jamal, DecoherenceQuadrant.fromStep(0).polarity());
    try testing.expectEqual(Polarity.Jamal, DecoherenceQuadrant.fromStep(12).polarity());
    try testing.expectEqual(Polarity.Jalal, DecoherenceQuadrant.fromStep(24).polarity());
    try testing.expectEqual(Polarity.Jalal, DecoherenceQuadrant.fromStep(36).polarity());
    try testing.expectEqual(Polarity.Jamal, DecoherenceQuadrant.fromStep(48).polarity()); // cycle resets
}

test "test_exodus" {
    try testing.expect(kenomaState(48));
    try testing.expect(!kenomaState(49));
    try testing.expect(!pleromaState(48));
    try testing.expect(pleromaState(49));
}

test "test_al_hamid_matrix" {
    try testing.expectEqual(@as(u32, 256), MASTER_AGGREGATE);
    try testing.expectEqual(@as(u32, 256), MATRIX_DIMENSION * MATRIX_DIMENSION);
    try testing.expectEqual(@as(u8, 4), digitRoot(256));
    try testing.expectEqual(@as(u32, 146), JAMAL_VECTOR);
    try testing.expectEqual(@as(u32, 110), JALAL_VECTOR);
    try testing.expectEqual(@as(u32, 36), POLARITY_DELTA);
    try testing.expectEqual(@as(u32, 2056), WAFQ_16X16_MAGIC);
    try testing.expect(AL_HAMID_MATRIX.verifyInvariants());
}

test "test_pillar_constants" {
    try testing.expectEqual(@as(u32, 110), Pillar.I_SovereignFoundation.constant());
    try testing.expectEqual(@as(u32, 146), Pillar.II_PropheticTransmission.constant());
    try testing.expectEqual(AHMAD_VALUE, Pillar.III_GenesisOrigin.constant());
    try testing.expectEqual(AL_HAMID_VALUE, Pillar.III_GenesisOrigin.constant());
    try testing.expectEqual(@as(u32, 110), Pillar.IV_HistoricalConvergence.constant());
    try testing.expectEqual(Pillar.I_SovereignFoundation.constant(), Pillar.IV_HistoricalConvergence.constant());
}

test "abjad: word values and hieroglyph decoder" {
    try testing.expectEqual(@as(u32, 66), (try wordValue("الله")).value);
    try testing.expectEqual(@as(u32, 53), (try wordValue("أحمد")).value);
    try testing.expectEqual(@as(u32, 110), (try wordValue("علي")).value);
    try testing.expectError(error.UnknownLetter, wordValue("abc"));
    const c = decodeHieroglyphProgram(&.{ .N5, .Aa1, .D58, .D54, .S29, .O29, .G1, .Aa5, .X1 });
    try testing.expectEqual(@as(u32, 2), c.step_count);
    try testing.expect(c.qutb_detected);
}
