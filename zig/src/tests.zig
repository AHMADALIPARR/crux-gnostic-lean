// SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
//! Test root: every module's tests plus the C ABI tests.

test {
    _ = @import("root.zig");
    _ = @import("capi.zig");
}
