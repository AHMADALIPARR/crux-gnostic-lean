# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
version       = "0.1.0"
author        = "Ahmad Ali Parr"
description   = "Nim bindings for libcrux, the Zig CRUX compiler"
license       = "AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0"
bin           = @["crux_cli"]
requires "nim >= 2.4.2"

task test, "Run the binding tests (needs ../zig/zig-out from `zig build`)":
  exec "nim c -r --hints:off tests/test_crux.nim"
