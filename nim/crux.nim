# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
## Nim bindings for libcrux, the C ABI of the Zig CRUX compiler
## (zig/src/capi.zig, zig/include/crux.h).
##
## Build the library first: `cd zig && zig build`. The paths below default to
## ../zig/zig-out; override with `-d:cruxPrefix=/path/to/zig-out`.

import std/os

const cruxPrefix {.strdefine.} = currentSourcePath().parentDir / ".." / "zig" / "zig-out"
const cruxHeader = cruxPrefix / "include" / "crux.h"

{.passL: cruxPrefix / "lib" / "libcrux.a".}

type
  CruxError* = object of CatchableError
    ## A CRUX diagnostic: "<input>:line:col: error: message".

proc c_crux_version(): cstring {.importc: "crux_version", header: cruxHeader, cdecl.}
proc c_crux_free(p: cstring) {.importc: "crux_free", header: cruxHeader, cdecl.}

proc c_crux_lex(src: cstring, len: csize_t, output: ptr cstring): cint {.importc: "crux_lex", header: cruxHeader, cdecl.}
proc c_crux_parse(src: cstring, len: csize_t, output: ptr cstring): cint {.importc: "crux_parse", header: cruxHeader, cdecl.}
proc c_crux_lower(src: cstring, len: csize_t, output: ptr cstring): cint {.importc: "crux_lower", header: cruxHeader, cdecl.}
proc c_crux_emit_smt(src: cstring, len: csize_t, output: ptr cstring): cint {.importc: "crux_emit_smt", header: cruxHeader, cdecl.}
proc c_crux_emit_lean(src: cstring, len: csize_t, output: ptr cstring): cint {.importc: "crux_emit_lean", header: cruxHeader, cdecl.}
proc c_crux_emit_sas(src: cstring, len: csize_t, output: ptr cstring): cint {.importc: "crux_emit_sas", header: cruxHeader, cdecl.}
proc c_crux_emit_cuda(src: cstring, len: csize_t, output: ptr cstring): cint {.importc: "crux_emit_cuda", header: cruxHeader, cdecl.}
proc c_crux_cert(src: cstring, len: csize_t, output: ptr cstring): cint {.importc: "crux_cert", header: cruxHeader, cdecl.}
proc c_crux_check(src: cstring, len: csize_t, output: ptr cstring): cint {.importc: "crux_check", header: cruxHeader, cdecl.}
proc c_crux_run(src: cstring, len: csize_t, output: ptr cstring): cint {.importc: "crux_run", header: cruxHeader, cdecl.}
proc c_crux_solve(src: cstring, len: csize_t, output: ptr cstring): cint {.importc: "crux_solve", header: cruxHeader, cdecl.}

proc c_crux_abjad_value(text: cstring, len: csize_t, value: ptr uint32): cint {.importc: "crux_abjad_value", header: cruxHeader, cdecl.}
proc c_crux_abjad_digit_root(n: uint32): uint8 {.importc: "crux_abjad_digit_root", header: cruxHeader, cdecl.}
proc c_crux_abjad_letter_value(index: cint): uint32 {.importc: "crux_abjad_letter_value", header: cruxHeader, cdecl.}
proc c_crux_wafq_allah_verify(): bool {.importc: "crux_wafq_allah_verify", header: cruxHeader, cdecl.}
proc c_crux_wafq_allah_sums(output: ptr array[8, uint32]) {.importc: "crux_wafq_allah_sums", header: cruxHeader, cdecl.}

proc finish(rc: cint, output: cstring): string =
  if output != nil:
    result = $output
    c_crux_free(output)
  case rc
  of 0: discard
  of 1: raise newException(CruxError, result)
  else: raise newException(OutOfMemDefect, "libcrux: allocation failure")

template call(f: untyped, src: string): string =
  var output: cstring = nil
  let rc = f(cstring(src), csize_t(src.len), addr output)
  finish(rc, output)

proc version*(): string = $c_crux_version()

proc lex*(src: string): string = call(c_crux_lex, src)
  ## Tokens with line:column, one per line.
proc parse*(src: string): string = call(c_crux_parse, src)
proc lower*(src: string): string = call(c_crux_lower, src)
proc emitSmt*(src: string): string = call(c_crux_emit_smt, src)
proc emitLean*(src: string): string = call(c_crux_emit_lean, src)
proc emitSas*(src: string): string = call(c_crux_emit_sas, src)
proc emitCuda*(src: string): string = call(c_crux_emit_cuda, src)
proc cert*(src: string): string = call(c_crux_cert, src)
proc check*(src: string): string = call(c_crux_check, src)
  ## OMEGA verdicts without external tools (Lean `decide`, then SAS).
proc run*(src: string): string = call(c_crux_run, src)
proc solve*(src: string): string = call(c_crux_solve, src)

proc abjadValue*(word: string): uint32 =
  ## Sum of the abjad values of the letters of `word` (spaces, tatweel and
  ## harakat are skipped).
  if c_crux_abjad_value(cstring(word), csize_t(word.len), addr result) != 0:
    raise newException(CruxError, "abjad: invalid UTF-8 or a non-Arabic letter in input")

proc digitRoot*(n: uint32): uint8 = c_crux_abjad_digit_root(n)

proc letterValue*(index: int): uint32 =
  ## Abjad value of letter `index` (0 = Alif ... 27 = Ghayn), 0 if out of range.
  c_crux_abjad_letter_value(cint(index))

proc wafqAllahVerify*(): bool = c_crux_wafq_allah_verify()

proc wafqAllahSums*(): array[8, uint32] =
  ## Row sums, column sums, diagonal, anti-diagonal of WAFQ_ALLAH_3X3.
  c_crux_wafq_allah_sums(addr result)
