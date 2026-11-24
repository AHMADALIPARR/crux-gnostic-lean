# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
## Tests for the Nim bindings: `nim c -r tests/test_crux.nim` or `nimble test`.

import std/[strutils, unittest]
import ../crux

const sample = "равенство(x + 1, 1 + x)"

suite "libcrux":
  test "version":
    check version() == "0.1.0"

  test "lex reports line:column":
    let toks = lex(sample)
    check toks.startsWith("1:1\tRavno\tравенство\n")
    check "1:13\tPlus\t+" in toks

  test "parse and diagnostics":
    check "Ravnostvo" in parse(sample)
    expect CruxError:
      discard parse("сила(")
    try:
      discard parse("сила(")
    except CruxError as e:
      check e.msg.startsWith("<input>:1:6: error:")

  test "emit-smt":
    let smt = emitSmt(sample)
    check "(set-logic QF_BV)" in smt
    check "(bvadd x (_ bv1 32))" in smt
    check "(check-sat)" in smt

  test "emit-lean":
    let lean = emitLean(sample)
    check "namespace CruxGenerated" in lean
    check "theorem sila_goal_S0_0" in lean

  test "emit-cuda":
    let cu = emitCuda("сила(S0[x := 2 + 3], x = 5)")
    check "__global__" in cu
    check "crux_sas_step" in cu

  test "check and solve":
    check check("2 * 3 + 1 = 7").startsWith("sila_goal_S0_0: PROVED")
    check solve("1 ≤ p ∧ p ≤ 3 ∧ 1 ≤ q ∧ q ≤ 3 ∧ p + q = 7") == "sila_goal_S0_0: UNSAT\n"

  test "abjad":
    check abjadValue("الله") == 66
    check abjadValue("علي") == 110
    check digitRoot(66) == 3
    check letterValue(0) == 1
    check letterValue(99) == 0
    check not wafqAllahVerify()
    let s = wafqAllahSums()
    check s[0 .. 5] == [33'u32, 33, 33, 33, 33, 33]
    check s[6] == 21
    check s[7] == 45
