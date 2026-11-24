-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Regression tests for Crux/Russian_checked.lean, checked by `#guard`
-- while this module builds (a failing case fails the build).
--
-- Reference corpus: 258 inputs (86 terms, 121 formulas, 37 Russian forms,
-- 14 sorts), 18 of them deeply nested. For each input the tests pin:
--   * the result and the end position of the internal entry point
--     (`parseTerm` / `parseFormula` / `parseRussianForm` / `parseSort`)
--     at the public fuel budget `tokens.length * 8 + 16`;
--   * the result of the public function (`parse_term` / `parse_formula` /
--     `parse_russian`), error messages included;
--   * that four times the budget gives the same result;
--   * the result at one eighth of the budget (mostly fuel exhaustion,
--     which must be a `recursion limit reached` error, never an AST).
-- Deep cases pin "length:hash" of the result string instead of the
-- full text.
--
-- These expected values are sample-based regression evidence, not a
-- proof of equivalence. How they were cross-checked is in the commit
-- message of the commit that added this file.

import Crux.Russian_checked

namespace Crux
namespace RussianCheckedTests

def showRes {α : Type} [Repr α] : Except String (α × Nat) → String
  | .ok (v, p) => s!"OK {p} {(repr v).pretty 100000000}"
  | .error e => s!"ERR {e}"

def showPub {α : Type} [Repr α] : Except String α → String
  | .ok v => s!"OK {(repr v).pretty 100000000}"
  | .error e => s!"ERR {e}"

def budget (s : String) : Nat := (tokenize s).length * 8 + 16

/-- Internal entry point with an explicit fuel; returns value and end position. -/
def runAt (entry s : String) (fuel : Nat) : String :=
  let toks := tokenize s
  if entry == "term" then showRes (parseTerm toks 0 fuel)
  else if entry == "formula" then showRes (parseFormula toks 0 fuel)
  else if entry == "sort" then showRes (parseSort toks 0 fuel)
  else showRes (parseRussianForm toks 0 fuel)

def run (entry s : String) : String := runAt entry s (budget s)

def pub (entry s : String) : String :=
  if entry == "term" then showPub (parse_term s)
  else if entry == "formula" then showPub (parse_formula s)
  else if entry == "russian" then showPub (parse_russian s)
  else "-"

def digest (r : String) : String := s!"{r.length}:{hash r}"

/-- Four times the budget gives the same result. -/
def stable (entry s : String) : Bool := runAt entry s (4 * budget s) == run entry s

-- t000: term 'x'
#guard run "term" "x" == "OK 1 Crux.Term.Var \"x\""
#guard pub "term" "x" == "OK Crux.Term.Var \"x\""
#guard runAt "term" "x" (budget "x" / 8) == "OK 1 Crux.Term.Var \"x\""
#guard stable "term" "x"
-- t001: term '42'
#guard run "term" "42" == "OK 1 Crux.Term.Const (Crux.Literal.Number 42)"
#guard pub "term" "42" == "OK Crux.Term.Const (Crux.Literal.Number 42)"
#guard runAt "term" "42" (budget "42" / 8) == "OK 1 Crux.Term.Const (Crux.Literal.Number 42)"
#guard stable "term" "42"
-- t002: term '0'
#guard run "term" "0" == "OK 1 Crux.Term.Const (Crux.Literal.Number 0)"
#guard pub "term" "0" == "OK Crux.Term.Const (Crux.Literal.Number 0)"
#guard runAt "term" "0" (budget "0" / 8) == "OK 1 Crux.Term.Const (Crux.Literal.Number 0)"
#guard stable "term" "0"
-- t003: term '007'
#guard run "term" "007" == "OK 1 Crux.Term.Const (Crux.Literal.Number 7)"
#guard pub "term" "007" == "OK Crux.Term.Const (Crux.Literal.Number 7)"
#guard runAt "term" "007" (budget "007" / 8) == "OK 1 Crux.Term.Const (Crux.Literal.Number 7)"
#guard stable "term" "007"
-- t004: term 'true'
#guard run "term" "true" == "OK 1 Crux.Term.Const (Crux.Literal.Bool true)"
#guard pub "term" "true" == "OK Crux.Term.Const (Crux.Literal.Bool true)"
#guard runAt "term" "true" (budget "true" / 8) == "OK 1 Crux.Term.Const (Crux.Literal.Bool true)"
#guard stable "term" "true"
-- t005: term 'false'
#guard run "term" "false" == "OK 1 Crux.Term.Const (Crux.Literal.Bool false)"
#guard pub "term" "false" == "OK Crux.Term.Const (Crux.Literal.Bool false)"
#guard runAt "term" "false" (budget "false" / 8) == "OK 1 Crux.Term.Const (Crux.Literal.Bool false)"
#guard stable "term" "false"
-- t006: term '⊤'
#guard run "term" "⊤" == "OK 1 Crux.Term.Const (Crux.Literal.Bool true)"
#guard pub "term" "⊤" == "OK Crux.Term.Const (Crux.Literal.Bool true)"
#guard runAt "term" "⊤" (budget "⊤" / 8) == "OK 1 Crux.Term.Const (Crux.Literal.Bool true)"
#guard stable "term" "⊤"
-- t007: term '⊥'
#guard run "term" "⊥" == "OK 1 Crux.Term.Const (Crux.Literal.Bool false)"
#guard pub "term" "⊥" == "OK Crux.Term.Const (Crux.Literal.Bool false)"
#guard runAt "term" "⊥" (budget "⊥" / 8) == "OK 1 Crux.Term.Const (Crux.Literal.Bool false)"
#guard stable "term" "⊥"
-- t008: term '"hello"'
#guard run "term" "\"hello\"" == "OK 1 Crux.Term.Const (Crux.Literal.Str \"hello\")"
#guard pub "term" "\"hello\"" == "OK Crux.Term.Const (Crux.Literal.Str \"hello\")"
#guard runAt "term" "\"hello\"" (budget "\"hello\"" / 8) == "OK 1 Crux.Term.Const (Crux.Literal.Str \"hello\")"
#guard stable "term" "\"hello\""
-- t009: term '"unterminated'
#guard run "term" "\"unterminated" == "OK 1 Crux.Term.Const (Crux.Literal.Str \"unterminated\")"
#guard pub "term" "\"unterminated" == "OK Crux.Term.Const (Crux.Literal.Str \"unterminated\")"
#guard runAt "term" "\"unterminated" (budget "\"unterminated" / 8) == "OK 1 Crux.Term.Const (Crux.Literal.Str \"unterminated\")"
#guard stable "term" "\"unterminated"
-- t010: term '()'
#guard run "term" "()" == "OK 2 Crux.Term.Nil"
#guard pub "term" "()" == "OK Crux.Term.Nil"
#guard runAt "term" "()" (budget "()" / 8) == "OK 2 Crux.Term.Nil"
#guard stable "term" "()"
-- t011: term '(x)'
#guard run "term" "(x)" == "OK 3 Crux.Term.Paren (Crux.Term.Var \"x\")"
#guard pub "term" "(x)" == "OK Crux.Term.Paren (Crux.Term.Var \"x\")"
#guard runAt "term" "(x)" (budget "(x)" / 8) == "OK 3 Crux.Term.Paren (Crux.Term.Var \"x\")"
#guard stable "term" "(x)"
-- t012: term '(x, y)'
#guard run "term" "(x, y)" == "OK 5 Crux.Term.Tuple [Crux.Term.Var \"x\", Crux.Term.Var \"y\"]"
#guard pub "term" "(x, y)" == "OK Crux.Term.Tuple [Crux.Term.Var \"x\", Crux.Term.Var \"y\"]"
#guard runAt "term" "(x, y)" (budget "(x, y)" / 8) == "OK 5 Crux.Term.Tuple [Crux.Term.Var \"x\", Crux.Term.Var \"y\"]"
#guard stable "term" "(x, y)"
-- t013: term '(x, y, z)'
#guard run "term" "(x, y, z)" == "OK 7 Crux.Term.Tuple [Crux.Term.Var \"x\", Crux.Term.Var \"y\", Crux.Term.Var \"z\"]"
#guard pub "term" "(x, y, z)" == "OK Crux.Term.Tuple [Crux.Term.Var \"x\", Crux.Term.Var \"y\", Crux.Term.Var \"z\"]"
#guard runAt "term" "(x, y, z)" (budget "(x, y, z)" / 8) == "OK 7 Crux.Term.Tuple [Crux.Term.Var \"x\", Crux.Term.Var \"y\", Crux.Term.Var \"z\"]"
#guard stable "term" "(x, y, z)"
-- t014: term '((x))'
#guard run "term" "((x))" == "OK 5 Crux.Term.Paren (Crux.Term.Paren (Crux.Term.Var \"x\"))"
#guard pub "term" "((x))" == "OK Crux.Term.Paren (Crux.Term.Paren (Crux.Term.Var \"x\"))"
#guard runAt "term" "((x))" (budget "((x))" / 8) == "ERR recursion limit reached in parse_term_atom"
#guard stable "term" "((x))"
-- t015: term '(x, (y, z))'
#guard run "term" "(x, (y, z))" == "OK 9 Crux.Term.Tuple [Crux.Term.Var \"x\", Crux.Term.Tuple [Crux.Term.Var \"y\", Crux.Term.Var \"z\"]]"
#guard pub "term" "(x, (y, z))" == "OK Crux.Term.Tuple [Crux.Term.Var \"x\", Crux.Term.Tuple [Crux.Term.Var \"y\", Crux.Term.Var \"z\"]]"
#guard runAt "term" "(x, (y, z))" (budget "(x, (y, z))" / 8) == "OK 9 Crux.Term.Tuple [Crux.Term.Var \"x\", Crux.Term.Tuple [Crux.Term.Var \"y\", Crux.Term.Var \"z\"]]"
#guard stable "term" "(x, (y, z))"
-- t016: term 'f x'
#guard run "term" "f x" == "OK 2 Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")"
#guard pub "term" "f x" == "OK Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")"
#guard runAt "term" "f x" (budget "f x" / 8) == "OK 2 Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")"
#guard stable "term" "f x"
-- t017: term 'f x y'
#guard run "term" "f x y" == "OK 3 Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.App (Crux.Term.Var \"x\") (Crux.Term.Var \"y\"))"
#guard pub "term" "f x y" == "OK Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.App (Crux.Term.Var \"x\") (Crux.Term.Var \"y\"))"
#guard runAt "term" "f x y" (budget "f x y" / 8) == "OK 3 Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.App (Crux.Term.Var \"x\") (Crux.Term.Var \"y\"))"
#guard stable "term" "f x y"
-- t018: term 'f (x)'
#guard run "term" "f (x)" == "OK 4 Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Paren (Crux.Term.Var \"x\"))"
#guard pub "term" "f (x)" == "OK Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Paren (Crux.Term.Var \"x\"))"
#guard runAt "term" "f (x)" (budget "f (x)" / 8) == "OK 4 Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Paren (Crux.Term.Var \"x\"))"
#guard stable "term" "f (x)"
-- t019: term 'f 1'
#guard run "term" "f 1" == "OK 2 Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Const (Crux.Literal.Number 1))"
#guard pub "term" "f 1" == "OK Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Const (Crux.Literal.Number 1))"
#guard runAt "term" "f 1" (budget "f 1" / 8) == "OK 2 Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Const (Crux.Literal.Number 1))"
#guard stable "term" "f 1"
-- t020: term 'f true'
#guard run "term" "f true" == "OK 2 Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Const (Crux.Literal.Bool true))"
#guard pub "term" "f true" == "OK Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Const (Crux.Literal.Bool true))"
#guard runAt "term" "f true" (budget "f true" / 8) == "OK 2 Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Const (Crux.Literal.Bool true))"
#guard stable "term" "f true"
-- t021: term 'f ()'
#guard run "term" "f ()" == "OK 3 Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Nil)"
#guard pub "term" "f ()" == "OK Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Nil)"
#guard runAt "term" "f ()" (budget "f ()" / 8) == "OK 3 Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Nil)"
#guard stable "term" "f ()"
-- t022: term 'f "s"'
#guard run "term" "f \"s\"" == "OK 1 Crux.Term.Var \"f\""
#guard pub "term" "f \"s\"" == "OK Crux.Term.Var \"f\""
#guard runAt "term" "f \"s\"" (budget "f \"s\"" / 8) == "OK 1 Crux.Term.Var \"f\""
#guard stable "term" "f \"s\""
-- t023: term 'f x + g y'
#guard run "term" "f x + g y" == "OK 5 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")) (Crux.Term.App (Crux.Term.Var \"g\") (Crux.Term.Var \"y\"))"
#guard pub "term" "f x + g y" == "OK Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")) (Crux.Term.App (Crux.Term.Var \"g\") (Crux.Term.Var \"y\"))"
#guard runAt "term" "f x + g y" (budget "f x + g y" / 8) == "OK 5 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")) (Crux.Term.App (Crux.Term.Var \"g\") (Crux.Term.Var \"y\"))"
#guard stable "term" "f x + g y"
-- t024: term 'a + b'
#guard run "term" "a + b" == "OK 3 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard pub "term" "a + b" == "OK Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard runAt "term" "a + b" (budget "a + b" / 8) == "OK 3 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard stable "term" "a + b"
-- t025: term 'a - b'
#guard run "term" "a - b" == "OK 3 Crux.Term.BinOp (Crux.BinOp.Sub) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard pub "term" "a - b" == "OK Crux.Term.BinOp (Crux.BinOp.Sub) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard runAt "term" "a - b" (budget "a - b" / 8) == "OK 3 Crux.Term.BinOp (Crux.BinOp.Sub) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard stable "term" "a - b"
-- t026: term 'a * b'
#guard run "term" "a * b" == "OK 3 Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard pub "term" "a * b" == "OK Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard runAt "term" "a * b" (budget "a * b" / 8) == "OK 3 Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard stable "term" "a * b"
-- t027: term 'a / b'
#guard run "term" "a / b" == "OK 3 Crux.Term.BinOp (Crux.BinOp.Div) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard pub "term" "a / b" == "OK Crux.Term.BinOp (Crux.BinOp.Div) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard runAt "term" "a / b" (budget "a / b" / 8) == "OK 3 Crux.Term.BinOp (Crux.BinOp.Div) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard stable "term" "a / b"
-- t028: term 'a % b'
#guard run "term" "a % b" == "OK 3 Crux.Term.BinOp (Crux.BinOp.Mod) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard pub "term" "a % b" == "OK Crux.Term.BinOp (Crux.BinOp.Mod) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard runAt "term" "a % b" (budget "a % b" / 8) == "OK 3 Crux.Term.BinOp (Crux.BinOp.Mod) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard stable "term" "a % b"
-- t029: term 'a + b * c'
#guard run "term" "a + b * c" == "OK 5 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"b\") (Crux.Term.Var \"c\"))"
#guard pub "term" "a + b * c" == "OK Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"b\") (Crux.Term.Var \"c\"))"
#guard runAt "term" "a + b * c" (budget "a + b * c" / 8) == "OK 5 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"b\") (Crux.Term.Var \"c\"))"
#guard stable "term" "a + b * c"
-- t030: term 'a * b + c'
#guard run "term" "a * b + c" == "OK 5 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"c\")"
#guard pub "term" "a * b + c" == "OK Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"c\")"
#guard runAt "term" "a * b + c" (budget "a * b + c" / 8) == "OK 5 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"c\")"
#guard stable "term" "a * b + c"
-- t031: term 'a - b - c'
#guard run "term" "a - b - c" == "OK 5 Crux.Term.BinOp (Crux.BinOp.Sub) (Crux.Term.BinOp (Crux.BinOp.Sub) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"c\")"
#guard pub "term" "a - b - c" == "OK Crux.Term.BinOp (Crux.BinOp.Sub) (Crux.Term.BinOp (Crux.BinOp.Sub) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"c\")"
#guard runAt "term" "a - b - c" (budget "a - b - c" / 8) == "OK 5 Crux.Term.BinOp (Crux.BinOp.Sub) (Crux.Term.BinOp (Crux.BinOp.Sub) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"c\")"
#guard stable "term" "a - b - c"
-- t032: term 'a + b + c + d'
#guard run "term" "a + b + c + d" == "OK 7 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"c\")) (Crux.Term.Var \"d\")"
#guard pub "term" "a + b + c + d" == "OK Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"c\")) (Crux.Term.Var \"d\")"
#guard runAt "term" "a + b + c + d" (budget "a + b + c + d" / 8) == "OK 7 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"c\")) (Crux.Term.Var \"d\")"
#guard stable "term" "a + b + c + d"
-- t033: term 'a * b * c'
#guard run "term" "a * b * c" == "OK 5 Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"c\")"
#guard pub "term" "a * b * c" == "OK Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"c\")"
#guard runAt "term" "a * b * c" (budget "a * b * c" / 8) == "OK 5 Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"c\")"
#guard stable "term" "a * b * c"
-- t034: term '(a + b) * c'
#guard run "term" "(a + b) * c" == "OK 7 Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Paren (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\"))) (Crux.Term.Var \"c\")"
#guard pub "term" "(a + b) * c" == "OK Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Paren (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\"))) (Crux.Term.Var \"c\")"
#guard runAt "term" "(a + b) * c" (budget "(a + b) * c" / 8) == "OK 7 Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Paren (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\"))) (Crux.Term.Var \"c\")"
#guard stable "term" "(a + b) * c"
-- t035: term 'a * (b + c)'
#guard run "term" "a * (b + c)" == "OK 7 Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"a\") (Crux.Term.Paren (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"b\") (Crux.Term.Var \"c\")))"
#guard pub "term" "a * (b + c)" == "OK Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"a\") (Crux.Term.Paren (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"b\") (Crux.Term.Var \"c\")))"
#guard runAt "term" "a * (b + c)" (budget "a * (b + c)" / 8) == "OK 7 Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"a\") (Crux.Term.Paren (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"b\") (Crux.Term.Var \"c\")))"
#guard stable "term" "a * (b + c)"
-- t036: term '1 + 2 * 3 - 4 / 2 % 5'
#guard run "term" "1 + 2 * 3 - 4 / 2 % 5" == "OK 11 Crux.Term.BinOp (Crux.BinOp.Sub) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Const (Crux.Literal.Number 1)) (Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Const (Crux.Literal.Number 2)) (Crux.Term.Const (Crux.Literal.Number 3)))) (Crux.Term.BinOp (Crux.BinOp.Mod) (Crux.Term.BinOp (Crux.BinOp.Div) (Crux.Term.Const (Crux.Literal.Number 4)) (Crux.Term.Const (Crux.Literal.Number 2))) (Crux.Term.Const (Crux.Literal.Number 5)))"
#guard pub "term" "1 + 2 * 3 - 4 / 2 % 5" == "OK Crux.Term.BinOp (Crux.BinOp.Sub) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Const (Crux.Literal.Number 1)) (Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Const (Crux.Literal.Number 2)) (Crux.Term.Const (Crux.Literal.Number 3)))) (Crux.Term.BinOp (Crux.BinOp.Mod) (Crux.Term.BinOp (Crux.BinOp.Div) (Crux.Term.Const (Crux.Literal.Number 4)) (Crux.Term.Const (Crux.Literal.Number 2))) (Crux.Term.Const (Crux.Literal.Number 5)))"
#guard runAt "term" "1 + 2 * 3 - 4 / 2 % 5" (budget "1 + 2 * 3 - 4 / 2 % 5" / 8) == "OK 11 Crux.Term.BinOp (Crux.BinOp.Sub) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Const (Crux.Literal.Number 1)) (Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Const (Crux.Literal.Number 2)) (Crux.Term.Const (Crux.Literal.Number 3)))) (Crux.Term.BinOp (Crux.BinOp.Mod) (Crux.Term.BinOp (Crux.BinOp.Div) (Crux.Term.Const (Crux.Literal.Number 4)) (Crux.Term.Const (Crux.Literal.Number 2))) (Crux.Term.Const (Crux.Literal.Number 5)))"
#guard stable "term" "1 + 2 * 3 - 4 / 2 % 5"
-- t037: term 'a -- comment\n + b'
#guard run "term" "a -- comment\n + b" == "OK 3 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard pub "term" "a -- comment\n + b" == "OK Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard runAt "term" "a -- comment\n + b" (budget "a -- comment\n + b" / 8) == "OK 3 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard stable "term" "a -- comment\n + b"
-- t038: term 'a--b'
#guard run "term" "a--b" == "OK 1 Crux.Term.Var \"a\""
#guard pub "term" "a--b" == "OK Crux.Term.Var \"a\""
#guard runAt "term" "a--b" (budget "a--b" / 8) == "OK 1 Crux.Term.Var \"a\""
#guard stable "term" "a--b"
-- t039: term 'a -> b'
#guard run "term" "a -> b" == "OK 1 Crux.Term.Var \"a\""
#guard pub "term" "a -> b" == "OK Crux.Term.Var \"a\""
#guard runAt "term" "a -> b" (budget "a -> b" / 8) == "OK 1 Crux.Term.Var \"a\""
#guard stable "term" "a -> b"
-- t040: term 'x = y'
#guard run "term" "x = y" == "OK 1 Crux.Term.Var \"x\""
#guard pub "term" "x = y" == "OK Crux.Term.Var \"x\""
#guard runAt "term" "x = y" (budget "x = y" / 8) == "OK 1 Crux.Term.Var \"x\""
#guard stable "term" "x = y"
-- t041: term 'fun x : Nat => x + 1'
#guard run "term" "fun x : Nat => x + 1" == "OK 8 Crux.Term.Lambda \"x\" (Crux.Sort.Nat) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"x\") (Crux.Term.Const (Crux.Literal.Number 1)))"
#guard pub "term" "fun x : Nat => x + 1" == "OK Crux.Term.Lambda \"x\" (Crux.Sort.Nat) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"x\") (Crux.Term.Const (Crux.Literal.Number 1)))"
#guard runAt "term" "fun x : Nat => x + 1" (budget "fun x : Nat => x + 1" / 8) == "OK 8 Crux.Term.Lambda \"x\" (Crux.Sort.Nat) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"x\") (Crux.Term.Const (Crux.Literal.Number 1)))"
#guard stable "term" "fun x : Nat => x + 1"
-- t042: term 'fun f : Nat → Nat => f 1'
#guard run "term" "fun f : Nat → Nat => f 1" == "OK 9 Crux.Term.Lambda \"f\" (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Nat)) (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Const (Crux.Literal.Number 1)))"
#guard pub "term" "fun f : Nat → Nat => f 1" == "OK Crux.Term.Lambda \"f\" (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Nat)) (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Const (Crux.Literal.Number 1)))"
#guard runAt "term" "fun f : Nat → Nat => f 1" (budget "fun f : Nat → Nat => f 1" / 8) == "OK 9 Crux.Term.Lambda \"f\" (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Nat)) (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Const (Crux.Literal.Number 1)))"
#guard stable "term" "fun f : Nat → Nat => f 1"
-- t043: term 'fun x : (Nat → Int) → Bool => x'
#guard run "term" "fun x : (Nat → Int) → Bool => x" == "OK 12 Crux.Term.Lambda \"x\" (Crux.Sort.Arrow (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Int)) (Crux.Sort.Bool)) (Crux.Term.Var \"x\")"
#guard pub "term" "fun x : (Nat → Int) → Bool => x" == "OK Crux.Term.Lambda \"x\" (Crux.Sort.Arrow (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Int)) (Crux.Sort.Bool)) (Crux.Term.Var \"x\")"
#guard runAt "term" "fun x : (Nat → Int) → Bool => x" (budget "fun x : (Nat → Int) → Bool => x" / 8) == "OK 12 Crux.Term.Lambda \"x\" (Crux.Sort.Arrow (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Int)) (Crux.Sort.Bool)) (Crux.Term.Var \"x\")"
#guard stable "term" "fun x : (Nat → Int) → Bool => x"
-- t044: term 'fun x : Foo ↦ x'
#guard run "term" "fun x : Foo ↦ x" == "OK 6 Crux.Term.Lambda \"x\" (Crux.Sort.User \"Foo\") (Crux.Term.Var \"x\")"
#guard pub "term" "fun x : Foo ↦ x" == "OK Crux.Term.Lambda \"x\" (Crux.Sort.User \"Foo\") (Crux.Term.Var \"x\")"
#guard runAt "term" "fun x : Foo ↦ x" (budget "fun x : Foo ↦ x" / 8) == "OK 6 Crux.Term.Lambda \"x\" (Crux.Sort.User \"Foo\") (Crux.Term.Var \"x\")"
#guard stable "term" "fun x : Foo ↦ x"
-- t045: term 'rec f = f x'
#guard run "term" "rec f = f x" == "OK 5 Crux.Term.Rec \"f\" (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\"))"
#guard pub "term" "rec f = f x" == "OK Crux.Term.Rec \"f\" (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\"))"
#guard runAt "term" "rec f = f x" (budget "rec f = f x" / 8) == "OK 5 Crux.Term.Rec \"f\" (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\"))"
#guard stable "term" "rec f = f x"
-- t046: term 'rec f == f'
#guard run "term" "rec f == f" == "OK 4 Crux.Term.Rec \"f\" (Crux.Term.Var \"f\")"
#guard pub "term" "rec f == f" == "OK Crux.Term.Rec \"f\" (Crux.Term.Var \"f\")"
#guard runAt "term" "rec f == f" (budget "rec f == f" / 8) == "OK 4 Crux.Term.Rec \"f\" (Crux.Term.Var \"f\")"
#guard stable "term" "rec f == f"
-- t047: term 'if x = y then a else b'
#guard run "term" "if x = y then a else b" == "OK 8 Crux.Term.IfThenElse (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard pub "term" "if x = y then a else b" == "OK Crux.Term.IfThenElse (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard runAt "term" "if x = y then a else b" (budget "if x = y then a else b" / 8) == "OK 8 Crux.Term.IfThenElse (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard stable "term" "if x = y then a else b"
-- t048: term 'if ¬ p then 1 else 2'
#guard run "term" "if ¬ p then 1 else 2" == "OK 7 Crux.Term.IfThenElse (Crux.Formula.Not (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))) (Crux.Term.Const (Crux.Literal.Number 1)) (Crux.Term.Const (Crux.Literal.Number 2))"
#guard pub "term" "if ¬ p then 1 else 2" == "OK Crux.Term.IfThenElse (Crux.Formula.Not (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))) (Crux.Term.Const (Crux.Literal.Number 1)) (Crux.Term.Const (Crux.Literal.Number 2))"
#guard runAt "term" "if ¬ p then 1 else 2" (budget "if ¬ p then 1 else 2" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "term" "if ¬ p then 1 else 2"
-- t049: term 'if p ∧ q then x else y'
#guard run "term" "if p ∧ q then x else y" == "OK 8 Crux.Term.IfThenElse (Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])]) (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")"
#guard pub "term" "if p ∧ q then x else y" == "OK Crux.Term.IfThenElse (Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])]) (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")"
#guard runAt "term" "if p ∧ q then x else y" (budget "if p ∧ q then x else y" / 8) == "ERR recursion limit reached in parse_term_atom"
#guard stable "term" "if p ∧ q then x else y"
-- t050: term 'if p → q then (x, y) else ()'
#guard run "term" "if p → q then (x, y) else ()" == "OK 13 Crux.Term.IfThenElse (Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" []))) (Crux.Term.Tuple [Crux.Term.Var \"x\", Crux.Term.Var \"y\"]) (Crux.Term.Nil)"
#guard pub "term" "if p → q then (x, y) else ()" == "OK Crux.Term.IfThenElse (Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" []))) (Crux.Term.Tuple [Crux.Term.Var \"x\", Crux.Term.Var \"y\"]) (Crux.Term.Nil)"
#guard runAt "term" "if p → q then (x, y) else ()" (budget "if p → q then (x, y) else ()" / 8) == "OK 13 Crux.Term.IfThenElse (Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" []))) (Crux.Term.Tuple [Crux.Term.Var \"x\", Crux.Term.Var \"y\"]) (Crux.Term.Nil)"
#guard stable "term" "if p → q then (x, y) else ()"
-- t051: term 'if if c then a else b = d then a else b'
#guard run "term" "if if c then a else b = d then a else b" == "OK 13 Crux.Term.IfThenElse (Crux.Formula.Eq (Crux.Term.IfThenElse (Crux.Formula.Atomic (Crux.Atomic.Predicate \"c\" [])) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"d\")) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard pub "term" "if if c then a else b = d then a else b" == "OK Crux.Term.IfThenElse (Crux.Formula.Eq (Crux.Term.IfThenElse (Crux.Formula.Atomic (Crux.Atomic.Predicate \"c\" [])) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"d\")) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")"
#guard runAt "term" "if if c then a else b = d then a else b" (budget "if if c then a else b = d then a else b" / 8) == "ERR recursion limit reached in parse_term"
#guard stable "term" "if if c then a else b = d then a else b"
-- t052: term 'переменная + 1'
#guard run "term" "переменная + 1" == "OK 3 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"переменная\") (Crux.Term.Const (Crux.Literal.Number 1))"
#guard pub "term" "переменная + 1" == "OK Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"переменная\") (Crux.Term.Const (Crux.Literal.Number 1))"
#guard runAt "term" "переменная + 1" (budget "переменная + 1" / 8) == "OK 3 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"переменная\") (Crux.Term.Const (Crux.Literal.Number 1))"
#guard stable "term" "переменная + 1"
-- t053: term 'α + β'
#guard run "term" "α + β" == "OK 3 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"α\") (Crux.Term.Var \"β\")"
#guard pub "term" "α + β" == "OK Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"α\") (Crux.Term.Var \"β\")"
#guard runAt "term" "α + β" (budget "α + β" / 8) == "OK 3 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"α\") (Crux.Term.Var \"β\")"
#guard stable "term" "α + β"
-- t054: term "x' + y_1"
#guard run "term" "x' + y_1" == "OK 3 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"x'\") (Crux.Term.Var \"y_1\")"
#guard pub "term" "x' + y_1" == "OK Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"x'\") (Crux.Term.Var \"y_1\")"
#guard runAt "term" "x' + y_1" (budget "x' + y_1" / 8) == "OK 3 Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"x'\") (Crux.Term.Var \"y_1\")"
#guard stable "term" "x' + y_1"
-- t055: term 'f x y z )'
#guard run "term" "f x y z )" == "OK 4 Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.App (Crux.Term.Var \"x\") (Crux.Term.App (Crux.Term.Var \"y\") (Crux.Term.Var \"z\")))"
#guard pub "term" "f x y z )" == "OK Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.App (Crux.Term.Var \"x\") (Crux.Term.App (Crux.Term.Var \"y\") (Crux.Term.Var \"z\")))"
#guard runAt "term" "f x y z )" (budget "f x y z )" / 8) == "OK 4 Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.App (Crux.Term.Var \"x\") (Crux.Term.App (Crux.Term.Var \"y\") (Crux.Term.Var \"z\")))"
#guard stable "term" "f x y z )"
-- t056: term ''
#guard run "term" "" == "ERR unexpected token in term: Crux.Token.Eof"
#guard pub "term" "" == "ERR unexpected token in term: Crux.Token.Eof"
#guard runAt "term" "" (budget "" / 8) == "ERR unexpected token in term: Crux.Token.Eof"
#guard stable "term" ""
-- t057: term '+'
#guard run "term" "+" == "ERR unexpected token in term: Crux.Token.Plus"
#guard pub "term" "+" == "ERR unexpected token in term: Crux.Token.Plus"
#guard runAt "term" "+" (budget "+" / 8) == "ERR unexpected token in term: Crux.Token.Plus"
#guard stable "term" "+"
-- t058: term ')'
#guard run "term" ")" == "ERR unexpected token in term: Crux.Token.RParen"
#guard pub "term" ")" == "ERR unexpected token in term: Crux.Token.RParen"
#guard runAt "term" ")" (budget ")" / 8) == "ERR unexpected token in term: Crux.Token.RParen"
#guard stable "term" ")"
-- t059: term '(x'
#guard run "term" "(x" == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard pub "term" "(x" == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard runAt "term" "(x" (budget "(x" / 8) == "ERR recursion limit reached in parse_term_atom"
#guard stable "term" "(x"
-- t060: term '(x,'
#guard run "term" "(x," == "ERR unexpected token in term: Crux.Token.Eof"
#guard pub "term" "(x," == "ERR unexpected token in term: Crux.Token.Eof"
#guard runAt "term" "(x," (budget "(x," / 8) == "ERR recursion limit reached in parse_term_atom"
#guard stable "term" "(x,"
-- t061: term '(x, y'
#guard run "term" "(x, y" == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard pub "term" "(x, y" == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard runAt "term" "(x, y" (budget "(x, y" / 8) == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard stable "term" "(x, y"
-- t062: term 'fun 1'
#guard run "term" "fun 1" == "ERR expected ident after fun, got Crux.Token.Number 1"
#guard pub "term" "fun 1" == "ERR expected ident after fun, got Crux.Token.Number 1"
#guard runAt "term" "fun 1" (budget "fun 1" / 8) == "ERR expected ident after fun, got Crux.Token.Number 1"
#guard stable "term" "fun 1"
-- t063: term 'fun x Nat => x'
#guard run "term" "fun x Nat => x" == "ERR expected Crux.Token.Colon, got Crux.Token.Ident \"Nat\""
#guard pub "term" "fun x Nat => x" == "ERR expected Crux.Token.Colon, got Crux.Token.Ident \"Nat\""
#guard runAt "term" "fun x Nat => x" (budget "fun x Nat => x" / 8) == "ERR expected Crux.Token.Colon, got Crux.Token.Ident \"Nat\""
#guard stable "term" "fun x Nat => x"
-- t064: term 'fun x : Nat x'
#guard run "term" "fun x : Nat x" == "ERR expected Crux.Token.FatArrow, got Crux.Token.Ident \"x\""
#guard pub "term" "fun x : Nat x" == "ERR expected Crux.Token.FatArrow, got Crux.Token.Ident \"x\""
#guard runAt "term" "fun x : Nat x" (budget "fun x : Nat x" / 8) == "ERR expected Crux.Token.FatArrow, got Crux.Token.Ident \"x\""
#guard stable "term" "fun x : Nat x"
-- t065: term 'rec 1'
#guard run "term" "rec 1" == "ERR expected ident after rec, got Crux.Token.Number 1"
#guard pub "term" "rec 1" == "ERR expected ident after rec, got Crux.Token.Number 1"
#guard runAt "term" "rec 1" (budget "rec 1" / 8) == "ERR expected ident after rec, got Crux.Token.Number 1"
#guard stable "term" "rec 1"
-- t066: term 'rec f f'
#guard run "term" "rec f f" == "ERR expected Crux.Token.Eq, got Crux.Token.Ident \"f\""
#guard pub "term" "rec f f" == "ERR expected Crux.Token.Eq, got Crux.Token.Ident \"f\""
#guard runAt "term" "rec f f" (budget "rec f f" / 8) == "ERR expected Crux.Token.Eq, got Crux.Token.Ident \"f\""
#guard stable "term" "rec f f"
-- t067: term 'if x then'
#guard run "term" "if x then" == "ERR unexpected token in term: Crux.Token.Eof"
#guard pub "term" "if x then" == "ERR unexpected token in term: Crux.Token.Eof"
#guard runAt "term" "if x then" (budget "if x then" / 8) == "ERR recursion limit reached in parse_formula_and"
#guard stable "term" "if x then"
-- t068: term 'if p then a'
#guard run "term" "if p then a" == "ERR expected Crux.Token.Else, got Crux.Token.Eof"
#guard pub "term" "if p then a" == "ERR expected Crux.Token.Else, got Crux.Token.Eof"
#guard runAt "term" "if p then a" (budget "if p then a" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "term" "if p then a"
-- t069: term 'if p then a else'
#guard run "term" "if p then a else" == "ERR unexpected token in term: Crux.Token.Eof"
#guard pub "term" "if p then a else" == "ERR unexpected token in term: Crux.Token.Eof"
#guard runAt "term" "if p then a else" (budget "if p then a else" / 8) == "ERR recursion limit reached in parse_term"
#guard stable "term" "if p then a else"
-- t070: term 'x +'
#guard run "term" "x +" == "ERR unexpected token in term: Crux.Token.Eof"
#guard pub "term" "x +" == "ERR unexpected token in term: Crux.Token.Eof"
#guard runAt "term" "x +" (budget "x +" / 8) == "ERR unexpected token in term: Crux.Token.Eof"
#guard stable "term" "x +"
-- t071: term 'f ('
#guard run "term" "f (" == "ERR unexpected token in term: Crux.Token.Eof"
#guard pub "term" "f (" == "ERR unexpected token in term: Crux.Token.Eof"
#guard runAt "term" "f (" (budget "f (" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "term" "f ("
-- t072: term '[x]'
#guard run "term" "[x]" == "ERR unexpected token in term: Crux.Token.LBracket"
#guard pub "term" "[x]" == "ERR unexpected token in term: Crux.Token.LBracket"
#guard runAt "term" "[x]" (budget "[x]" / 8) == "ERR unexpected token in term: Crux.Token.LBracket"
#guard stable "term" "[x]"
-- t073: term 'let x = 1 in x'
#guard run "term" "let x = 1 in x" == "ERR unexpected token in term: Crux.Token.Let"
#guard pub "term" "let x = 1 in x" == "ERR unexpected token in term: Crux.Token.Let"
#guard runAt "term" "let x = 1 in x" (budget "let x = 1 in x" / 8) == "ERR unexpected token in term: Crux.Token.Let"
#guard stable "term" "let x = 1 in x"
-- t074: term 'match x with'
#guard run "term" "match x with" == "ERR unexpected token in term: Crux.Token.Match"
#guard pub "term" "match x with" == "ERR unexpected token in term: Crux.Token.Match"
#guard runAt "term" "match x with" (budget "match x with" / 8) == "ERR unexpected token in term: Crux.Token.Match"
#guard stable "term" "match x with"
-- t075: term '∀ x : Nat . p'
#guard run "term" "∀ x : Nat . p" == "ERR unexpected token in term: Crux.Token.Forall"
#guard pub "term" "∀ x : Nat . p" == "ERR unexpected token in term: Crux.Token.Forall"
#guard runAt "term" "∀ x : Nat . p" (budget "∀ x : Nat . p" / 8) == "ERR unexpected token in term: Crux.Token.Forall"
#guard stable "term" "∀ x : Nat . p"
-- t076: term 'fun x : => x'
#guard run "term" "fun x : => x" == "ERR unexpected token in sort: Crux.Token.FatArrow"
#guard pub "term" "fun x : => x" == "ERR unexpected token in sort: Crux.Token.FatArrow"
#guard runAt "term" "fun x : => x" (budget "fun x : => x" / 8) == "ERR unexpected token in sort: Crux.Token.FatArrow"
#guard stable "term" "fun x : => x"
-- t077: term 'a + + b'
#guard run "term" "a + + b" == "ERR unexpected token in term: Crux.Token.Plus"
#guard pub "term" "a + + b" == "ERR unexpected token in term: Crux.Token.Plus"
#guard runAt "term" "a + + b" (budget "a + + b" / 8) == "ERR unexpected token in term: Crux.Token.Plus"
#guard stable "term" "a + + b"
-- t078: term '1 2 3'
#guard run "term" "1 2 3" == "OK 1 Crux.Term.Const (Crux.Literal.Number 1)"
#guard pub "term" "1 2 3" == "OK Crux.Term.Const (Crux.Literal.Number 1)"
#guard runAt "term" "1 2 3" (budget "1 2 3" / 8) == "OK 1 Crux.Term.Const (Crux.Literal.Number 1)"
#guard stable "term" "1 2 3"
-- f079: formula 'p'
#guard run "formula" "p" == "OK 1 Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])"
#guard pub "formula" "p" == "OK Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])"
#guard runAt "formula" "p" (budget "p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "p"
-- f080: formula 'true'
#guard run "formula" "true" == "OK 1 Crux.Formula.Atomic (Crux.Atomic.True)"
#guard pub "formula" "true" == "OK Crux.Formula.Atomic (Crux.Atomic.True)"
#guard runAt "formula" "true" (budget "true" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "true"
-- f081: formula 'false'
#guard run "formula" "false" == "OK 1 Crux.Formula.Atomic (Crux.Atomic.False)"
#guard pub "formula" "false" == "OK Crux.Formula.Atomic (Crux.Atomic.False)"
#guard runAt "formula" "false" (budget "false" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "false"
-- f082: formula '⊤'
#guard run "formula" "⊤" == "OK 1 Crux.Formula.Atomic (Crux.Atomic.True)"
#guard pub "formula" "⊤" == "OK Crux.Formula.Atomic (Crux.Atomic.True)"
#guard runAt "formula" "⊤" (budget "⊤" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "⊤"
-- f083: formula '⊥'
#guard run "formula" "⊥" == "OK 1 Crux.Formula.Atomic (Crux.Atomic.False)"
#guard pub "formula" "⊥" == "OK Crux.Formula.Atomic (Crux.Atomic.False)"
#guard runAt "formula" "⊥" (budget "⊥" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "⊥"
-- f084: formula '¬p'
#guard run "formula" "¬p" == "OK 2 Crux.Formula.Not (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "¬p" == "OK Crux.Formula.Not (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "¬p" (budget "¬p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "¬p"
-- f085: formula '!p'
#guard run "formula" "!p" == "OK 2 Crux.Formula.Not (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "!p" == "OK Crux.Formula.Not (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "!p" (budget "!p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "!p"
-- f086: formula '¬¬p'
#guard run "formula" "¬¬p" == "OK 3 Crux.Formula.Not (Crux.Formula.Not (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])))"
#guard pub "formula" "¬¬p" == "OK Crux.Formula.Not (Crux.Formula.Not (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])))"
#guard runAt "formula" "¬¬p" (budget "¬¬p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "¬¬p"
-- f087: formula '¬ ¬ ¬ p'
#guard run "formula" "¬ ¬ ¬ p" == "OK 4 Crux.Formula.Not (Crux.Formula.Not (Crux.Formula.Not (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))))"
#guard pub "formula" "¬ ¬ ¬ p" == "OK Crux.Formula.Not (Crux.Formula.Not (Crux.Formula.Not (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))))"
#guard runAt "formula" "¬ ¬ ¬ p" (budget "¬ ¬ ¬ p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "¬ ¬ ¬ p"
-- f088: formula 'p ∧ q'
#guard run "formula" "p ∧ q" == "OK 3 Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])]"
#guard pub "formula" "p ∧ q" == "OK Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])]"
#guard runAt "formula" "p ∧ q" (budget "p ∧ q" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "p ∧ q"
-- f089: formula 'p ∨ q'
#guard run "formula" "p ∨ q" == "OK 3 Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])]"
#guard pub "formula" "p ∨ q" == "OK Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])]"
#guard runAt "formula" "p ∨ q" (budget "p ∨ q" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "p ∨ q"
-- f090: formula 'p → q'
#guard run "formula" "p → q" == "OK 3 Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" []))"
#guard pub "formula" "p → q" == "OK Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" []))"
#guard runAt "formula" "p → q" (budget "p → q" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "p → q"
-- f091: formula 'p -> q'
#guard run "formula" "p -> q" == "OK 3 Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" []))"
#guard pub "formula" "p -> q" == "OK Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" []))"
#guard runAt "formula" "p -> q" (budget "p -> q" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "p -> q"
-- f092: formula 'p → q → r'
#guard run "formula" "p → q → r" == "OK 5 Crux.Formula.Implies (Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" []))) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"r\" []))"
#guard pub "formula" "p → q → r" == "OK Crux.Formula.Implies (Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" []))) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"r\" []))"
#guard runAt "formula" "p → q → r" (budget "p → q → r" / 8) == "ERR recursion limit reached in parse_term_atom"
#guard stable "formula" "p → q → r"
-- f093: formula 'p ∧ q ∧ r'
#guard run "formula" "p ∧ q ∧ r" == "OK 5 Crux.Formula.And [Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])], Crux.Formula.Atomic (Crux.Atomic.Predicate \"r\" [])]"
#guard pub "formula" "p ∧ q ∧ r" == "OK Crux.Formula.And [Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])], Crux.Formula.Atomic (Crux.Atomic.Predicate \"r\" [])]"
#guard runAt "formula" "p ∧ q ∧ r" (budget "p ∧ q ∧ r" / 8) == "ERR recursion limit reached in parse_term_atom"
#guard stable "formula" "p ∧ q ∧ r"
-- f094: formula 'p ∨ q ∨ r'
#guard run "formula" "p ∨ q ∨ r" == "OK 5 Crux.Formula.And [Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])], Crux.Formula.Atomic (Crux.Atomic.Predicate \"r\" [])]"
#guard pub "formula" "p ∨ q ∨ r" == "OK Crux.Formula.And [Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])], Crux.Formula.Atomic (Crux.Atomic.Predicate \"r\" [])]"
#guard runAt "formula" "p ∨ q ∨ r" (budget "p ∨ q ∨ r" / 8) == "ERR recursion limit reached in parse_term_atom"
#guard stable "formula" "p ∨ q ∨ r"
-- f095: formula 'p ∧ q ∨ r → s'
#guard run "formula" "p ∧ q ∨ r → s" == "OK 7 Crux.Formula.Implies (Crux.Formula.And [Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])], Crux.Formula.Atomic (Crux.Atomic.Predicate \"r\" [])]) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"s\" []))"
#guard pub "formula" "p ∧ q ∨ r → s" == "OK Crux.Formula.Implies (Crux.Formula.And [Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])], Crux.Formula.Atomic (Crux.Atomic.Predicate \"r\" [])]) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"s\" []))"
#guard runAt "formula" "p ∧ q ∨ r → s" (budget "p ∧ q ∨ r → s" / 8) == "OK 7 Crux.Formula.Implies (Crux.Formula.And [Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])], Crux.Formula.Atomic (Crux.Atomic.Predicate \"r\" [])]) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"s\" []))"
#guard stable "formula" "p ∧ q ∨ r → s"
-- f096: formula 'p ∨ q ∧ r'
#guard run "formula" "p ∨ q ∧ r" == "OK 5 Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"r\" [])]]"
#guard pub "formula" "p ∨ q ∧ r" == "OK Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"r\" [])]]"
#guard runAt "formula" "p ∨ q ∧ r" (budget "p ∨ q ∧ r" / 8) == "ERR recursion limit reached in parse_term_atom"
#guard stable "formula" "p ∨ q ∧ r"
-- f097: formula 'p → q ∧ r'
#guard run "formula" "p → q ∧ r" == "OK 5 Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])) (Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"r\" [])])"
#guard pub "formula" "p → q ∧ r" == "OK Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])) (Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"r\" [])])"
#guard runAt "formula" "p → q ∧ r" (budget "p → q ∧ r" / 8) == "ERR recursion limit reached in parse_term_atom"
#guard stable "formula" "p → q ∧ r"
-- f098: formula '(p → q) ∧ r'
#guard run "formula" "(p → q) ∧ r" == "OK 7 Crux.Formula.And [Crux.Formula.Paren (Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" []))), Crux.Formula.Atomic (Crux.Atomic.Predicate \"r\" [])]"
#guard pub "formula" "(p → q) ∧ r" == "OK Crux.Formula.And [Crux.Formula.Paren (Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" []))), Crux.Formula.Atomic (Crux.Atomic.Predicate \"r\" [])]"
#guard runAt "formula" "(p → q) ∧ r" (budget "(p → q) ∧ r" / 8) == "ERR recursion limit reached in parse_term"
#guard stable "formula" "(p → q) ∧ r"
-- f099: formula '¬(p ∧ q)'
#guard run "formula" "¬(p ∧ q)" == "OK 6 Crux.Formula.Not (Crux.Formula.Paren (Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])]))"
#guard pub "formula" "¬(p ∧ q)" == "OK Crux.Formula.Not (Crux.Formula.Paren (Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])]))"
#guard runAt "formula" "¬(p ∧ q)" (budget "¬(p ∧ q)" / 8) == "ERR recursion limit reached in parse_formula_and"
#guard stable "formula" "¬(p ∧ q)"
-- f100: formula '¬p ∧ q'
#guard run "formula" "¬p ∧ q" == "OK 4 Crux.Formula.And [Crux.Formula.Not (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])]"
#guard pub "formula" "¬p ∧ q" == "OK Crux.Formula.And [Crux.Formula.Not (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])]"
#guard runAt "formula" "¬p ∧ q" (budget "¬p ∧ q" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "¬p ∧ q"
-- f101: formula '∀ x : Nat . p'
#guard run "formula" "∀ x : Nat . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : Nat . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : Nat . p" (budget "∀ x : Nat . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : Nat . p"
-- f102: formula 'forall x : Nat . x = x'
#guard run "formula" "forall x : Nat . x = x" == "OK 8 Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"x\"))"
#guard pub "formula" "forall x : Nat . x = x" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"x\"))"
#guard runAt "formula" "forall x : Nat . x = x" (budget "forall x : Nat . x = x" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "forall x : Nat . x = x"
-- f103: formula '∃ y : Int . y < 0'
#guard run "formula" "∃ y : Int . y < 0" == "OK 8 Crux.Formula.Exists \"y\" (Crux.Sort.Int) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"<\" [Crux.Term.Var \"y\", Crux.Term.Const (Crux.Literal.Number 0)]))"
#guard pub "formula" "∃ y : Int . y < 0" == "OK Crux.Formula.Exists \"y\" (Crux.Sort.Int) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"<\" [Crux.Term.Var \"y\", Crux.Term.Const (Crux.Literal.Number 0)]))"
#guard runAt "formula" "∃ y : Int . y < 0" (budget "∃ y : Int . y < 0" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "∃ y : Int . y < 0"
-- f104: formula 'exists y : Int . y ≥ 0'
#guard run "formula" "exists y : Int . y ≥ 0" == "OK 8 Crux.Formula.Exists \"y\" (Crux.Sort.Int) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"≥\" [Crux.Term.Var \"y\", Crux.Term.Const (Crux.Literal.Number 0)]))"
#guard pub "formula" "exists y : Int . y ≥ 0" == "OK Crux.Formula.Exists \"y\" (Crux.Sort.Int) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"≥\" [Crux.Term.Var \"y\", Crux.Term.Const (Crux.Literal.Number 0)]))"
#guard runAt "formula" "exists y : Int . y ≥ 0" (budget "exists y : Int . y ≥ 0" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "exists y : Int . y ≥ 0"
-- f105: formula 'mu X . X'
#guard run "formula" "mu X . X" == "OK 4 Crux.Formula.Mu \"X\" (Crux.Formula.Atomic (Crux.Atomic.Predicate \"X\" []))"
#guard pub "formula" "mu X . X" == "OK Crux.Formula.Mu \"X\" (Crux.Formula.Atomic (Crux.Atomic.Predicate \"X\" []))"
#guard runAt "formula" "mu X . X" (budget "mu X . X" / 8) == "ERR recursion limit reached in parse_formula_or"
#guard stable "formula" "mu X . X"
-- f106: formula 'nu X . X ∧ p'
#guard run "formula" "nu X . X ∧ p" == "OK 6 Crux.Formula.Nu \"X\" (Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"X\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])])"
#guard pub "formula" "nu X . X ∧ p" == "OK Crux.Formula.Nu \"X\" (Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"X\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])])"
#guard runAt "formula" "nu X . X ∧ p" (budget "nu X . X ∧ p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "nu X . X ∧ p"
-- f107: formula 'μ X . X'
#guard run "formula" "μ X . X" == "ERR unexpected term in formula position: Crux.Term.App (Crux.Term.Var \"μ\") (Crux.Term.Var \"X\")"
#guard pub "formula" "μ X . X" == "ERR unexpected term in formula position: Crux.Term.App (Crux.Term.Var \"μ\") (Crux.Term.Var \"X\")"
#guard runAt "formula" "μ X . X" (budget "μ X . X" / 8) == "ERR recursion limit reached in parse_term_atom"
#guard stable "formula" "μ X . X"
-- f108: formula '∀ x : Nat . ∃ y : Nat . x < y'
#guard run "formula" "∀ x : Nat . ∃ y : Nat . x < y" == "OK 13 Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Exists \"y\" (Crux.Sort.Nat) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"<\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])))"
#guard pub "formula" "∀ x : Nat . ∃ y : Nat . x < y" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Exists \"y\" (Crux.Sort.Nat) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"<\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])))"
#guard runAt "formula" "∀ x : Nat . ∃ y : Nat . x < y" (budget "∀ x : Nat . ∃ y : Nat . x < y" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "∀ x : Nat . ∃ y : Nat . x < y"
-- f109: formula '∀ f : Nat → Nat . f x = x'
#guard run "formula" "∀ f : Nat → Nat . f x = x" == "OK 11 Crux.Formula.Forall \"f\" (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Nat)) (Crux.Formula.Eq (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")) (Crux.Term.Var \"x\"))"
#guard pub "formula" "∀ f : Nat → Nat . f x = x" == "OK Crux.Formula.Forall \"f\" (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Nat)) (Crux.Formula.Eq (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")) (Crux.Term.Var \"x\"))"
#guard runAt "formula" "∀ f : Nat → Nat . f x = x" (budget "∀ f : Nat → Nat . f x = x" / 8) == "OK 11 Crux.Formula.Forall \"f\" (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Nat)) (Crux.Formula.Eq (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")) (Crux.Term.Var \"x\"))"
#guard stable "formula" "∀ f : Nat → Nat . f x = x"
-- f110: formula '∀ x : (Nat) . p'
#guard run "formula" "∀ x : (Nat) . p" == "OK 8 Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : (Nat) . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : (Nat) . p" (budget "∀ x : (Nat) . p" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "∀ x : (Nat) . p"
-- f111: formula '∀ x : Foo . p'
#guard run "formula" "∀ x : Foo . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.User \"Foo\") (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : Foo . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.User \"Foo\") (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : Foo . p" (budget "∀ x : Foo . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : Foo . p"
-- f112: formula '∀ x : Nat → Int → Bool . p'
#guard run "formula" "∀ x : Nat → Int → Bool . p" == "OK 10 Crux.Formula.Forall \"x\" (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Arrow (Crux.Sort.Int) (Crux.Sort.Bool))) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : Nat → Int → Bool . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Arrow (Crux.Sort.Int) (Crux.Sort.Bool))) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : Nat → Int → Bool . p" (budget "∀ x : Nat → Int → Bool . p" / 8) == "OK 10 Crux.Formula.Forall \"x\" (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Arrow (Crux.Sort.Int) (Crux.Sort.Bool))) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard stable "formula" "∀ x : Nat → Int → Bool . p"
-- f113: formula '∀ x : (Nat → Int) → Bool . p'
#guard run "formula" "∀ x : (Nat → Int) → Bool . p" == "OK 12 Crux.Formula.Forall \"x\" (Crux.Sort.Arrow (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Int)) (Crux.Sort.Bool)) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : (Nat → Int) → Bool . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Arrow (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Int)) (Crux.Sort.Bool)) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : (Nat → Int) → Bool . p" (budget "∀ x : (Nat → Int) → Bool . p" / 8) == "OK 12 Crux.Formula.Forall \"x\" (Crux.Sort.Arrow (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Int)) (Crux.Sort.Bool)) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard stable "formula" "∀ x : (Nat → Int) → Bool . p"
-- f114: formula 'x = y'
#guard run "formula" "x = y" == "OK 3 Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")"
#guard pub "formula" "x = y" == "OK Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")"
#guard runAt "formula" "x = y" (budget "x = y" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "x = y"
-- f115: formula 'x == y'
#guard run "formula" "x == y" == "OK 3 Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")"
#guard pub "formula" "x == y" == "OK Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")"
#guard runAt "formula" "x == y" (budget "x == y" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "x == y"
-- f116: formula 'x ≡ y'
#guard run "formula" "x ≡ y" == "OK 3 Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")"
#guard pub "formula" "x ≡ y" == "OK Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")"
#guard runAt "formula" "x ≡ y" (budget "x ≡ y" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "x ≡ y"
-- f117: formula 'x != y'
#guard run "formula" "x != y" == "OK 3 Crux.Formula.Not (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\"))"
#guard pub "formula" "x != y" == "OK Crux.Formula.Not (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\"))"
#guard runAt "formula" "x != y" (budget "x != y" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "x != y"
-- f118: formula 'x ≠ y'
#guard run "formula" "x ≠ y" == "OK 3 Crux.Formula.Not (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\"))"
#guard pub "formula" "x ≠ y" == "OK Crux.Formula.Not (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\"))"
#guard runAt "formula" "x ≠ y" (budget "x ≠ y" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "x ≠ y"
-- f119: formula 'x < y'
#guard run "formula" "x < y" == "OK 3 Crux.Formula.Atomic (Crux.Atomic.Predicate \"<\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])"
#guard pub "formula" "x < y" == "OK Crux.Formula.Atomic (Crux.Atomic.Predicate \"<\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])"
#guard runAt "formula" "x < y" (budget "x < y" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "x < y"
-- f120: formula 'x <= y'
#guard run "formula" "x <= y" == "OK 3 Crux.Formula.Atomic (Crux.Atomic.Predicate \"≤\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])"
#guard pub "formula" "x <= y" == "OK Crux.Formula.Atomic (Crux.Atomic.Predicate \"≤\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])"
#guard runAt "formula" "x <= y" (budget "x <= y" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "x <= y"
-- f121: formula 'x ≤ y'
#guard run "formula" "x ≤ y" == "OK 3 Crux.Formula.Atomic (Crux.Atomic.Predicate \"≤\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])"
#guard pub "formula" "x ≤ y" == "OK Crux.Formula.Atomic (Crux.Atomic.Predicate \"≤\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])"
#guard runAt "formula" "x ≤ y" (budget "x ≤ y" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "x ≤ y"
-- f122: formula 'x > y'
#guard run "formula" "x > y" == "OK 3 Crux.Formula.Atomic (Crux.Atomic.Predicate \">\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])"
#guard pub "formula" "x > y" == "OK Crux.Formula.Atomic (Crux.Atomic.Predicate \">\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])"
#guard runAt "formula" "x > y" (budget "x > y" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "x > y"
-- f123: formula 'x >= y'
#guard run "formula" "x >= y" == "OK 3 Crux.Formula.Atomic (Crux.Atomic.Predicate \"≥\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])"
#guard pub "formula" "x >= y" == "OK Crux.Formula.Atomic (Crux.Atomic.Predicate \"≥\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])"
#guard runAt "formula" "x >= y" (budget "x >= y" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "x >= y"
-- f124: formula 'x ≥ y'
#guard run "formula" "x ≥ y" == "OK 3 Crux.Formula.Atomic (Crux.Atomic.Predicate \"≥\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])"
#guard pub "formula" "x ≥ y" == "OK Crux.Formula.Atomic (Crux.Atomic.Predicate \"≥\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])"
#guard runAt "formula" "x ≥ y" (budget "x ≥ y" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "x ≥ y"
-- f125: formula 'f x = g y'
#guard run "formula" "f x = g y" == "OK 5 Crux.Formula.Eq (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")) (Crux.Term.App (Crux.Term.Var \"g\") (Crux.Term.Var \"y\"))"
#guard pub "formula" "f x = g y" == "OK Crux.Formula.Eq (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")) (Crux.Term.App (Crux.Term.Var \"g\") (Crux.Term.Var \"y\"))"
#guard runAt "formula" "f x = g y" (budget "f x = g y" / 8) == "ERR recursion limit reached in parse_term_atom"
#guard stable "formula" "f x = g y"
-- f126: formula 'a + b = c * d'
#guard run "formula" "a + b = c * d" == "OK 7 Crux.Formula.Eq (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"c\") (Crux.Term.Var \"d\"))"
#guard pub "formula" "a + b = c * d" == "OK Crux.Formula.Eq (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"c\") (Crux.Term.Var \"d\"))"
#guard runAt "formula" "a + b = c * d" (budget "a + b = c * d" / 8) == "OK 7 Crux.Formula.Eq (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.BinOp (Crux.BinOp.Mul) (Crux.Term.Var \"c\") (Crux.Term.Var \"d\"))"
#guard stable "formula" "a + b = c * d"
-- f127: formula '(x, y) = z'
#guard run "formula" "(x, y) = z" == "ERR expected Crux.Token.RParen, got Crux.Token.Comma"
#guard pub "formula" "(x, y) = z" == "ERR expected Crux.Token.RParen, got Crux.Token.Comma"
#guard runAt "formula" "(x, y) = z" (budget "(x, y) = z" / 8) == "ERR recursion limit reached in parse_term"
#guard stable "formula" "(x, y) = z"
-- f128: formula '() = ()'
#guard run "formula" "() = ()" == "ERR unexpected token in term: Crux.Token.RParen"
#guard pub "formula" "() = ()" == "ERR unexpected token in term: Crux.Token.RParen"
#guard runAt "formula" "() = ()" (budget "() = ()" / 8) == "ERR recursion limit reached in parse_formula_and"
#guard stable "formula" "() = ()"
-- f129: formula '"s" = "t"'
#guard run "formula" "\"s\" = \"t\"" == "OK 3 Crux.Formula.Eq (Crux.Term.Const (Crux.Literal.Str \"s\")) (Crux.Term.Const (Crux.Literal.Str \"t\"))"
#guard pub "formula" "\"s\" = \"t\"" == "OK Crux.Formula.Eq (Crux.Term.Const (Crux.Literal.Str \"s\")) (Crux.Term.Const (Crux.Literal.Str \"t\"))"
#guard runAt "formula" "\"s\" = \"t\"" (budget "\"s\" = \"t\"" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "\"s\" = \"t\""
-- f130: formula 'if p then a else b = c'
#guard run "formula" "if p then a else b = c" == "OK 8 Crux.Formula.Eq (Crux.Term.IfThenElse (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"c\")"
#guard pub "formula" "if p then a else b = c" == "OK Crux.Formula.Eq (Crux.Term.IfThenElse (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])) (Crux.Term.Var \"a\") (Crux.Term.Var \"b\")) (Crux.Term.Var \"c\")"
#guard runAt "formula" "if p then a else b = c" (budget "if p then a else b = c" / 8) == "ERR recursion limit reached in parse_formula_and"
#guard stable "formula" "if p then a else b = c"
-- f131: formula 'fun x : Nat => x = y'
#guard run "formula" "fun x : Nat => x = y" == "OK 8 Crux.Formula.Eq (Crux.Term.Lambda \"x\" (Crux.Sort.Nat) (Crux.Term.Var \"x\")) (Crux.Term.Var \"y\")"
#guard pub "formula" "fun x : Nat => x = y" == "OK Crux.Formula.Eq (Crux.Term.Lambda \"x\" (Crux.Sort.Nat) (Crux.Term.Var \"x\")) (Crux.Term.Var \"y\")"
#guard runAt "formula" "fun x : Nat => x = y" (budget "fun x : Nat => x = y" / 8) == "OK 8 Crux.Formula.Eq (Crux.Term.Lambda \"x\" (Crux.Sort.Nat) (Crux.Term.Var \"x\")) (Crux.Term.Var \"y\")"
#guard stable "formula" "fun x : Nat => x = y"
-- f132: formula 'rec f = f'
#guard run "formula" "rec f = f" == "ERR unexpected term in formula position: Crux.Term.Rec \"f\" (Crux.Term.Var \"f\")"
#guard pub "formula" "rec f = f" == "ERR unexpected term in formula position: Crux.Term.Rec \"f\" (Crux.Term.Var \"f\")"
#guard runAt "formula" "rec f = f" (budget "rec f = f" / 8) == "ERR recursion limit reached in parse_term_atom"
#guard stable "formula" "rec f = f"
-- f133: formula 'равенство(x, y)'
#guard run "formula" "равенство(x, y)" == "OK 6 Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")"
#guard pub "formula" "равенство(x, y)" == "OK Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")"
#guard runAt "formula" "равенство(x, y)" (budget "равенство(x, y)" / 8) == "OK 6 Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")"
#guard stable "formula" "равенство(x, y)"
-- f134: formula 'равенство(f x, y + 1)'
#guard run "formula" "равенство(f x, y + 1)" == "OK 9 Crux.Formula.Eq (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"y\") (Crux.Term.Const (Crux.Literal.Number 1)))"
#guard pub "formula" "равенство(f x, y + 1)" == "OK Crux.Formula.Eq (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"y\") (Crux.Term.Const (Crux.Literal.Number 1)))"
#guard runAt "formula" "равенство(f x, y + 1)" (budget "равенство(f x, y + 1)" / 8) == "OK 9 Crux.Formula.Eq (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"y\") (Crux.Term.Const (Crux.Literal.Number 1)))"
#guard stable "formula" "равенство(f x, y + 1)"
-- f135: formula 'p ⊢ q'
#guard run "formula" "p ⊢ q" == "OK 1 Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])"
#guard pub "formula" "p ⊢ q" == "OK Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])"
#guard runAt "formula" "p ⊢ q" (budget "p ⊢ q" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "p ⊢ q"
-- f136: formula 'p ⊨ q'
#guard run "formula" "p ⊨ q" == "OK 1 Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])"
#guard pub "formula" "p ⊨ q" == "OK Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])"
#guard runAt "formula" "p ⊨ q" (budget "p ⊨ q" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "p ⊨ q"
-- f137: formula 'p ↔ q'
#guard run "formula" "p ↔ q" == "OK 1 Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])"
#guard pub "formula" "p ↔ q" == "OK Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])"
#guard runAt "formula" "p ↔ q" (budget "p ↔ q" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "p ↔ q"
-- f138: formula 'x = y ∧ y = z → x = z'
#guard run "formula" "x = y ∧ y = z → x = z" == "OK 11 Crux.Formula.Implies (Crux.Formula.And [Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\"), Crux.Formula.Eq (Crux.Term.Var \"y\") (Crux.Term.Var \"z\")]) (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"z\"))"
#guard pub "formula" "x = y ∧ y = z → x = z" == "OK Crux.Formula.Implies (Crux.Formula.And [Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\"), Crux.Formula.Eq (Crux.Term.Var \"y\") (Crux.Term.Var \"z\")]) (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"z\"))"
#guard runAt "formula" "x = y ∧ y = z → x = z" (budget "x = y ∧ y = z → x = z" / 8) == "OK 11 Crux.Formula.Implies (Crux.Formula.And [Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\"), Crux.Formula.Eq (Crux.Term.Var \"y\") (Crux.Term.Var \"z\")]) (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"z\"))"
#guard stable "formula" "x = y ∧ y = z → x = z"
-- f139: formula 'S 1'
#guard run "formula" "S 1" == "ERR unexpected term in formula position: Crux.Term.App (Crux.Term.Var \"S\") (Crux.Term.Const (Crux.Literal.Number 1))"
#guard pub "formula" "S 1" == "ERR unexpected term in formula position: Crux.Term.App (Crux.Term.Var \"S\") (Crux.Term.Const (Crux.Literal.Number 1))"
#guard runAt "formula" "S 1" (budget "S 1" / 8) == "ERR recursion limit reached in parse_term"
#guard stable "formula" "S 1"
-- f140: formula 'сила(S, p)'
#guard run "formula" "сила(S, p)" == "ERR unexpected token in term: Crux.Token.Sila"
#guard pub "formula" "сила(S, p)" == "ERR unexpected token in term: Crux.Token.Sila"
#guard runAt "formula" "сила(S, p)" (budget "сила(S, p)" / 8) == "ERR unexpected token in term: Crux.Token.Sila"
#guard stable "formula" "сила(S, p)"
-- f141: formula ''
#guard run "formula" "" == "ERR unexpected token in term: Crux.Token.Eof"
#guard pub "formula" "" == "ERR unexpected token in term: Crux.Token.Eof"
#guard runAt "formula" "" (budget "" / 8) == "ERR recursion limit reached in parse_formula_and"
#guard stable "formula" ""
-- f142: formula '¬'
#guard run "formula" "¬" == "ERR unexpected token in term: Crux.Token.Eof"
#guard pub "formula" "¬" == "ERR unexpected token in term: Crux.Token.Eof"
#guard runAt "formula" "¬" (budget "¬" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "¬"
-- f143: formula 'p ∧'
#guard run "formula" "p ∧" == "ERR unexpected token in term: Crux.Token.Eof"
#guard pub "formula" "p ∧" == "ERR unexpected token in term: Crux.Token.Eof"
#guard runAt "formula" "p ∧" (budget "p ∧" / 8) == "ERR recursion limit reached in parse_term"
#guard stable "formula" "p ∧"
-- f144: formula 'p ∨'
#guard run "formula" "p ∨" == "ERR unexpected token in term: Crux.Token.Eof"
#guard pub "formula" "p ∨" == "ERR unexpected token in term: Crux.Token.Eof"
#guard runAt "formula" "p ∨" (budget "p ∨" / 8) == "ERR recursion limit reached in parse_term"
#guard stable "formula" "p ∨"
-- f145: formula 'p →'
#guard run "formula" "p →" == "ERR unexpected token in term: Crux.Token.Eof"
#guard pub "formula" "p →" == "ERR unexpected token in term: Crux.Token.Eof"
#guard runAt "formula" "p →" (budget "p →" / 8) == "ERR recursion limit reached in parse_term"
#guard stable "formula" "p →"
-- f146: formula '(p'
#guard run "formula" "(p" == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard pub "formula" "(p" == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard runAt "formula" "(p" (budget "(p" / 8) == "ERR recursion limit reached in parse_formula"
#guard stable "formula" "(p"
-- f147: formula '(p ∧ q'
#guard run "formula" "(p ∧ q" == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard pub "formula" "(p ∧ q" == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard runAt "formula" "(p ∧ q" (budget "(p ∧ q" / 8) == "ERR recursion limit reached in parse_formula_or"
#guard stable "formula" "(p ∧ q"
-- f148: formula '∀ 1 : Nat . p'
#guard run "formula" "∀ 1 : Nat . p" == "ERR expected ident after forall, got Crux.Token.Number 1"
#guard pub "formula" "∀ 1 : Nat . p" == "ERR expected ident after forall, got Crux.Token.Number 1"
#guard runAt "formula" "∀ 1 : Nat . p" (budget "∀ 1 : Nat . p" / 8) == "ERR expected ident after forall, got Crux.Token.Number 1"
#guard stable "formula" "∀ 1 : Nat . p"
-- f149: formula '∀ x Nat . p'
#guard run "formula" "∀ x Nat . p" == "ERR expected Crux.Token.Colon, got Crux.Token.Ident \"Nat\""
#guard pub "formula" "∀ x Nat . p" == "ERR expected Crux.Token.Colon, got Crux.Token.Ident \"Nat\""
#guard runAt "formula" "∀ x Nat . p" (budget "∀ x Nat . p" / 8) == "ERR expected Crux.Token.Colon, got Crux.Token.Ident \"Nat\""
#guard stable "formula" "∀ x Nat . p"
-- f150: formula '∀ x : Nat p'
#guard run "formula" "∀ x : Nat p" == "ERR expected Crux.Token.Dot, got Crux.Token.Ident \"p\""
#guard pub "formula" "∀ x : Nat p" == "ERR expected Crux.Token.Dot, got Crux.Token.Ident \"p\""
#guard runAt "formula" "∀ x : Nat p" (budget "∀ x : Nat p" / 8) == "ERR expected Crux.Token.Dot, got Crux.Token.Ident \"p\""
#guard stable "formula" "∀ x : Nat p"
-- f151: formula '∀ x : . p'
#guard run "formula" "∀ x : . p" == "ERR unexpected token in sort: Crux.Token.Dot"
#guard pub "formula" "∀ x : . p" == "ERR unexpected token in sort: Crux.Token.Dot"
#guard runAt "formula" "∀ x : . p" (budget "∀ x : . p" / 8) == "ERR unexpected token in sort: Crux.Token.Dot"
#guard stable "formula" "∀ x : . p"
-- f152: formula '∃ x : Nat'
#guard run "formula" "∃ x : Nat" == "ERR expected Crux.Token.Dot, got Crux.Token.Eof"
#guard pub "formula" "∃ x : Nat" == "ERR expected Crux.Token.Dot, got Crux.Token.Eof"
#guard runAt "formula" "∃ x : Nat" (budget "∃ x : Nat" / 8) == "ERR expected Crux.Token.Dot, got Crux.Token.Eof"
#guard stable "formula" "∃ x : Nat"
-- f153: formula 'mu 1 . p'
#guard run "formula" "mu 1 . p" == "ERR expected ident after μ, got Crux.Token.Number 1"
#guard pub "formula" "mu 1 . p" == "ERR expected ident after μ, got Crux.Token.Number 1"
#guard runAt "formula" "mu 1 . p" (budget "mu 1 . p" / 8) == "ERR expected ident after μ, got Crux.Token.Number 1"
#guard stable "formula" "mu 1 . p"
-- f154: formula 'mu X X'
#guard run "formula" "mu X X" == "ERR expected Crux.Token.Dot, got Crux.Token.Ident \"X\""
#guard pub "formula" "mu X X" == "ERR expected Crux.Token.Dot, got Crux.Token.Ident \"X\""
#guard runAt "formula" "mu X X" (budget "mu X X" / 8) == "ERR expected Crux.Token.Dot, got Crux.Token.Ident \"X\""
#guard stable "formula" "mu X X"
-- f155: formula 'nu . p'
#guard run "formula" "nu . p" == "ERR expected ident after ν, got Crux.Token.Dot"
#guard pub "formula" "nu . p" == "ERR expected ident after ν, got Crux.Token.Dot"
#guard runAt "formula" "nu . p" (budget "nu . p" / 8) == "ERR expected ident after ν, got Crux.Token.Dot"
#guard stable "formula" "nu . p"
-- f156: formula 'x + 1'
#guard run "formula" "x + 1" == "ERR unexpected term in formula position: Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"x\") (Crux.Term.Const (Crux.Literal.Number 1))"
#guard pub "formula" "x + 1" == "ERR unexpected term in formula position: Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"x\") (Crux.Term.Const (Crux.Literal.Number 1))"
#guard runAt "formula" "x + 1" (budget "x + 1" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "x + 1"
-- f157: formula 'f x'
#guard run "formula" "f x" == "ERR unexpected term in formula position: Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")"
#guard pub "formula" "f x" == "ERR unexpected term in formula position: Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")"
#guard runAt "formula" "f x" (budget "f x" / 8) == "ERR recursion limit reached in parse_term"
#guard stable "formula" "f x"
-- f158: formula 'x = '
#guard run "formula" "x = " == "ERR unexpected token in term: Crux.Token.Eof"
#guard pub "formula" "x = " == "ERR unexpected token in term: Crux.Token.Eof"
#guard runAt "formula" "x = " (budget "x = " / 8) == "ERR recursion limit reached in parse_term"
#guard stable "formula" "x = "
-- f159: formula 'x <'
#guard run "formula" "x <" == "ERR unexpected token in term: Crux.Token.Eof"
#guard pub "formula" "x <" == "ERR unexpected token in term: Crux.Token.Eof"
#guard runAt "formula" "x <" (budget "x <" / 8) == "ERR recursion limit reached in parse_term"
#guard stable "formula" "x <"
-- f160: formula 'равенство(x y)'
#guard run "formula" "равенство(x y)" == "ERR expected Crux.Token.Comma, got Crux.Token.RParen"
#guard pub "formula" "равенство(x y)" == "ERR expected Crux.Token.Comma, got Crux.Token.RParen"
#guard runAt "formula" "равенство(x y)" (budget "равенство(x y)" / 8) == "ERR recursion limit reached in parse_term_atom"
#guard stable "formula" "равенство(x y)"
-- f161: formula 'равенство x, y)'
#guard run "formula" "равенство x, y)" == "ERR expected Crux.Token.LParen, got Crux.Token.Ident \"x\""
#guard pub "formula" "равенство x, y)" == "ERR expected Crux.Token.LParen, got Crux.Token.Ident \"x\""
#guard runAt "formula" "равенство x, y)" (budget "равенство x, y)" / 8) == "ERR expected Crux.Token.LParen, got Crux.Token.Ident \"x\""
#guard stable "formula" "равенство x, y)"
-- f162: formula 'равенство(x, y'
#guard run "formula" "равенство(x, y" == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard pub "formula" "равенство(x, y" == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard runAt "formula" "равенство(x, y" (budget "равенство(x, y" / 8) == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard stable "formula" "равенство(x, y"
-- f163: formula 'импликация'
#guard run "formula" "импликация" == "ERR unexpected token in term: Crux.Token.Imply"
#guard pub "formula" "импликация" == "ERR unexpected token in term: Crux.Token.Imply"
#guard runAt "formula" "импликация" (budget "импликация" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "импликация"
-- f164: formula 'конъюнкция(p, q)'
#guard run "formula" "конъюнкция(p, q)" == "ERR unexpected token in term: Crux.Token.Conj"
#guard pub "formula" "конъюнкция(p, q)" == "ERR unexpected token in term: Crux.Token.Conj"
#guard runAt "formula" "конъюнкция(p, q)" (budget "конъюнкция(p, q)" / 8) == "ERR unexpected token in term: Crux.Token.Conj"
#guard stable "formula" "конъюнкция(p, q)"
-- f165: formula 'дизъюнкция'
#guard run "formula" "дизъюнкция" == "ERR unexpected token in term: Crux.Token.Disj"
#guard pub "formula" "дизъюнкция" == "ERR unexpected token in term: Crux.Token.Disj"
#guard runAt "formula" "дизъюнкция" (budget "дизъюнкция" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "дизъюнкция"
-- f166: formula 'отрицание p'
#guard run "formula" "отрицание p" == "ERR unexpected token in term: Crux.Token.Neg"
#guard pub "formula" "отрицание p" == "ERR unexpected token in term: Crux.Token.Neg"
#guard runAt "formula" "отрицание p" (budget "отрицание p" / 8) == "ERR recursion limit reached in parse_term"
#guard stable "formula" "отрицание p"
-- f167: formula 'для всех x'
#guard run "formula" "для всех x" == "ERR unexpected term in formula position: Crux.Term.App (Crux.Term.Var \"для\") (Crux.Term.App (Crux.Term.Var \"всех\") (Crux.Term.Var \"x\"))"
#guard pub "formula" "для всех x" == "ERR unexpected term in formula position: Crux.Term.App (Crux.Term.Var \"для\") (Crux.Term.App (Crux.Term.Var \"всех\") (Crux.Term.Var \"x\"))"
#guard runAt "formula" "для всех x" (budget "для всех x" / 8) == "ERR recursion limit reached in parse_term_binop"
#guard stable "formula" "для всех x"
-- f168: formula 'существует x'
#guard run "formula" "существует x" == "ERR unexpected token in term: Crux.Token.Sushchestvuet"
#guard pub "formula" "существует x" == "ERR unexpected token in term: Crux.Token.Sushchestvuet"
#guard runAt "formula" "существует x" (budget "существует x" / 8) == "ERR recursion limit reached in parse_term"
#guard stable "formula" "существует x"
-- f169: formula 'рекурсия'
#guard run "formula" "рекурсия" == "ERR unexpected token in term: Crux.Token.Rekursiya"
#guard pub "formula" "рекурсия" == "ERR unexpected token in term: Crux.Token.Rekursiya"
#guard runAt "formula" "рекурсия" (budget "рекурсия" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "рекурсия"
-- f170: formula 'состояние'
#guard run "formula" "состояние" == "ERR unexpected token in term: Crux.Token.Sostoyanie"
#guard pub "formula" "состояние" == "ERR unexpected token in term: Crux.Token.Sostoyanie"
#guard runAt "formula" "состояние" (budget "состояние" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "состояние"
-- f171: formula 'p q'
#guard run "formula" "p q" == "ERR unexpected term in formula position: Crux.Term.App (Crux.Term.Var \"p\") (Crux.Term.Var \"q\")"
#guard pub "formula" "p q" == "ERR unexpected term in formula position: Crux.Term.App (Crux.Term.Var \"p\") (Crux.Term.Var \"q\")"
#guard runAt "formula" "p q" (budget "p q" / 8) == "ERR recursion limit reached in parse_term"
#guard stable "formula" "p q"
-- f172: formula 'p )'
#guard run "formula" "p )" == "OK 1 Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])"
#guard pub "formula" "p )" == "OK Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])"
#guard runAt "formula" "p )" (budget "p )" / 8) == "ERR recursion limit reached in parse_term"
#guard stable "formula" "p )"
-- f173: formula '∀ x : Prop . p'
#guard run "formula" "∀ x : Prop . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.Prop) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : Prop . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Prop) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : Prop . p" (budget "∀ x : Prop . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : Prop . p"
-- f174: formula '∀ x : Type . p'
#guard run "formula" "∀ x : Type . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.Type) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : Type . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Type) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : Type . p" (budget "∀ x : Type . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : Type . p"
-- f175: formula '∀ x : Nat . p'
#guard run "formula" "∀ x : Nat . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : Nat . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : Nat . p" (budget "∀ x : Nat . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : Nat . p"
-- f176: formula '∀ x : Int . p'
#guard run "formula" "∀ x : Int . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.Int) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : Int . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Int) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : Int . p" (budget "∀ x : Int . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : Int . p"
-- f177: formula '∀ x : Bool . p'
#guard run "formula" "∀ x : Bool . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.Bool) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : Bool . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Bool) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : Bool . p" (budget "∀ x : Bool . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : Bool . p"
-- f178: formula '∀ x : State . p'
#guard run "formula" "∀ x : State . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.State) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : State . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.State) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : State . p" (budget "∀ x : State . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : State . p"
-- f179: formula '∀ x : Formula . p'
#guard run "formula" "∀ x : Formula . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.Formula) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : Formula . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Formula) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : Formula . p" (budget "∀ x : Formula . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : Formula . p"
-- f180: formula '∀ x : Term . p'
#guard run "formula" "∀ x : Term . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.Term) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : Term . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Term) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : Term . p" (budget "∀ x : Term . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : Term . p"
-- f181: formula '∀ x : MIR . p'
#guard run "formula" "∀ x : MIR . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.MIR) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : MIR . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.MIR) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : MIR . p" (budget "∀ x : MIR . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : MIR . p"
-- f182: formula '∀ x : Core . p'
#guard run "formula" "∀ x : Core . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.Core) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : Core . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Core) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : Core . p" (budget "∀ x : Core . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : Core . p"
-- f183: formula '∀ x : Haskell . p'
#guard run "formula" "∀ x : Haskell . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.Haskell) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : Haskell . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Haskell) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : Haskell . p" (budget "∀ x : Haskell . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : Haskell . p"
-- f184: formula '∀ x : Rust . p'
#guard run "formula" "∀ x : Rust . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.Rust) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : Rust . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Rust) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : Rust . p" (budget "∀ x : Rust . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : Rust . p"
-- f185: formula '∀ x : Z3Expr . p'
#guard run "formula" "∀ x : Z3Expr . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.Z3Expr) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : Z3Expr . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.Z3Expr) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : Z3Expr . p" (budget "∀ x : Z3Expr . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : Z3Expr . p"
-- f186: formula '∀ x : LeanTerm . p'
#guard run "formula" "∀ x : LeanTerm . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.LeanTerm) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : LeanTerm . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.LeanTerm) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : LeanTerm . p" (budget "∀ x : LeanTerm . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : LeanTerm . p"
-- f187: formula '∀ x : SASAbs . p'
#guard run "formula" "∀ x : SASAbs . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.SASAbs) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : SASAbs . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.SASAbs) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : SASAbs . p" (budget "∀ x : SASAbs . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : SASAbs . p"
-- f188: formula '∀ x : User1 . p'
#guard run "formula" "∀ x : User1 . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.User \"User1\") (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : User1 . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.User \"User1\") (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : User1 . p" (budget "∀ x : User1 . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : User1 . p"
-- f189: formula '∀ x : Ω . p'
#guard run "formula" "∀ x : Ω . p" == "OK 6 Crux.Formula.Forall \"x\" (Crux.Sort.User \"Ω\") (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "formula" "∀ x : Ω . p" == "OK Crux.Formula.Forall \"x\" (Crux.Sort.User \"Ω\") (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "formula" "∀ x : Ω . p" (budget "∀ x : Ω . p" / 8) == "ERR recursion limit reached in parse_formula_atom"
#guard stable "formula" "∀ x : Ω . p"
-- r190: russian 'равенство(x, y)'
#guard run "russian" "равенство(x, y)" == "OK 6 Crux.RussianForm.Ravnostvo (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")"
#guard pub "russian" "равенство(x, y)" == "OK Crux.RussianForm.Ravnostvo (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")"
#guard runAt "russian" "равенство(x, y)" (budget "равенство(x, y)" / 8) == "OK 6 Crux.RussianForm.Ravnostvo (Crux.Term.Var \"x\") (Crux.Term.Var \"y\")"
#guard stable "russian" "равенство(x, y)"
-- r191: russian 'равенство(f x, y + 1)'
#guard run "russian" "равенство(f x, y + 1)" == "OK 9 Crux.RussianForm.Ravnostvo (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"y\") (Crux.Term.Const (Crux.Literal.Number 1)))"
#guard pub "russian" "равенство(f x, y + 1)" == "OK Crux.RussianForm.Ravnostvo (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"y\") (Crux.Term.Const (Crux.Literal.Number 1)))"
#guard runAt "russian" "равенство(f x, y + 1)" (budget "равенство(f x, y + 1)" / 8) == "OK 9 Crux.RussianForm.Ravnostvo (Crux.Term.App (Crux.Term.Var \"f\") (Crux.Term.Var \"x\")) (Crux.Term.BinOp (Crux.BinOp.Add) (Crux.Term.Var \"y\") (Crux.Term.Const (Crux.Literal.Number 1)))"
#guard stable "russian" "равенство(f x, y + 1)"
-- r192: russian 'равенство((a, b), ())'
#guard run "russian" "равенство((a, b), ())" == "OK 11 Crux.RussianForm.Ravnostvo (Crux.Term.Tuple [Crux.Term.Var \"a\", Crux.Term.Var \"b\"]) (Crux.Term.Nil)"
#guard pub "russian" "равенство((a, b), ())" == "OK Crux.RussianForm.Ravnostvo (Crux.Term.Tuple [Crux.Term.Var \"a\", Crux.Term.Var \"b\"]) (Crux.Term.Nil)"
#guard runAt "russian" "равенство((a, b), ())" (budget "равенство((a, b), ())" / 8) == "OK 11 Crux.RussianForm.Ravnostvo (Crux.Term.Tuple [Crux.Term.Var \"a\", Crux.Term.Var \"b\"]) (Crux.Term.Nil)"
#guard stable "russian" "равенство((a, b), ())"
-- r193: russian 'сила(S, p)'
#guard run "russian" "сила(S, p)" == "OK 6 Crux.RussianForm.Sila (Crux.State.S) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "russian" "сила(S, p)" == "OK Crux.RussianForm.Sila (Crux.State.S) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "russian" "сила(S, p)" (budget "сила(S, p)" / 8) == "OK 6 Crux.RussianForm.Sila (Crux.State.S) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard stable "russian" "сила(S, p)"
-- r194: russian 'сила(S0, p ∧ q)'
#guard run "russian" "сила(S0, p ∧ q)" == "OK 8 Crux.RussianForm.Sila (Crux.State.S0) (Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])])"
#guard pub "russian" "сила(S0, p ∧ q)" == "OK Crux.RussianForm.Sila (Crux.State.S0) (Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])])"
#guard runAt "russian" "сила(S0, p ∧ q)" (budget "сила(S0, p ∧ q)" / 8) == "OK 8 Crux.RussianForm.Sila (Crux.State.S0) (Crux.Formula.And [Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []), Crux.Formula.Atomic (Crux.Atomic.Predicate \"q\" [])])"
#guard stable "russian" "сила(S0, p ∧ q)"
-- r195: russian 'сила(S 3, p)'
#guard run "russian" "сила(S 3, p)" == "OK 7 Crux.RussianForm.Sila (Crux.State.Sn 3) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "russian" "сила(S 3, p)" == "OK Crux.RussianForm.Sila (Crux.State.Sn 3) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "russian" "сила(S 3, p)" (budget "сила(S 3, p)" / 8) == "OK 7 Crux.RussianForm.Sila (Crux.State.Sn 3) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard stable "russian" "сила(S 3, p)"
-- r196: russian 'сила(S12, x = y)'
#guard run "russian" "сила(S12, x = y)" == "OK 8 Crux.RussianForm.Sila (Crux.State.Sn 12) (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\"))"
#guard pub "russian" "сила(S12, x = y)" == "OK Crux.RussianForm.Sila (Crux.State.Sn 12) (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\"))"
#guard runAt "russian" "сила(S12, x = y)" (budget "сила(S12, x = y)" / 8) == "OK 8 Crux.RussianForm.Sila (Crux.State.Sn 12) (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"y\"))"
#guard stable "russian" "сила(S12, x = y)"
-- r197: russian 'сила(Sx, p)'
#guard run "russian" "сила(Sx, p)" == "ERR invalid state name: Sx"
#guard pub "russian" "сила(Sx, p)" == "ERR invalid state name: Sx"
#guard runAt "russian" "сила(Sx, p)" (budget "сила(Sx, p)" / 8) == "ERR invalid state name: Sx"
#guard stable "russian" "сила(Sx, p)"
-- r198: russian 'сила(T, p)'
#guard run "russian" "сила(T, p)" == "ERR unexpected token in state: Crux.Token.Ident \"T\""
#guard pub "russian" "сила(T, p)" == "ERR unexpected token in state: Crux.Token.Ident \"T\""
#guard runAt "russian" "сила(T, p)" (budget "сила(T, p)" / 8) == "ERR unexpected token in state: Crux.Token.Ident \"T\""
#guard stable "russian" "сила(T, p)"
-- r199: russian 'сила(S, p'
#guard run "russian" "сила(S, p" == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard pub "russian" "сила(S, p" == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard runAt "russian" "сила(S, p" (budget "сила(S, p" / 8) == "ERR recursion limit reached in parse_term_atom"
#guard stable "russian" "сила(S, p"
-- r200: russian 'сила S, p)'
#guard run "russian" "сила S, p)" == "ERR expected Crux.Token.LParen, got Crux.Token.Ident \"S\""
#guard pub "russian" "сила S, p)" == "ERR expected Crux.Token.LParen, got Crux.Token.Ident \"S\""
#guard runAt "russian" "сила S, p)" (budget "сила S, p)" / 8) == "ERR expected Crux.Token.LParen, got Crux.Token.Ident \"S\""
#guard stable "russian" "сила S, p)"
-- r201: russian 'сила(S p)'
#guard run "russian" "сила(S p)" == "ERR expected Crux.Token.Comma, got Crux.Token.Ident \"p\""
#guard pub "russian" "сила(S p)" == "ERR expected Crux.Token.Comma, got Crux.Token.Ident \"p\""
#guard runAt "russian" "сила(S p)" (budget "сила(S p)" / 8) == "ERR expected Crux.Token.Comma, got Crux.Token.Ident \"p\""
#guard stable "russian" "сила(S p)"
-- r202: russian 'омега(kani, S, p)'
#guard run "russian" "омега(kani, S, p)" == "OK 8 Crux.RussianForm.Omega (Crux.Backend.Kani { name := \"placeholder\", params := [], return_sort := Crux.Sort.Bool, body := [] }) (Crux.State.S) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "russian" "омега(kani, S, p)" == "OK Crux.RussianForm.Omega (Crux.Backend.Kani { name := \"placeholder\", params := [], return_sort := Crux.Sort.Bool, body := [] }) (Crux.State.S) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "russian" "омега(kani, S, p)" (budget "омега(kani, S, p)" / 8) == "OK 8 Crux.RussianForm.Omega (Crux.Backend.Kani { name := \"placeholder\", params := [], return_sort := Crux.Sort.Bool, body := [] }) (Crux.State.S) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard stable "russian" "омега(kani, S, p)"
-- r203: russian 'омега(anything, S1, ∀ x : Nat . x = x)'
#guard run "russian" "омега(anything, S1, ∀ x : Nat . x = x)" == "OK 15 Crux.RussianForm.Omega (Crux.Backend.Kani { name := \"placeholder\", params := [], return_sort := Crux.Sort.Bool, body := [] }) (Crux.State.Sn 1) (Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"x\")))"
#guard pub "russian" "омега(anything, S1, ∀ x : Nat . x = x)" == "OK Crux.RussianForm.Omega (Crux.Backend.Kani { name := \"placeholder\", params := [], return_sort := Crux.Sort.Bool, body := [] }) (Crux.State.Sn 1) (Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"x\")))"
#guard runAt "russian" "омега(anything, S1, ∀ x : Nat . x = x)" (budget "омега(anything, S1, ∀ x : Nat . x = x)" / 8) == "OK 15 Crux.RussianForm.Omega (Crux.Backend.Kani { name := \"placeholder\", params := [], return_sort := Crux.Sort.Bool, body := [] }) (Crux.State.Sn 1) (Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Eq (Crux.Term.Var \"x\") (Crux.Term.Var \"x\")))"
#guard stable "russian" "омега(anything, S1, ∀ x : Nat . x = x)"
-- r204: russian 'омега((, S, p)'
#guard run "russian" "омега((, S, p)" == "OK 8 Crux.RussianForm.Omega (Crux.Backend.Kani { name := \"placeholder\", params := [], return_sort := Crux.Sort.Bool, body := [] }) (Crux.State.S) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard pub "russian" "омега((, S, p)" == "OK Crux.RussianForm.Omega (Crux.Backend.Kani { name := \"placeholder\", params := [], return_sort := Crux.Sort.Bool, body := [] }) (Crux.State.S) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard runAt "russian" "омега((, S, p)" (budget "омега((, S, p)" / 8) == "OK 8 Crux.RussianForm.Omega (Crux.Backend.Kani { name := \"placeholder\", params := [], return_sort := Crux.Sort.Bool, body := [] }) (Crux.State.S) (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" []))"
#guard stable "russian" "омега((, S, p)"
-- r205: russian 'омега(k S, p)'
#guard run "russian" "омега(k S, p)" == "ERR expected Crux.Token.Comma, got Crux.Token.Ident \"S\""
#guard pub "russian" "омега(k S, p)" == "ERR expected Crux.Token.Comma, got Crux.Token.Ident \"S\""
#guard runAt "russian" "омега(k S, p)" (budget "омега(k S, p)" / 8) == "ERR expected Crux.Token.Comma, got Crux.Token.Ident \"S\""
#guard stable "russian" "омега(k S, p)"
-- r206: russian 'омега(k, 5, p)'
#guard run "russian" "омега(k, 5, p)" == "ERR unexpected token in state: Crux.Token.Number 5"
#guard pub "russian" "омега(k, 5, p)" == "ERR unexpected token in state: Crux.Token.Number 5"
#guard runAt "russian" "омега(k, 5, p)" (budget "омега(k, 5, p)" / 8) == "ERR unexpected token in state: Crux.Token.Number 5"
#guard stable "russian" "омега(k, 5, p)"
-- r207: russian 'доказательство'
#guard run "russian" "доказательство" == "OK 1 Crux.RussianForm.Dokazatelstvo { obligations := [] }"
#guard pub "russian" "доказательство" == "OK Crux.RussianForm.Dokazatelstvo { obligations := [] }"
#guard runAt "russian" "доказательство" (budget "доказательство" / 8) == "OK 1 Crux.RussianForm.Dokazatelstvo { obligations := [] }"
#guard stable "russian" "доказательство"
-- r208: russian 'доказательство(junk)'
#guard run "russian" "доказательство(junk)" == "OK 1 Crux.RussianForm.Dokazatelstvo { obligations := [] }"
#guard pub "russian" "доказательство(junk)" == "OK Crux.RussianForm.Dokazatelstvo { obligations := [] }"
#guard runAt "russian" "доказательство(junk)" (budget "доказательство(junk)" / 8) == "OK 1 Crux.RussianForm.Dokazatelstvo { obligations := [] }"
#guard stable "russian" "доказательство(junk)"
-- r209: russian 'импликация'
#guard run "russian" "импликация" == "ERR unexpected Russian form: Crux.Token.Imply"
#guard pub "russian" "импликация" == "ERR unexpected Russian form: Crux.Token.Imply"
#guard runAt "russian" "импликация" (budget "импликация" / 8) == "ERR unexpected Russian form: Crux.Token.Imply"
#guard stable "russian" "импликация"
-- r210: russian 'конъюнкция'
#guard run "russian" "конъюнкция" == "ERR unexpected Russian form: Crux.Token.Conj"
#guard pub "russian" "конъюнкция" == "ERR unexpected Russian form: Crux.Token.Conj"
#guard runAt "russian" "конъюнкция" (budget "конъюнкция" / 8) == "ERR unexpected Russian form: Crux.Token.Conj"
#guard stable "russian" "конъюнкция"
-- r211: russian 'дизъюнкция'
#guard run "russian" "дизъюнкция" == "ERR unexpected Russian form: Crux.Token.Disj"
#guard pub "russian" "дизъюнкция" == "ERR unexpected Russian form: Crux.Token.Disj"
#guard runAt "russian" "дизъюнкция" (budget "дизъюнкция" / 8) == "ERR unexpected Russian form: Crux.Token.Disj"
#guard stable "russian" "дизъюнкция"
-- r212: russian 'отрицание'
#guard run "russian" "отрицание" == "ERR unexpected Russian form: Crux.Token.Neg"
#guard pub "russian" "отрицание" == "ERR unexpected Russian form: Crux.Token.Neg"
#guard runAt "russian" "отрицание" (budget "отрицание" / 8) == "ERR unexpected Russian form: Crux.Token.Neg"
#guard stable "russian" "отрицание"
-- r213: russian 'существует'
#guard run "russian" "существует" == "ERR unexpected Russian form: Crux.Token.Sushchestvuet"
#guard pub "russian" "существует" == "ERR unexpected Russian form: Crux.Token.Sushchestvuet"
#guard runAt "russian" "существует" (budget "существует" / 8) == "ERR unexpected Russian form: Crux.Token.Sushchestvuet"
#guard stable "russian" "существует"
-- r214: russian 'рекурсия'
#guard run "russian" "рекурсия" == "ERR unexpected Russian form: Crux.Token.Rekursiya"
#guard pub "russian" "рекурсия" == "ERR unexpected Russian form: Crux.Token.Rekursiya"
#guard runAt "russian" "рекурсия" (budget "рекурсия" / 8) == "ERR unexpected Russian form: Crux.Token.Rekursiya"
#guard stable "russian" "рекурсия"
-- r215: russian 'состояние'
#guard run "russian" "состояние" == "ERR unexpected Russian form: Crux.Token.Sostoyanie"
#guard pub "russian" "состояние" == "ERR unexpected Russian form: Crux.Token.Sostoyanie"
#guard runAt "russian" "состояние" (budget "состояние" / 8) == "ERR unexpected Russian form: Crux.Token.Sostoyanie"
#guard stable "russian" "состояние"
-- r216: russian 'омега'
#guard run "russian" "омега" == "ERR expected Crux.Token.LParen, got Crux.Token.Eof"
#guard pub "russian" "омега" == "ERR expected Crux.Token.LParen, got Crux.Token.Eof"
#guard runAt "russian" "омега" (budget "омега" / 8) == "ERR expected Crux.Token.LParen, got Crux.Token.Eof"
#guard stable "russian" "омега"
-- r217: russian 'сила'
#guard run "russian" "сила" == "ERR expected Crux.Token.LParen, got Crux.Token.Eof"
#guard pub "russian" "сила" == "ERR expected Crux.Token.LParen, got Crux.Token.Eof"
#guard runAt "russian" "сила" (budget "сила" / 8) == "ERR expected Crux.Token.LParen, got Crux.Token.Eof"
#guard stable "russian" "сила"
-- r218: russian ''
#guard run "russian" "" == "ERR unexpected Russian form: Crux.Token.Eof"
#guard pub "russian" "" == "ERR unexpected Russian form: Crux.Token.Eof"
#guard runAt "russian" "" (budget "" / 8) == "ERR unexpected Russian form: Crux.Token.Eof"
#guard stable "russian" ""
-- r219: russian 'x'
#guard run "russian" "x" == "ERR unexpected Russian form: Crux.Token.Ident \"x\""
#guard pub "russian" "x" == "ERR unexpected Russian form: Crux.Token.Ident \"x\""
#guard runAt "russian" "x" (budget "x" / 8) == "ERR unexpected Russian form: Crux.Token.Ident \"x\""
#guard stable "russian" "x"
-- r220: russian 'p ∧ q'
#guard run "russian" "p ∧ q" == "ERR unexpected Russian form: Crux.Token.Ident \"p\""
#guard pub "russian" "p ∧ q" == "ERR unexpected Russian form: Crux.Token.Ident \"p\""
#guard runAt "russian" "p ∧ q" (budget "p ∧ q" / 8) == "ERR unexpected Russian form: Crux.Token.Ident \"p\""
#guard stable "russian" "p ∧ q"
-- r221: russian 'равенство(x, y'
#guard run "russian" "равенство(x, y" == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard pub "russian" "равенство(x, y" == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard runAt "russian" "равенство(x, y" (budget "равенство(x, y" / 8) == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard stable "russian" "равенство(x, y"
-- r222: russian 'равенство(x)'
#guard run "russian" "равенство(x)" == "ERR expected Crux.Token.Comma, got Crux.Token.RParen"
#guard pub "russian" "равенство(x)" == "ERR expected Crux.Token.Comma, got Crux.Token.RParen"
#guard runAt "russian" "равенство(x)" (budget "равенство(x)" / 8) == "ERR expected Crux.Token.Comma, got Crux.Token.RParen"
#guard stable "russian" "равенство(x)"
-- r223: russian 'равенство x'
#guard run "russian" "равенство x" == "ERR expected Crux.Token.LParen, got Crux.Token.Ident \"x\""
#guard pub "russian" "равенство x" == "ERR expected Crux.Token.LParen, got Crux.Token.Ident \"x\""
#guard runAt "russian" "равенство x" (budget "равенство x" / 8) == "ERR expected Crux.Token.LParen, got Crux.Token.Ident \"x\""
#guard stable "russian" "равенство x"
-- r224: russian 'сила(S, ∀ x : Nat . x < y → y > x)'
#guard run "russian" "сила(S, ∀ x : Nat . x < y → y > x)" == "OK 17 Crux.RussianForm.Sila (Crux.State.S) (Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"<\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])) (Crux.Formula.Atomic (Crux.Atomic.Predicate \">\" [Crux.Term.Var \"y\", Crux.Term.Var \"x\"]))))"
#guard pub "russian" "сила(S, ∀ x : Nat . x < y → y > x)" == "OK Crux.RussianForm.Sila (Crux.State.S) (Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"<\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])) (Crux.Formula.Atomic (Crux.Atomic.Predicate \">\" [Crux.Term.Var \"y\", Crux.Term.Var \"x\"]))))"
#guard runAt "russian" "сила(S, ∀ x : Nat . x < y → y > x)" (budget "сила(S, ∀ x : Nat . x < y → y > x)" / 8) == "OK 17 Crux.RussianForm.Sila (Crux.State.S) (Crux.Formula.Forall \"x\" (Crux.Sort.Nat) (Crux.Formula.Implies (Crux.Formula.Atomic (Crux.Atomic.Predicate \"<\" [Crux.Term.Var \"x\", Crux.Term.Var \"y\"])) (Crux.Formula.Atomic (Crux.Atomic.Predicate \">\" [Crux.Term.Var \"y\", Crux.Term.Var \"x\"]))))"
#guard stable "russian" "сила(S, ∀ x : Nat . x < y → y > x)"
-- r225: russian 'омега(z3, S0, ¬p)'
#guard run "russian" "омега(z3, S0, ¬p)" == "OK 9 Crux.RussianForm.Omega (Crux.Backend.Kani { name := \"placeholder\", params := [], return_sort := Crux.Sort.Bool, body := [] }) (Crux.State.S0) (Crux.Formula.Not (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])))"
#guard pub "russian" "омега(z3, S0, ¬p)" == "OK Crux.RussianForm.Omega (Crux.Backend.Kani { name := \"placeholder\", params := [], return_sort := Crux.Sort.Bool, body := [] }) (Crux.State.S0) (Crux.Formula.Not (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])))"
#guard runAt "russian" "омега(z3, S0, ¬p)" (budget "омега(z3, S0, ¬p)" / 8) == "OK 9 Crux.RussianForm.Omega (Crux.Backend.Kani { name := \"placeholder\", params := [], return_sort := Crux.Sort.Bool, body := [] }) (Crux.State.S0) (Crux.Formula.Not (Crux.Formula.Atomic (Crux.Atomic.Predicate \"p\" [])))"
#guard stable "russian" "омега(z3, S0, ¬p)"
-- s226: sort 'Nat'
#guard run "sort" "Nat" == "OK 1 Crux.Sort.Nat"
#guard runAt "sort" "Nat" (budget "Nat" / 8) == "OK 1 Crux.Sort.Nat"
#guard stable "sort" "Nat"
-- s227: sort 'Nat → Int'
#guard run "sort" "Nat → Int" == "OK 3 Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Int)"
#guard runAt "sort" "Nat → Int" (budget "Nat → Int" / 8) == "OK 3 Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Int)"
#guard stable "sort" "Nat → Int"
-- s228: sort 'Nat -> Int'
#guard run "sort" "Nat -> Int" == "OK 3 Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Int)"
#guard runAt "sort" "Nat -> Int" (budget "Nat -> Int" / 8) == "OK 3 Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Int)"
#guard stable "sort" "Nat -> Int"
-- s229: sort 'Nat → Int → Bool'
#guard run "sort" "Nat → Int → Bool" == "OK 5 Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Arrow (Crux.Sort.Int) (Crux.Sort.Bool))"
#guard runAt "sort" "Nat → Int → Bool" (budget "Nat → Int → Bool" / 8) == "OK 5 Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Arrow (Crux.Sort.Int) (Crux.Sort.Bool))"
#guard stable "sort" "Nat → Int → Bool"
-- s230: sort '(Nat → Int) → Bool'
#guard run "sort" "(Nat → Int) → Bool" == "OK 7 Crux.Sort.Arrow (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Int)) (Crux.Sort.Bool)"
#guard runAt "sort" "(Nat → Int) → Bool" (budget "(Nat → Int) → Bool" / 8) == "OK 7 Crux.Sort.Arrow (Crux.Sort.Arrow (Crux.Sort.Nat) (Crux.Sort.Int)) (Crux.Sort.Bool)"
#guard stable "sort" "(Nat → Int) → Bool"
-- s231: sort '((Nat))'
#guard run "sort" "((Nat))" == "OK 5 Crux.Sort.Nat"
#guard runAt "sort" "((Nat))" (budget "((Nat))" / 8) == "OK 5 Crux.Sort.Nat"
#guard stable "sort" "((Nat))"
-- s232: sort 'Foo'
#guard run "sort" "Foo" == "OK 1 Crux.Sort.User \"Foo\""
#guard runAt "sort" "Foo" (budget "Foo" / 8) == "OK 1 Crux.Sort.User \"Foo\""
#guard stable "sort" "Foo"
-- s233: sort 'Prop → Type'
#guard run "sort" "Prop → Type" == "OK 3 Crux.Sort.Arrow (Crux.Sort.Prop) (Crux.Sort.Type)"
#guard runAt "sort" "Prop → Type" (budget "Prop → Type" / 8) == "OK 3 Crux.Sort.Arrow (Crux.Sort.Prop) (Crux.Sort.Type)"
#guard stable "sort" "Prop → Type"
-- s234: sort '(Nat'
#guard run "sort" "(Nat" == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard runAt "sort" "(Nat" (budget "(Nat" / 8) == "ERR expected Crux.Token.RParen, got Crux.Token.Eof"
#guard stable "sort" "(Nat"
-- s235: sort '→'
#guard run "sort" "→" == "ERR unexpected token in sort: Crux.Token.Arrow"
#guard runAt "sort" "→" (budget "→" / 8) == "ERR unexpected token in sort: Crux.Token.Arrow"
#guard stable "sort" "→"
-- s236: sort ''
#guard run "sort" "" == "ERR unexpected token in sort: Crux.Token.Eof"
#guard runAt "sort" "" (budget "" / 8) == "ERR unexpected token in sort: Crux.Token.Eof"
#guard stable "sort" ""
-- s237: sort 'Nat →'
#guard run "sort" "Nat →" == "ERR unexpected token in sort: Crux.Token.Eof"
#guard runAt "sort" "Nat →" (budget "Nat →" / 8) == "ERR unexpected token in sort: Crux.Token.Eof"
#guard stable "sort" "Nat →"
-- s238: sort '( )'
#guard run "sort" "( )" == "ERR unexpected token in sort: Crux.Token.RParen"
#guard runAt "sort" "( )" (budget "( )" / 8) == "ERR unexpected token in sort: Crux.Token.RParen"
#guard stable "sort" "( )"
-- s239: sort 'Nat Int'
#guard run "sort" "Nat Int" == "OK 1 Crux.Sort.Nat"
#guard runAt "sort" "Nat Int" (budget "Nat Int" / 8) == "OK 1 Crux.Sort.Nat"
#guard stable "sort" "Nat Int"
-- f240: formula '((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((...'
#guard digest (run "formula" "((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))") == "4257:9352913115528028252"
#guard stable "formula" "((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((p))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))"
-- t241: term '((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((...'
#guard digest (run "term" "((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((x))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))") == "3624:4764550204769543144"
#guard stable "term" "((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((x))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))"
-- f242: formula '¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬...'
#guard digest (run "formula" "¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬p") == "5757:12464113598090514586"
#guard stable "formula" "¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬p"
-- f243: formula 'p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ ...'
#guard digest (run "formula" "p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p") == "21286:4595866238819132215"
#guard stable "formula" "p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p ∧ p"
-- f244: formula 'p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ ...'
#guard digest (run "formula" "p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p") == "14186:2385420770726383194"
#guard stable "formula" "p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p ∨ p"
-- f245: formula 'p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → ...'
#guard digest (run "formula" "p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p") == "15181:7534167514755986066"
#guard stable "formula" "p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p → p"
-- t246: term 'a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + ...'
#guard digest (run "term" "a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a") == "16469:5285067386262235437"
#guard stable "term" "a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a + a"
-- t247: term 'a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * ...'
#guard digest (run "term" "a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a + b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b") == "16469:15347677275092679053"
#guard stable "term" "a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a * a + b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b - b"
-- t248: term 'f x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 ...'
#guard digest (run "term" "f x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 x79 x80 x81 x82 x83 x84 x85 x86 x87 x88 x89 x90 x91 x92 x93 x94 x95 x96 x97 x98 x99 x100 x101 x102 x103 x104 x105 x106 x107 x108 x109 x110 x111 x112 x113 x114 x115 x116 x117 x118 x119 x120 x121 x122 x123 x124 x125 x126 x127 x128 x129 x130 x131 x132 x133 x134 x135 x136 x137 x138 x139 x140 x141 x142 x143 x144 x145 x146 x147 x148 x149 x150 x151 x152 x153 x154 x155 x156 x157 x158 x159 x160 x161 x162 x163 x164 x165 x166 x167 x168 x169 x170 x171 x172 x173 x174 x175 x176 x177 x178 x179 x180 x181 x182 x183 x184 x185 x186 x187 x188 x189 x190 x191 x192 x193 x194 x195 x196 x197 x198 x199 x200 x201 x202 x203 x204 x205 x206 x207 x208 x209 x210 x211 x212 x213 x214 x215 x216 x217 x218 x219 x220 x221 x222 x223 x224 x225 x226 x227 x228 x229 x230 x231 x232 x233 x234 x235 x236 x237 x238 x239 x240 x241 x242 x243 x244 x245 x246 x247 x248 x249 x250 x251 x252 x253 x254 x255 x256 x257 x258 x259 x260 x261 x262 x263 x264 x265 x266 x267 x268 x269 x270 x271 x272 x273 x274 x275 x276 x277 x278 x279 x280 x281 x282 x283 x284 x285 x286 x287 x288 x289 x290 x291 x292 x293 x294 x295 x296 x297 x298 x299") == "11614:666356486876377525"
#guard stable "term" "f x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 x79 x80 x81 x82 x83 x84 x85 x86 x87 x88 x89 x90 x91 x92 x93 x94 x95 x96 x97 x98 x99 x100 x101 x102 x103 x104 x105 x106 x107 x108 x109 x110 x111 x112 x113 x114 x115 x116 x117 x118 x119 x120 x121 x122 x123 x124 x125 x126 x127 x128 x129 x130 x131 x132 x133 x134 x135 x136 x137 x138 x139 x140 x141 x142 x143 x144 x145 x146 x147 x148 x149 x150 x151 x152 x153 x154 x155 x156 x157 x158 x159 x160 x161 x162 x163 x164 x165 x166 x167 x168 x169 x170 x171 x172 x173 x174 x175 x176 x177 x178 x179 x180 x181 x182 x183 x184 x185 x186 x187 x188 x189 x190 x191 x192 x193 x194 x195 x196 x197 x198 x199 x200 x201 x202 x203 x204 x205 x206 x207 x208 x209 x210 x211 x212 x213 x214 x215 x216 x217 x218 x219 x220 x221 x222 x223 x224 x225 x226 x227 x228 x229 x230 x231 x232 x233 x234 x235 x236 x237 x238 x239 x240 x241 x242 x243 x244 x245 x246 x247 x248 x249 x250 x251 x252 x253 x254 x255 x256 x257 x258 x259 x260 x261 x262 x263 x264 x265 x266 x267 x268 x269 x270 x271 x272 x273 x274 x275 x276 x277 x278 x279 x280 x281 x282 x283 x284 x285 x286 x287 x288 x289 x290 x291 x292 x293 x294 x295 x296 x297 x298 x299"
-- f249: formula '∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ...'
#guard digest (run "formula" "∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . p") == "4257:9672025310215486266"
#guard stable "formula" "∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . ∀ x : Nat . p"
-- f250: formula '∀ x : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → ...'
#guard digest (run "formula" "∀ x : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat . p") == "6899:15917961712728890562"
#guard stable "formula" "∀ x : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat . p"
-- t251: term '(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13,...'
#guard digest (run "term" "(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, t63, t64, t65, t66, t67, t68, t69, t70, t71, t72, t73, t74, t75, t76, t77, t78, t79, t80, t81, t82, t83, t84, t85, t86, t87, t88, t89, t90, t91, t92, t93, t94, t95, t96, t97, t98, t99, t100, t101, t102, t103, t104, t105, t106, t107, t108, t109, t110, t111, t112, t113, t114, t115, t116, t117, t118, t119, t120, t121, t122, t123, t124, t125, t126, t127, t128, t129, t130, t131, t132, t133, t134, t135, t136, t137, t138, t139, t140, t141, t142, t143, t144, t145, t146, t147, t148, t149, t150, t151, t152, t153, t154, t155, t156, t157, t158, t159, t160, t161, t162, t163, t164, t165, t166, t167, t168, t169, t170, t171, t172, t173, t174, t175, t176, t177, t178, t179, t180, t181, t182, t183, t184, t185, t186, t187, t188, t189, t190, t191, t192, t193, t194, t195, t196, t197, t198, t199, t200, t201, t202, t203, t204, t205, t206, t207, t208, t209, t210, t211, t212, t213, t214, t215, t216, t217, t218, t219, t220, t221, t222, t223, t224, t225, t226, t227, t228, t229, t230, t231, t232, t233, t234, t235, t236, t237, t238, t239, t240, t241, t242, t243, t244, t245, t246, t247, t248, t249, t250, t251, t252, t253, t254, t255, t256, t257, t258, t259, t260, t261, t262, t263, t264, t265, t266, t267, t268, t269, t270, t271, t272, t273, t274, t275, t276, t277, t278, t279, t280, t281, t282, t283, t284, t285, t286, t287, t288, t289, t290, t291, t292, t293, t294, t295, t296, t297, t298, t299)") == "6513:6449281359387679867"
#guard stable "term" "(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, t63, t64, t65, t66, t67, t68, t69, t70, t71, t72, t73, t74, t75, t76, t77, t78, t79, t80, t81, t82, t83, t84, t85, t86, t87, t88, t89, t90, t91, t92, t93, t94, t95, t96, t97, t98, t99, t100, t101, t102, t103, t104, t105, t106, t107, t108, t109, t110, t111, t112, t113, t114, t115, t116, t117, t118, t119, t120, t121, t122, t123, t124, t125, t126, t127, t128, t129, t130, t131, t132, t133, t134, t135, t136, t137, t138, t139, t140, t141, t142, t143, t144, t145, t146, t147, t148, t149, t150, t151, t152, t153, t154, t155, t156, t157, t158, t159, t160, t161, t162, t163, t164, t165, t166, t167, t168, t169, t170, t171, t172, t173, t174, t175, t176, t177, t178, t179, t180, t181, t182, t183, t184, t185, t186, t187, t188, t189, t190, t191, t192, t193, t194, t195, t196, t197, t198, t199, t200, t201, t202, t203, t204, t205, t206, t207, t208, t209, t210, t211, t212, t213, t214, t215, t216, t217, t218, t219, t220, t221, t222, t223, t224, t225, t226, t227, t228, t229, t230, t231, t232, t233, t234, t235, t236, t237, t238, t239, t240, t241, t242, t243, t244, t245, t246, t247, t248, t249, t250, t251, t252, t253, t254, t255, t256, t257, t258, t259, t260, t261, t262, t263, t264, t265, t266, t267, t268, t269, t270, t271, t272, t273, t274, t275, t276, t277, t278, t279, t280, t281, t282, t283, t284, t285, t286, t287, t288, t289, t290, t291, t292, t293, t294, t295, t296, t297, t298, t299)"
-- f252: formula 'if if if if if if if if if if if if if if if if if if if if ...'
#guard digest (run "formula" "if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if p then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d") == "4097:1994252925451086145"
#guard stable "formula" "if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if if p then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d then a else b = d"
-- t253: term 'if p then if p then if p then if p then if p then if p then ...'
#guard digest (run "term" "if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then x else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y") == "5784:3853363747527761041"
#guard stable "term" "if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then if p then x else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y else y"
-- t254: term 'fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => ...'
#guard digest (run "term" "fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => x") == "2364:1607309059244046036"
#guard stable "term" "fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => fun v : Nat => x"
-- f255: formula '((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((...'
#guard digest (run "formula" "((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((p") == "50:3598972548294236168"
#guard stable "formula" "((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((p"
-- f256: formula '¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬...'
#guard digest (run "formula" "¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬") == "44:5858997119033133391"
#guard stable "formula" "¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬¬"
-- r257: russian 'сила(S, ((((((((((((((((((((((((((((((((((((((((((((((((((((...'
#guard digest (run "russian" "сила(S, ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))") == "3246:6746924957308888997"
#guard stable "russian" "сила(S, ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((p)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))"

-- Fuel 0 is a defined failure for every entry point.
#guard runAt "term" "x" 0 == "ERR recursion limit reached in parse_term"
#guard runAt "formula" "p" 0 == "ERR recursion limit reached in parse_formula"
#guard runAt "sort" "Nat" 0 == "ERR recursion limit reached in parse_sort"
#guard runAt "russian" "доказательство" 0 == "ERR recursion limit reached in parse_russian_form"

end RussianCheckedTests
end Crux
