-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab
--
-- Checked copy of Crux/Russian.lean. The original file is unchanged.
-- Every edit below is marked with a `-- Changed:` comment. Summary:
--  * The sort, term and formula parsers form ONE `mutual` block. The
--    original passed the mutual function `parseFormula` into `parseTerm` as
--    a higher-order argument (`parseTerm parseFormula tokens pos fuel`).
--    Inside the formula block's well-founded recursion that hides the fuel
--    of every call made through the argument, so the termination checker
--    is left with goals `a✝ < fuel.succ` about an arbitrary `a✝`, which no
--    proof can close. Term atoms now call `parseFormula` directly; the
--    higher-order parameter is gone. The original's only instantiation of
--    it was `parseFormula`, so every call computes what it computed.
--  * Termination is structural recursion on the shared fuel `Nat`
--    (`termination_by structural fuel => fuel`): every recursive call is on
--    the predecessor `fuel` of a `fuel + 1` pattern. No well-founded
--    recursion, no `decreasing_by`, no `partial`.
--  * Token dispatch inside the recursive parsers goes through small
--    non-recursive classifier functions (`sortHead`, `termHead`,
--    `fAtomHead`, ...) that reproduce the original `match` arms in order.
--  * `set_option maxHeartbeats 10000000` is no longer global. The same
--    original value is scoped to the `Token` declaration, whose derived
--    `DecidableEq` for 71 constructors needs it; every parser definition is
--    checked under Lean's default limit.
/-
Russian-form parser (fsl/src/crux/russian.rs).
Lexer and recursive-descent parser as pure functions: the lexer threads
(input : List Char) and pos explicitly, the parser threads tokens and
pos and returns Except String (value × newPos). Recursion is bounded by
an explicit fuel argument (tokens.length * 8 + 16 for the public entry
points); the source's recursion is unbounded.

Russian keyword strings use correct Cyrillic, decoded from the mojibake
in the pasted Rust: равенство, импликация, конъюнкция, дизъюнкция,
отрицание, для всех, существует, рекурсия, состояние, сила, омега,
доказательство. Unicode characters in the lexer are the real characters:
→ ↔ ∀ ∃ ∧ ∨ ¬ ≡ ≤ ≥ ≠ ⊢ ⊨ ⊤ ⊥ ↦.

Ported exactly as written in the source:
- the Omega arm of parse_russian_form carries the placeholder backend
  (KaniMIR named "placeholder");
- parse_formula_or builds Formula::And for an Or (as written);
- the keyword "для всех" contains a space, so it can never match a
  single identifier (as written).
-/

import Crux.Ast

namespace Crux

-- Changed: the original's global `set_option maxHeartbeats 10000000` is
-- scoped to this declaration only (same value; the derived DecidableEq
-- instance of this 71-constructor type needs more than the default).
set_option maxHeartbeats 10000000 in
inductive Token where
  | Ravno | Imply | Conj | Disj | Neg | DlyaVsekh | Sushchestvuet | Rekursiya
  | Sostoyanie | Sila | Omega | Dokazatelstvo
  | Let | In | If | Then | Else | Match | With | Fold | Rec | Fun
  | Theorem | Lemma | Example | Proof | QED | By | Sorry
  | LParen | RParen | LBracket | RBracket | LBrace | RBrace
  | Comma | Semicolon | Dot | Colon | Pipe | Arrow | DoubleArrow | FatArrow
  | Eq | Ne | Lt | Le | Gt | Ge | Plus | Minus | Star | Slash | Percent
  | Cons | Concat | And | Or | Not | Implies | Iff | Forall | Exists | Mu | Nu
  | Ident (name : String)
  | Number (n : Int)
  | BoolLit (b : Bool)
  | StringLit (s : String)
  | Eof
deriving DecidableEq, Repr

def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' ||
  (0x0370 ≤ c.toNat && c.toNat ≤ 0x03FF) ||
  (0x0400 ≤ c.toNat && c.toNat ≤ 0x04FF)

def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_' ||
  (0x0370 ≤ c.toNat && c.toNat ≤ 0x03FF) ||
  (0x0400 ≤ c.toNat && c.toNat ≤ 0x04FF)

def readIdent (input : List Char) (pos : Nat) : String × Nat :=
  let chars := (input.drop pos).takeWhile isIdentChar
  (chars.asString, pos + chars.length)

def readNumber (input : List Char) (pos : Nat) : Int × Nat :=
  let chars := (input.drop pos).takeWhile (·.isDigit)
  let n := chars.asString.toNat?.getD 0
  ((n : Int), pos + chars.length)

def readStringLit (input : List Char) (pos : Nat) : String × Nat :=
  let rest := input.drop pos
  let chars := rest.takeWhile (· != '"')
  let closed := (rest.drop chars.length).head? == some '"'
  (chars.asString, pos + chars.length + if closed then 1 else 0)

def skipLine (input : List Char) (pos : Nat) : Nat :=
  let rest := input.drop pos
  let taken := rest.takeWhile (· != '\n')
  pos + taken.length + (if (rest.drop taken.length).head? == some '\n' then 1 else 0)

def skipWsComments (input : List Char) (pos : Nat) : Nat → Nat
  | 0 => pos
  | fuel + 1 =>
    match input.get? pos with
    | none => pos
    | some c =>
      if c.isWhitespace then skipWsComments input (pos + 1) fuel
      else if c == '-' && input.get? (pos + 1) == some '-' then
        skipWsComments input (skipLine input (pos + 2)) fuel
      else pos

def keywordToken (id : String) : Token :=
  match id with
  | "равенство" => .Ravno
  | "импликация" => .Imply
  | "конъюнкция" => .Conj
  | "дизъюнкция" => .Disj
  | "отрицание" => .Neg
  | "для всех" => .DlyaVsekh
  | "существует" => .Sushchestvuet
  | "рекурсия" => .Rekursiya
  | "состояние" => .Sostoyanie
  | "сила" => .Sila
  | "омега" => .Omega
  | "доказательство" => .Dokazatelstvo
  | "let" => .Let
  | "in" => .In
  | "if" => .If
  | "then" => .Then
  | "else" => .Else
  | "match" => .Match
  | "with" => .With
  | "fold" => .Fold
  | "rec" => .Rec
  | "fun" => .Fun
  | "theorem" => .Theorem
  | "lemma" => .Lemma
  | "example" => .Example
  | "proof" => .Proof
  | "qed" => .QED
  | "by" => .By
  | "sorry" => .Sorry
  | "true" => .BoolLit true
  | "false" => .BoolLit false
  | "forall" => .Forall
  | "exists" => .Exists
  | "mu" => .Mu
  | "nu" => .Nu
  | _ => .Ident id

def tokenizeAux (input : List Char) (pos : Nat) : Nat → List Token
  | 0 => [Token.Eof]
  | fuel + 1 =>
    let pos := skipWsComments input pos fuel
    match input.get? pos with
    | none => [Token.Eof]
    | some c =>
      match c with
      | '(' => .LParen :: tokenizeAux input (pos + 1) fuel
      | ')' => .RParen :: tokenizeAux input (pos + 1) fuel
      | '[' => .LBracket :: tokenizeAux input (pos + 1) fuel
      | ']' => .RBracket :: tokenizeAux input (pos + 1) fuel
      | '{' => .LBrace :: tokenizeAux input (pos + 1) fuel
      | '}' => .RBrace :: tokenizeAux input (pos + 1) fuel
      | ',' => .Comma :: tokenizeAux input (pos + 1) fuel
      | ';' => .Semicolon :: tokenizeAux input (pos + 1) fuel
      | '.' => .Dot :: tokenizeAux input (pos + 1) fuel
      | ':' => .Colon :: tokenizeAux input (pos + 1) fuel
      | '|' => .Pipe :: tokenizeAux input (pos + 1) fuel
      | '+' => .Plus :: tokenizeAux input (pos + 1) fuel
      | '%' => .Percent :: tokenizeAux input (pos + 1) fuel
      | '*' => .Star :: tokenizeAux input (pos + 1) fuel
      | '/' => .Slash :: tokenizeAux input (pos + 1) fuel
      | '=' =>
        match input.get? (pos + 1) with
        | some '=' => .Eq :: tokenizeAux input (pos + 2) fuel
        | some '>' => .FatArrow :: tokenizeAux input (pos + 2) fuel
        | _ => .Eq :: tokenizeAux input (pos + 1) fuel
      | '!' =>
        if input.get? (pos + 1) == some '=' then
          .Ne :: tokenizeAux input (pos + 2) fuel
        else
          .Not :: tokenizeAux input (pos + 1) fuel
      | '<' =>
        match input.get? (pos + 1) with
        | some '=' => .Le :: tokenizeAux input (pos + 2) fuel
        | some '-' => .Cons :: tokenizeAux input (pos + 2) fuel
        | _ => .Lt :: tokenizeAux input (pos + 1) fuel
      | '>' =>
        if input.get? (pos + 1) == some '=' then
          .Ge :: tokenizeAux input (pos + 2) fuel
        else
          .Gt :: tokenizeAux input (pos + 1) fuel
      | '-' =>
        match input.get? (pos + 1) with
        | some '>' => .Arrow :: tokenizeAux input (pos + 2) fuel
        | some '-' => .Minus :: tokenizeAux input (pos + 2) fuel
        | _ => .Minus :: tokenizeAux input (pos + 1) fuel
      | '→' => .Arrow :: tokenizeAux input (pos + 1) fuel
      | '↔' => .DoubleArrow :: tokenizeAux input (pos + 1) fuel
      | '∀' => .Forall :: tokenizeAux input (pos + 1) fuel
      | '∃' => .Exists :: tokenizeAux input (pos + 1) fuel
      | '∧' => .And :: tokenizeAux input (pos + 1) fuel
      | '∨' => .Or :: tokenizeAux input (pos + 1) fuel
      | '¬' => .Not :: tokenizeAux input (pos + 1) fuel
      | '≡' => .Eq :: tokenizeAux input (pos + 1) fuel
      | '≤' => .Le :: tokenizeAux input (pos + 1) fuel
      | '≥' => .Ge :: tokenizeAux input (pos + 1) fuel
      | '≠' => .Ne :: tokenizeAux input (pos + 1) fuel
      | '⊢' => .Not :: tokenizeAux input (pos + 1) fuel
      | '⊨' => .Not :: tokenizeAux input (pos + 1) fuel
      | '⊤' => .BoolLit true :: tokenizeAux input (pos + 1) fuel
      | '⊥' => .BoolLit false :: tokenizeAux input (pos + 1) fuel
      | '↦' => .FatArrow :: tokenizeAux input (pos + 1) fuel
      | '"' =>
        let (s, pos') := readStringLit input (pos + 1)
        .StringLit s :: tokenizeAux input pos' fuel
      | _ =>
        if c.isDigit then
          let (n, pos') := readNumber input pos
          .Number n :: tokenizeAux input pos' fuel
        else if isIdentStart c then
          let (id, pos') := readIdent input pos
          keywordToken id :: tokenizeAux input pos' fuel
        else
          tokenizeAux input (pos + 1) fuel

def tokenize (input : String) : List Token :=
  tokenizeAux input.toList 0 (input.length + 1)

def peekTok (tokens : List Token) (pos : Nat) : Token :=
  (tokens.get? pos).getD .Eof

def advanceTok (tokens : List Token) (pos : Nat) : Token × Nat :=
  (peekTok tokens pos, pos + 1)

def expectTok (tokens : List Token) (pos : Nat) (expected : Token) : Except String Nat :=
  let t := peekTok tokens pos
  if t == expected then .ok (pos + 1)
  else .error s!"expected {repr expected}, got {repr t}"

def binop_prec : BinOp → Nat
  | .Mul | .Div | .Mod => 7
  | .Add | .Sub => 6
  | .Lt | .Le | .Gt | .Ge => 4
  | .Eq | .Ne => 3

def sortOfName (s : String) : «Sort» :=
  match s with
  | "Prop" => .Prop
  | "Type" => .Type
  | "Nat" => .Nat
  | "Int" => .Int
  | "Bool" => .Bool
  | "State" => .State
  | "Formula" => .Formula
  | "Term" => .Term
  | "MIR" => .MIR
  | "Core" => .Core
  | "Haskell" => .Haskell
  | "Rust" => .Rust
  | "Z3Expr" => .Z3Expr
  | "LeanTerm" => .LeanTerm
  | "SASAbs" => .SASAbs
  | other => .User other


-- Changed: token classifiers for the parser below. Each one is a plain,
-- non-recursive function that maps a token to the arm the original
-- parser's `match` on that token would take, in the original arm order.
-- The recursive parsers then dispatch on these small types instead of
-- matching the 71-constructor `Token` directly. Reason (measured): with a
-- direct 71-way `Token` match inside a structurally recursive definition,
-- the kernel type check of `parseFormulaAtom` alone took 58.8 s (with
-- `debug.skipKernelTC` it took 0.8 s); with the classifiers it takes 0.7 s.

/-- Arms of the original `match advanceTok tokens pos with` in `parseSort`. -/
inductive SortHead where
  | ident (s : String)
  | lparen
  | other

def sortHead : Token → SortHead
  | .Ident s => .ident s
  | .LParen => .lparen
  | _ => .other

/-- The original `let op := match peekTok tokens pos with ...` table of
`parseTermBinopLoop`, unchanged. -/
def termBinOp? : Token → Option BinOp
  | .Plus => some BinOp.Add
  | .Minus => some BinOp.Sub
  | .Star => some BinOp.Mul
  | .Slash => some BinOp.Div
  | .Percent => some BinOp.Mod
  | _ => none

/-- Arms of the original `match peekTok tokens pos with` in `parseTermAtom`. -/
inductive TermHead where
  | ident (name : String)
  | number (n : Int)
  | boolLit (b : Bool)
  | stringLit (s : String)
  | lparen
  | fun_
  | if_
  | rec_
  | other

def termHead : Token → TermHead
  | .Ident name => .ident name
  | .Number n => .number n
  | .BoolLit b => .boolLit b
  | .StringLit s => .stringLit s
  | .LParen => .lparen
  | .Fun => .fun_
  | .If => .if_
  | .Rec => .rec_
  | _ => .other

/-- The original application test after an identifier in `parseTermAtom`:
`| .Ident _ | .Number _ | .LParen | .BoolLit _ => <application>`. -/
def startsAppArg : Token → Bool
  | .Ident _ | .Number _ | .LParen | .BoolLit _ => true
  | _ => false

/-- The original `| (.Ident x, pos) => ... | (t, _) => error` matches. -/
def identOf? : Token → Option String
  | .Ident s => some s
  | _ => none

/-- The original `| .Implies | .Arrow => ...` arm of `parseFormulaImpliesLoop`. -/
def isImpliesTok : Token → Bool
  | .Implies | .Arrow => true
  | _ => false

/-- Arms of the original `match peekTok tokens pos with` in `parseFormulaAtom`. -/
inductive FAtomHead where
  | not | forall_ | exists_ | mu | nu | lparen | boolTrue | boolFalse | ravno | other

def fAtomHead : Token → FAtomHead
  | .Not => .not
  | .Forall => .forall_
  | .Exists => .exists_
  | .Mu => .mu
  | .Nu => .nu
  | .LParen => .lparen
  | .BoolLit true => .boolTrue
  | .BoolLit false => .boolFalse
  | .Ravno => .ravno
  | _ => .other

/-- Arms of the original relational `match peekTok tokens pos with` after the
left-hand term in the fallback arm of `parseFormulaAtom`. -/
inductive RelHead where
  | eq | ne | lt | le | gt | ge | none

def relHead : Token → RelHead
  | .Eq => .eq
  | .Ne => .ne
  | .Lt => .lt
  | .Le => .le
  | .Gt => .gt
  | .Ge => .ge
  | _ => .none

/-- The original last arm: a bare term in formula position (unchanged). -/
def bareTermFormula (lhs : Term) (pos : Nat) : Except String (Formula × Nat) :=
  match lhs with
  | .Var name => .ok (.Atomic (.Predicate name []), pos)
  | _ => .error s!"unexpected term in formula position: {repr lhs}"

-- Changed: the sort, term and formula parsers are ONE mutual block (the
-- original had three blocks and passed `parseFormula` into the term block
-- as the argument `parseF`). Term atoms call `parseFormula` directly. All
-- fifteen functions recurse structurally on the shared fuel argument: each
-- recursive call is on `fuel` under a `fuel + 1` pattern, and fuel `0`
-- returns the original `.error "recursion limit reached in ..."` value.
mutual

def parseSort (tokens : List Token) (pos : Nat) : Nat → Except String («Sort» × Nat)
  | 0 => .error "recursion limit reached in parse_sort"
  | fuel + 1 => do
    -- Changed: dispatch through `sortHead` (same arms, same order).
    let (t, pos') := advanceTok tokens pos
    let (base, pos) ← match sortHead t with
      | .ident s => .ok (sortOfName s, pos')
      | .lparen => do
        let (s, pos) ← parseSort tokens pos' fuel
        let pos ← expectTok tokens pos .RParen
        .ok (s, pos)
      | .other => .error s!"unexpected token in sort: {repr t}"
    parseSortArrows tokens base pos fuel
termination_by structural fuel => fuel

def parseSortArrows (tokens : List Token) (base : «Sort») (pos : Nat) : Nat → Except String («Sort» × Nat)
  | 0 => .error "recursion limit reached in parse_sort"
  | fuel + 1 =>
    if peekTok tokens pos == .Arrow then do
      let (_, pos) := advanceTok tokens pos
      let (rhs, pos) ← parseSort tokens pos fuel
      parseSortArrows tokens (.Arrow base rhs) pos fuel
    else
      .ok (base, pos)
termination_by structural fuel => fuel

-- Changed: no `parseF` parameter (term block).
def parseTerm (tokens : List Token) (pos : Nat) : Nat → Except String (Term × Nat)
  | 0 => .error "recursion limit reached in parse_term"
  | fuel + 1 => parseTermBinop tokens pos 0 fuel
termination_by structural fuel => fuel

def parseTermBinop (tokens : List Token) (pos : Nat) (minPrec : Nat) : Nat → Except String (Term × Nat)
  | 0 => .error "recursion limit reached in parse_term_binop"
  | fuel + 1 => do
    let (lhs, pos) ← parseTermAtom tokens pos fuel
    parseTermBinopLoop tokens lhs pos minPrec fuel
termination_by structural fuel => fuel

def parseTermBinopLoop (tokens : List Token) (lhs : Term) (pos : Nat) (minPrec : Nat) : Nat → Except String (Term × Nat)
  | 0 => .error "recursion limit reached in parse_term_binop"
  | fuel + 1 =>
    -- Changed: the operator table is `termBinOp?` (same table).
    match termBinOp? (peekTok tokens pos) with
    | none => .ok (lhs, pos)
    | some o =>
      let prec := binop_prec o
      if prec < minPrec then .ok (lhs, pos)
      else do
        let (_, pos) := advanceTok tokens pos
        let (rhs, pos) ← parseTermBinop tokens pos (prec + 1) fuel
        parseTermBinopLoop tokens (.BinOp o lhs rhs) pos minPrec fuel
termination_by structural fuel => fuel

def parseTermAtom (tokens : List Token) (pos : Nat) : Nat → Except String (Term × Nat)
  | 0 => .error "recursion limit reached in parse_term_atom"
  | fuel + 1 =>
    -- Changed: dispatch through `termHead` (same arms, same order).
    match termHead (peekTok tokens pos) with
    | .ident name => do
      let (_, pos) := advanceTok tokens pos
      -- Changed: the application test is `startsAppArg` (same tokens).
      if startsAppArg (peekTok tokens pos) then do
        let (arg, pos) ← parseTermAtom tokens pos fuel
        .ok (.App (.Var name) arg, pos)
      else .ok (.Var name, pos)
    | .number n => .ok (.Const (.Number n), pos + 1)
    | .boolLit b => .ok (.Const (.Bool b), pos + 1)
    | .stringLit s => .ok (.Const (.Str s), pos + 1)
    | .lparen => do
      let (_, pos) := advanceTok tokens pos
      if peekTok tokens pos == .RParen then
        .ok (.Nil, pos + 1)
      else do
        let (first, pos) ← parseTerm tokens pos fuel
        if peekTok tokens pos == .Comma then
          parseTupleRest tokens [first] pos fuel
        else do
          let pos ← expectTok tokens pos .RParen
          .ok (.Paren first, pos)
    | .fun_ => do
      let (_, pos) := advanceTok tokens pos
      -- Changed: `identOf?` replaces the `(.Ident param, pos)` pattern.
      let (t, pos) := advanceTok tokens pos
      match identOf? t with
      | some param => do
        let pos ← expectTok tokens pos .Colon
        let (sort, pos) ← parseSort tokens pos fuel
        let pos ← expectTok tokens pos .FatArrow
        let (body, pos) ← parseTerm tokens pos fuel
        .ok (.Lambda param sort body, pos)
      | none => .error s!"expected ident after fun, got {repr t}"
    | .if_ => do
      let (_, pos) := advanceTok tokens pos
      -- Changed: was `parseF tokens pos fuel` with `parseF := parseFormula`.
      let (cond, pos) ← parseFormula tokens pos fuel
      let pos ← expectTok tokens pos .Then
      let (then_, pos) ← parseTerm tokens pos fuel
      let pos ← expectTok tokens pos .Else
      let (else_, pos) ← parseTerm tokens pos fuel
      .ok (.IfThenElse cond then_ else_, pos)
    | .rec_ => do
      let (_, pos) := advanceTok tokens pos
      -- Changed: `identOf?` replaces the `(.Ident name, pos)` pattern.
      let (t, pos) := advanceTok tokens pos
      match identOf? t with
      | some name => do
        let pos ← expectTok tokens pos .Eq
        let (body, pos) ← parseTerm tokens pos fuel
        .ok (.Rec name body, pos)
      | none => .error s!"expected ident after rec, got {repr t}"
    | .other => .error s!"unexpected token in term: {repr (peekTok tokens pos)}"
termination_by structural fuel => fuel

def parseTupleRest (tokens : List Token) (elems : List Term) (pos : Nat) : Nat → Except String (Term × Nat)
  | 0 => .error "recursion limit reached in parse_tuple"
  | fuel + 1 =>
    if peekTok tokens pos == .Comma then do
      let (_, pos) := advanceTok tokens pos
      let (elem, pos) ← parseTerm tokens pos fuel
      parseTupleRest tokens (elems ++ [elem]) pos fuel
    else do
      let pos ← expectTok tokens pos .RParen
      .ok (.Tuple elems, pos)
termination_by structural fuel => fuel

def parseFormula (tokens : List Token) (pos : Nat) : Nat → Except String (Formula × Nat)
  | 0 => .error "recursion limit reached in parse_formula"
  | fuel + 1 => parseFormulaImplies tokens pos fuel
termination_by structural fuel => fuel

def parseFormulaImplies (tokens : List Token) (pos : Nat) : Nat → Except String (Formula × Nat)
  | 0 => .error "recursion limit reached in parse_formula_implies"
  | fuel + 1 => do
    let (lhs, pos) ← parseFormulaOr tokens pos fuel
    parseFormulaImpliesLoop tokens lhs pos fuel
termination_by structural fuel => fuel

def parseFormulaImpliesLoop (tokens : List Token) (lhs : Formula) (pos : Nat) : Nat → Except String (Formula × Nat)
  | 0 => .error "recursion limit reached in parse_formula_implies"
  | fuel + 1 =>
    -- Changed: the `| .Implies | .Arrow` test is `isImpliesTok`.
    if isImpliesTok (peekTok tokens pos) then do
      let (_, pos) := advanceTok tokens pos
      let (rhs, pos) ← parseFormulaOr tokens pos fuel
      parseFormulaImpliesLoop tokens (.Implies lhs rhs) pos fuel
    else .ok (lhs, pos)
termination_by structural fuel => fuel

def parseFormulaOr (tokens : List Token) (pos : Nat) : Nat → Except String (Formula × Nat)
  | 0 => .error "recursion limit reached in parse_formula_or"
  | fuel + 1 => do
    let (lhs, pos) ← parseFormulaAnd tokens pos fuel
    parseFormulaOrLoop tokens lhs pos fuel
termination_by structural fuel => fuel

def parseFormulaOrLoop (tokens : List Token) (lhs : Formula) (pos : Nat) : Nat → Except String (Formula × Nat)
  | 0 => .error "recursion limit reached in parse_formula_or"
  | fuel + 1 =>
    if peekTok tokens pos == .Or then do
      let (_, pos) := advanceTok tokens pos
      let (rhs, pos) ← parseFormulaAnd tokens pos fuel
      -- as written in the source: parse_formula_or builds Formula::And
      parseFormulaOrLoop tokens (.And [lhs, rhs]) pos fuel
    else
      .ok (lhs, pos)
termination_by structural fuel => fuel

def parseFormulaAnd (tokens : List Token) (pos : Nat) : Nat → Except String (Formula × Nat)
  | 0 => .error "recursion limit reached in parse_formula_and"
  | fuel + 1 => do
    let (lhs, pos) ← parseFormulaAtom tokens pos fuel
    parseFormulaAndLoop tokens lhs pos fuel
termination_by structural fuel => fuel

def parseFormulaAndLoop (tokens : List Token) (lhs : Formula) (pos : Nat) : Nat → Except String (Formula × Nat)
  | 0 => .error "recursion limit reached in parse_formula_and"
  | fuel + 1 =>
    if peekTok tokens pos == .And then do
      let (_, pos) := advanceTok tokens pos
      let (rhs, pos) ← parseFormulaAtom tokens pos fuel
      parseFormulaAndLoop tokens (.And [lhs, rhs]) pos fuel
    else
      .ok (lhs, pos)
termination_by structural fuel => fuel

def parseFormulaAtom (tokens : List Token) (pos : Nat) : Nat → Except String (Formula × Nat)
  | 0 => .error "recursion limit reached in parse_formula_atom"
  | fuel + 1 =>
    -- Changed: dispatch through `fAtomHead` (same arms, same order).
    match fAtomHead (peekTok tokens pos) with
    | .not => do
      let (_, pos) := advanceTok tokens pos
      let (f, pos) ← parseFormulaAtom tokens pos fuel
      .ok (.Not f, pos)
    | .forall_ => do
      let (_, pos) := advanceTok tokens pos
      -- Changed: `identOf?` replaces the `(.Ident var, pos)` pattern.
      let (t, pos) := advanceTok tokens pos
      match identOf? t with
      | some var => do
        let pos ← expectTok tokens pos .Colon
        let (sort, pos) ← parseSort tokens pos fuel
        let pos ← expectTok tokens pos .Dot
        let (body, pos) ← parseFormula tokens pos fuel
        .ok (.Forall var sort body, pos)
      | none => .error s!"expected ident after forall, got {repr t}"
    | .exists_ => do
      let (_, pos) := advanceTok tokens pos
      let (t, pos) := advanceTok tokens pos
      match identOf? t with
      | some var => do
        let pos ← expectTok tokens pos .Colon
        let (sort, pos) ← parseSort tokens pos fuel
        let pos ← expectTok tokens pos .Dot
        let (body, pos) ← parseFormula tokens pos fuel
        .ok (.Exists var sort body, pos)
      | none => .error s!"expected ident after exists, got {repr t}"
    | .mu => do
      let (_, pos) := advanceTok tokens pos
      let (t, pos) := advanceTok tokens pos
      match identOf? t with
      | some var => do
        let pos ← expectTok tokens pos .Dot
        let (body, pos) ← parseFormula tokens pos fuel
        .ok (.Mu var body, pos)
      | none => .error s!"expected ident after μ, got {repr t}"
    | .nu => do
      let (_, pos) := advanceTok tokens pos
      let (t, pos) := advanceTok tokens pos
      match identOf? t with
      | some var => do
        let pos ← expectTok tokens pos .Dot
        let (body, pos) ← parseFormula tokens pos fuel
        .ok (.Nu var body, pos)
      | none => .error s!"expected ident after ν, got {repr t}"
    | .lparen => do
      let (_, pos) := advanceTok tokens pos
      let (f, pos) ← parseFormula tokens pos fuel
      let pos ← expectTok tokens pos .RParen
      .ok (.Paren f, pos)
    | .boolTrue => .ok (.Atomic .True, pos + 1)
    | .boolFalse => .ok (.Atomic .False, pos + 1)
    | .ravno => do
      let (_, pos) := advanceTok tokens pos
      let pos ← expectTok tokens pos .LParen
      let (a, pos) ← parseTerm tokens pos fuel
      let pos ← expectTok tokens pos .Comma
      let (b, pos) ← parseTerm tokens pos fuel
      let pos ← expectTok tokens pos .RParen
      .ok (.Eq a b, pos)
    | .other => do
      let (lhs, pos) ← parseTerm tokens pos fuel
      -- Changed: dispatch through `relHead` (same arms, same order).
      match relHead (peekTok tokens pos) with
      | .eq => do
        let (_, pos) := advanceTok tokens pos
        let (rhs, pos) ← parseTerm tokens pos fuel
        .ok (.Eq lhs rhs, pos)
      | .ne => do
        let (_, pos) := advanceTok tokens pos
        let (rhs, pos) ← parseTerm tokens pos fuel
        .ok (.Not (.Eq lhs rhs), pos)
      | .lt => do
        let (_, pos) := advanceTok tokens pos
        let (rhs, pos) ← parseTerm tokens pos fuel
        .ok (.Atomic (.Predicate "<" [lhs, rhs]), pos)
      | .le => do
        let (_, pos) := advanceTok tokens pos
        let (rhs, pos) ← parseTerm tokens pos fuel
        .ok (.Atomic (.Predicate "≤" [lhs, rhs]), pos)
      | .gt => do
        let (_, pos) := advanceTok tokens pos
        let (rhs, pos) ← parseTerm tokens pos fuel
        .ok (.Atomic (.Predicate ">" [lhs, rhs]), pos)
      | .ge => do
        let (_, pos) := advanceTok tokens pos
        let (rhs, pos) ← parseTerm tokens pos fuel
        .ok (.Atomic (.Predicate "≥" [lhs, rhs]), pos)
      -- Changed: the original `match lhs with` arm is `bareTermFormula`.
      | .none => bareTermFormula lhs pos
termination_by structural fuel => fuel

end
def parseState (tokens : List Token) (pos : Nat) : Nat → Except String (State × Nat)
  | 0 => .error "recursion limit reached in parse_state"
  | fuel + 1 =>
    let (t, pos) := advanceTok tokens pos
    match t with
    | .Ident s =>
      if s == "S" then
        match peekTok tokens pos with
        | .Number n => .ok (.Sn n.toNat, pos + 1)
        | _ => .ok (.S, pos)
      else if s == "S0" then
        .ok (.S0, pos)
      else if s.startsWith "S" && s.length > 1 then
        match (s.drop 1).toNat? with
        | some n => .ok (.Sn n, pos)
        | none => .error s!"invalid state name: {s}"
      else
        .error s!"unexpected token in state: {repr t}"
    | _ => .error s!"unexpected token in state: {repr t}"


def parseRussianForm (tokens : List Token) (pos : Nat) : Nat → Except String (RussianForm × Nat)
  | 0 => .error "recursion limit reached in parse_russian_form"
  | fuel + 1 =>
    match peekTok tokens pos with
    | .Ravno => do
      let (_, pos) := advanceTok tokens pos
      let pos ← expectTok tokens pos .LParen
      -- Changed: `parseTerm` has no `parseF` argument (twice below).
      let (a, pos) ← parseTerm tokens pos fuel
      let pos ← expectTok tokens pos .Comma
      let (b, pos) ← parseTerm tokens pos fuel
      let pos ← expectTok tokens pos .RParen
      .ok (.Ravnostvo a b, pos)
    | .Sila => do
      let (_, pos) := advanceTok tokens pos
      let pos ← expectTok tokens pos .LParen
      let (state, pos) ← parseState tokens pos fuel
      let pos ← expectTok tokens pos .Comma
      let (formula, pos) ← parseFormula tokens pos fuel
      let pos ← expectTok tokens pos .RParen
      .ok (.Sila state formula, pos)
    | .Omega => do
      let (_, pos) := advanceTok tokens pos
      let pos ← expectTok tokens pos .LParen
      let (_, pos) := advanceTok tokens pos
      let pos ← expectTok tokens pos .Comma
      let (state, pos) ← parseState tokens pos fuel
      let pos ← expectTok tokens pos .Comma
      let (formula, pos) ← parseFormula tokens pos fuel
      let pos ← expectTok tokens pos .RParen
      .ok (.Omega (.Kani { name := "placeholder", params := [], return_sort := .Bool, body := [] }) state formula, pos)
    | .Dokazatelstvo => do
      let (_, pos) := advanceTok tokens pos
      .ok (.Dokazatelstvo { obligations := [] }, pos)
    | t => .error s!"unexpected Russian form: {repr t}"



-- Changed (comment only): why `tokens.length * 8 + 16` is enough fuel.
-- Fuel is spent per call depth, not per token: sibling calls get the same
-- fuel. Without consuming a token, a call chain is at most
--   parseFormula → Implies → Or → And → FormulaAtom → parseTerm → Binop → TermAtom
-- (8 calls), and every recursive cycle of the call graph consumes a token
-- first (an operator, `(`, `¬`, a quantifier, `if`, `fun`, `rec`, `,`,
-- `→`, or an identifier in an application). So depth grows by at most 8
-- per consumed token, and depth stays below tokens.length * 8 + 16. The
-- budget is the original's. This argument is not yet a Lean theorem; the
-- tests in Russian_checked_tests.lean check on every reference case that
-- four times the budget gives the same result.
def parse_russian (input : String) : Except String RussianForm :=
  let tokens := tokenize input
  let fuel := tokens.length * 8 + 16
  match parseRussianForm tokens 0 fuel with
  | .ok (form, _) => .ok form
  | .error e => .error e

def parse_formula (input : String) : Except String Formula :=
  let tokens := tokenize input
  let fuel := tokens.length * 8 + 16
  match parseFormula tokens 0 fuel with
  | .ok (f, _) => .ok f
  | .error e => .error e

def parse_term (input : String) : Except String Term :=
  let tokens := tokenize input
  let fuel := tokens.length * 8 + 16
  -- Changed: was `parseTerm parseFormula tokens 0 fuel`.
  match parseTerm tokens 0 fuel with
  | .ok (t, _) => .ok t
  | .error e => .error e

-- The two end-to-end checks below are kept out of the theorem list:
-- kernel reduction of String.toList / string equality in `decide` /
-- `rfl` over the lexer and parser is prohibitively slow (the `lean`
-- process ran for 9+ minutes on this file). The same checks are run
-- by runtime evaluation (#eval) in a scratch file instead; see
-- STATUS.md. The lexer and parser themselves are unchanged.
-- theorem tokenize_ravnostvo :
--     tokenize "равенство(x, y)" =
--       [.Ravno, .LParen, .Ident "x", .Comma, .Ident "y", .RParen, .Eof] := by decide
-- theorem parse_ravnostvo :
--     parse_russian "равенство(x, y)" = .ok (.Ravnostvo (.Var "x") (.Var "y")) := by rfl

end Crux
