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
set_option maxHeartbeats 10000000

namespace Crux

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

mutual

def parseSort (tokens : List Token) (pos : Nat) : Nat → Except String («Sort» × Nat)
  | 0 => .error "recursion limit reached in parse_sort"
  | fuel + 1 => do
    let (base, pos) ← match advanceTok tokens pos with
      | (.Ident s, pos) => .ok (sortOfName s, pos)
      | (.LParen, pos) => do
        let (s, pos) ← parseSort tokens pos fuel
        let pos ← expectTok tokens pos .RParen
        .ok (s, pos)
      | (t, _) => .error s!"unexpected token in sort: {repr t}"
    parseSortArrows tokens base pos fuel


termination_by fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _
def parseSortArrows (tokens : List Token) (base : «Sort») (pos : Nat) : Nat → Except String («Sort» × Nat)
  | 0 => .error "recursion limit reached in parse_sort"
  | fuel + 1 =>
    if peekTok tokens pos == .Arrow then do
      let (_, pos) := advanceTok tokens pos
      let (rhs, pos) ← parseSort tokens pos fuel
      parseSortArrows tokens (.Arrow base rhs) pos fuel
    else
      .ok (base, pos)


termination_by fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _

end
mutual
def parseTerm (parseF : List Token → Nat → Nat → Except String (Formula × Nat)) (tokens : List Token) (pos : Nat) : Nat → Except String (Term × Nat)
  | 0 => .error "recursion limit reached in parse_term"
  | fuel + 1 => parseTermBinop parseF tokens pos 0 fuel


termination_by fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _
def parseTermBinop (parseF : List Token → Nat → Nat → Except String (Formula × Nat)) (tokens : List Token) (pos : Nat) (minPrec : Nat) : Nat → Except String (Term × Nat)
  | 0 => .error "recursion limit reached in parse_term_binop"
  | fuel + 1 => do
    let (lhs, pos) ← parseTermAtom parseF tokens pos fuel
    parseTermBinopLoop parseF tokens lhs pos minPrec fuel


termination_by fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _
def parseTermBinopLoop (parseF : List Token → Nat → Nat → Except String (Formula × Nat)) (tokens : List Token) (lhs : Term) (pos : Nat) (minPrec : Nat) : Nat → Except String (Term × Nat)
  | 0 => .error "recursion limit reached in parse_term_binop"
  | fuel + 1 =>
    let op := match peekTok tokens pos with
      | .Plus => some BinOp.Add
      | .Minus => some BinOp.Sub
      | .Star => some BinOp.Mul
      | .Slash => some BinOp.Div
      | .Percent => some BinOp.Mod
      | _ => none
    match op with
    | none => .ok (lhs, pos)
    | some o =>
      let prec := binop_prec o
      if prec < minPrec then .ok (lhs, pos)
      else do
        let (_, pos) := advanceTok tokens pos
        let (rhs, pos) ← parseTermBinop parseF tokens pos (prec + 1) fuel
        parseTermBinopLoop parseF tokens (.BinOp o lhs rhs) pos minPrec fuel


termination_by fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _
def parseTermAtom (parseF : List Token → Nat → Nat → Except String (Formula × Nat)) (tokens : List Token) (pos : Nat) : Nat → Except String (Term × Nat)
  | 0 => .error "recursion limit reached in parse_term_atom"
  | fuel + 1 =>
    match peekTok tokens pos with
    | .Ident name => do
      let (_, pos) := advanceTok tokens pos
      match peekTok tokens pos with
      | .Ident _ | .Number _ | .LParen | .BoolLit _ => do
        let (arg, pos) ← parseTermAtom parseF tokens pos fuel
        .ok (.App (.Var name) arg, pos)
      | _ => .ok (.Var name, pos)
    | .Number n => .ok (.Const (.Number n), pos + 1)
    | .BoolLit b => .ok (.Const (.Bool b), pos + 1)
    | .StringLit s => .ok (.Const (.Str s), pos + 1)
    | .LParen => do
      let (_, pos) := advanceTok tokens pos
      if peekTok tokens pos == .RParen then
        .ok (.Nil, pos + 1)
      else do
        let (first, pos) ← parseTerm parseF tokens pos fuel
        if peekTok tokens pos == .Comma then
          parseTupleRest parseF tokens [first] pos fuel
        else do
          let pos ← expectTok tokens pos .RParen
          .ok (.Paren first, pos)
    | .Fun => do
      let (_, pos) := advanceTok tokens pos
      match advanceTok tokens pos with
      | (.Ident param, pos) => do
        let pos ← expectTok tokens pos .Colon
        let (sort, pos) ← parseSort tokens pos fuel
        let pos ← expectTok tokens pos .FatArrow
        let (body, pos) ← parseTerm parseF tokens pos fuel
        .ok (.Lambda param sort body, pos)
      | (t, _) => .error s!"expected ident after fun, got {repr t}"
    | .If => do
      let (_, pos) := advanceTok tokens pos
      let (cond, pos) ← parseF tokens pos fuel
      let pos ← expectTok tokens pos .Then
      let (then_, pos) ← parseTerm parseF tokens pos fuel
      let pos ← expectTok tokens pos .Else
      let (else_, pos) ← parseTerm parseF tokens pos fuel
      .ok (.IfThenElse cond then_ else_, pos)
    | .Rec => do
      let (_, pos) := advanceTok tokens pos
      match advanceTok tokens pos with
      | (.Ident name, pos) => do
        let pos ← expectTok tokens pos .Eq
        let (body, pos) ← parseTerm parseF tokens pos fuel
        .ok (.Rec name body, pos)
      | (t, _) => .error s!"expected ident after rec, got {repr t}"
    | t => .error s!"unexpected token in term: {repr t}"


termination_by fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _
def parseTupleRest (parseF : List Token → Nat → Nat → Except String (Formula × Nat)) (tokens : List Token) (elems : List Term) (pos : Nat) : Nat → Except String (Term × Nat)
  | 0 => .error "recursion limit reached in parse_tuple"
  | fuel + 1 =>
    if peekTok tokens pos == .Comma then do
      let (_, pos) := advanceTok tokens pos
      let (elem, pos) ← parseTerm parseF tokens pos fuel
      parseTupleRest parseF tokens (elems ++ [elem]) pos fuel
    else do
      let pos ← expectTok tokens pos .RParen
      .ok (.Tuple elems, pos)


termination_by fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _

end
mutual
def parseFormula (tokens : List Token) (pos : Nat) : Nat → Except String (Formula × Nat)
  | 0 => .error "recursion limit reached in parse_formula"
  | fuel + 1 => parseFormulaImplies tokens pos fuel


termination_by fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _
def parseFormulaImplies (tokens : List Token) (pos : Nat) : Nat → Except String (Formula × Nat)
  | 0 => .error "recursion limit reached in parse_formula_implies"
  | fuel + 1 => do
    let (lhs, pos) ← parseFormulaOr tokens pos fuel
    parseFormulaImpliesLoop tokens lhs pos fuel


termination_by fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _
def parseFormulaImpliesLoop (tokens : List Token) (lhs : Formula) (pos : Nat) : Nat → Except String (Formula × Nat)
  | 0 => .error "recursion limit reached in parse_formula_implies"
  | fuel + 1 =>
    match peekTok tokens pos with
    | .Implies | .Arrow => do
      let (_, pos) := advanceTok tokens pos
      let (rhs, pos) ← parseFormulaOr tokens pos fuel
      parseFormulaImpliesLoop tokens (.Implies lhs rhs) pos fuel
    | _ => .ok (lhs, pos)


termination_by fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _
def parseFormulaOr (tokens : List Token) (pos : Nat) : Nat → Except String (Formula × Nat)
  | 0 => .error "recursion limit reached in parse_formula_or"
  | fuel + 1 => do
    let (lhs, pos) ← parseFormulaAnd tokens pos fuel
    parseFormulaOrLoop tokens lhs pos fuel


termination_by fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _
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


termination_by fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _
def parseFormulaAnd (tokens : List Token) (pos : Nat) : Nat → Except String (Formula × Nat)
  | 0 => .error "recursion limit reached in parse_formula_and"
  | fuel + 1 => do
    let (lhs, pos) ← parseFormulaAtom tokens pos fuel
    parseFormulaAndLoop tokens lhs pos fuel


termination_by fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _
def parseFormulaAndLoop (tokens : List Token) (lhs : Formula) (pos : Nat) : Nat → Except String (Formula × Nat)
  | 0 => .error "recursion limit reached in parse_formula_and"
  | fuel + 1 =>
    if peekTok tokens pos == .And then do
      let (_, pos) := advanceTok tokens pos
      let (rhs, pos) ← parseFormulaAtom tokens pos fuel
      parseFormulaAndLoop tokens (.And [lhs, rhs]) pos fuel
    else
      .ok (lhs, pos)


termination_by fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _
def parseFormulaAtom (tokens : List Token) (pos : Nat) : Nat → Except String (Formula × Nat)
  | 0 => .error "recursion limit reached in parse_formula_atom"
  | fuel + 1 =>
    match peekTok tokens pos with
    | .Not => do
      let (_, pos) := advanceTok tokens pos
      let (f, pos) ← parseFormulaAtom tokens pos fuel
      .ok (.Not f, pos)
    | .Forall => do
      let (_, pos) := advanceTok tokens pos
      match advanceTok tokens pos with
      | (.Ident var, pos) => do
        let pos ← expectTok tokens pos .Colon
        let (sort, pos) ← parseSort tokens pos fuel
        let pos ← expectTok tokens pos .Dot
        let (body, pos) ← parseFormula tokens pos fuel
        .ok (.Forall var sort body, pos)
      | (t, _) => .error s!"expected ident after forall, got {repr t}"
    | .Exists => do
      let (_, pos) := advanceTok tokens pos
      match advanceTok tokens pos with
      | (.Ident var, pos) => do
        let pos ← expectTok tokens pos .Colon
        let (sort, pos) ← parseSort tokens pos fuel
        let pos ← expectTok tokens pos .Dot
        let (body, pos) ← parseFormula tokens pos fuel
        .ok (.Exists var sort body, pos)
      | (t, _) => .error s!"expected ident after exists, got {repr t}"
    | .Mu => do
      let (_, pos) := advanceTok tokens pos
      match advanceTok tokens pos with
      | (.Ident var, pos) => do
        let pos ← expectTok tokens pos .Dot
        let (body, pos) ← parseFormula tokens pos fuel
        .ok (.Mu var body, pos)
      | (t, _) => .error s!"expected ident after μ, got {repr t}"
    | .Nu => do
      let (_, pos) := advanceTok tokens pos
      match advanceTok tokens pos with
      | (.Ident var, pos) => do
        let pos ← expectTok tokens pos .Dot
        let (body, pos) ← parseFormula tokens pos fuel
        .ok (.Nu var body, pos)
      | (t, _) => .error s!"expected ident after ν, got {repr t}"
    | .LParen => do
      let (_, pos) := advanceTok tokens pos
      let (f, pos) ← parseFormula tokens pos fuel
      let pos ← expectTok tokens pos .RParen
      .ok (.Paren f, pos)
    | .BoolLit true => .ok (.Atomic .True, pos + 1)
    | .BoolLit false => .ok (.Atomic .False, pos + 1)
    | .Ravno => do
      let (_, pos) := advanceTok tokens pos
      let pos ← expectTok tokens pos .LParen
      let (a, pos) ← parseTerm parseFormula tokens pos fuel
      let pos ← expectTok tokens pos .Comma
      let (b, pos) ← parseTerm parseFormula tokens pos fuel
      let pos ← expectTok tokens pos .RParen
      .ok (.Eq a b, pos)
    | _ => do
      let (lhs, pos) ← parseTerm parseFormula tokens pos fuel
      match peekTok tokens pos with
      | .Eq => do
        let (_, pos) := advanceTok tokens pos
        let (rhs, pos) ← parseTerm parseFormula tokens pos fuel
        .ok (.Eq lhs rhs, pos)
      | .Ne => do
        let (_, pos) := advanceTok tokens pos
        let (rhs, pos) ← parseTerm parseFormula tokens pos fuel
        .ok (.Not (.Eq lhs rhs), pos)
      | .Lt => do
        let (_, pos) := advanceTok tokens pos
        let (rhs, pos) ← parseTerm parseFormula tokens pos fuel
        .ok (.Atomic (.Predicate "<" [lhs, rhs]), pos)
      | .Le => do
        let (_, pos) := advanceTok tokens pos
        let (rhs, pos) ← parseTerm parseFormula tokens pos fuel
        .ok (.Atomic (.Predicate "≤" [lhs, rhs]), pos)
      | .Gt => do
        let (_, pos) := advanceTok tokens pos
        let (rhs, pos) ← parseTerm parseFormula tokens pos fuel
        .ok (.Atomic (.Predicate ">" [lhs, rhs]), pos)
      | .Ge => do
        let (_, pos) := advanceTok tokens pos
        let (rhs, pos) ← parseTerm parseFormula tokens pos fuel
        .ok (.Atomic (.Predicate "≥" [lhs, rhs]), pos)
      | _ =>
        match lhs with
        | .Var name => .ok (.Atomic (.Predicate name []), pos)
        | _ => .error s!"unexpected term in formula position: {repr lhs}"


termination_by fuel => fuel
decreasing_by all_goals exact Nat.lt_succ_self _
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
      let (a, pos) ← parseTerm parseFormula tokens pos fuel
      let pos ← expectTok tokens pos .Comma
      let (b, pos) ← parseTerm parseFormula tokens pos fuel
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
  match parseTerm parseFormula tokens 0 fuel with
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
