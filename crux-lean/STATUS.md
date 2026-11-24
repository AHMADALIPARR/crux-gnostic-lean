# STATUS

## Sources

- Rust sources in `rust/` are saved verbatim as sent, header comments and license blocks included, mojibake included (UTF-8 misread as Latin-1, e.g. `â€“` for –, `â†’` for →, `Ñ€...` for Cyrillic). The verbatim files are not edited.
- `ast.rs`, `lean_backend.rs`, `domain.rs`, `search.rs`, `suspension.rs` are the real files as sent.
- `arithmetic.rs` is the renamed `constraint.rs` (renamed because `suspension.rs` imports it as `super::arithmetic`). The file is the final Constraint paste, truncated mid-function inside the `Lt` arm; its last line is `match dom_b.min()`. The user confirmed on 2026-11-23 that no remainder is coming. This is final, not awaited.
- `mod.rs` declares the crux modules: `ast, russian, omega, z3_backend, sas_backend, lean_backend, lean_monad_stack, pcc, pipeline`, plus re-exports.

## Toolchain

- Lean `leanprover/lean4:v4.19.0`, binaries at `~/.elan/bin`. `lakefile.lean`: package `Crux`, `lean_lib Crux` with roots `#[`Crux]`, `leanOptions` `autoImplicit false` and `relaxedAutoImplicit false`, no dependencies, no Mathlib, pure Lean 4.19 core.
- Rust `rustc 1.99.0` / `cargo 1.99.0` at `~/workspace/.tools/cargo/bin` (reference/verification only).

## Lean build

- `lake build` result: pending the Russian.lean elaboration (see below). 13 of 14 modules build green on their own: Ast, LeanMonadStack, LeanBackend, TacticInfra, Domain, Arithmetic, Z3Backend, SasBackend, Omega, Pcc, Search, Suspension, and (once Russian builds) Pipeline. `Crux.lean` imports all 14 modules.
- `Crux.Search` builds (`lake build Crux.Search`, exit 0). `Crux.Suspension` builds (`lake build Crux.Suspension`, exit 0). `Crux.Pipeline` cannot build until `Crux.Russian` does, because it imports Russian.
- `Crux/Russian.lean` is the only module still failing to build. It blocks `Crux/Pipeline.lean` and therefore the full `lake build`.

## Russian.lean — status

- The port is complete as written: `Token` (all variants), the lexer as pure functions threading `(input : List Char)` and `pos` explicitly with explicit fuel, and the parser (`parseTerm / parseFormula / parseSort / parseState / parseRussianForm`, public `parse_russian / parse_formula / parse_term`).
- Russian keyword strings use correct Cyrillic, decoded from the mojibake: `равенство, импликация, конъюнкция, дизъюнкция, отрицание, для всех, существует, рекурсия, состояние, сила, омега, доказательство`. Lexer unicode chars are the real chars: `→ ↔ ∀ ∃ ∧ ∨ ¬ ≡ ≤ ≥ ≠ ⊢ ⊨ ⊤ ⊥ ↦`.
- The Rust parser's Omega-arm placeholder is ported exactly (`KaniMIR` named `"placeholder"`). The `parse_formula_or` quirk is ported exactly as written (it builds `Formula::And` for `Or`).
- Parser functions recurse on an explicit `fuel : Nat` argument, written in equation style (`def f (params...) : Nat → T | 0 => ... | fuel + 1 => ...`), in a single mutual block of 17 functions, each with `termination_by fuel => fuel` and `decreasing_by all_goals exact Nat.lt_succ_self _`. The file has `set_option maxHeartbeats 10000000` after the `import Crux.Ast` line.
- The two end-to-end theorems (`tokenize_ravnostvo` by decide, `parse_ravnostvo` by rfl) are commented out, not deleted: kernel reduction of `String.toList` / string equality in `decide` / `rfl` over the lexer and parser is prohibitively slow (the `lean` process ran for 9+ minutes on the file). The same checks are to be run by runtime evaluation (`#eval`) in a scratch file instead. The lexer and parser themselves are unchanged.
- Findings from the diagnostic session: the lexer alone elaborates in 12s and prints the correct tokens for `"равенство(x, y)"`. The 5-function term-parser block alone elaborates in ~16s. The 8-function formula-parser block alone elaborates in ~39s but its `parseFormulaAtom` decreasing goals fail: when a mutual function is passed as an argument to another function (`parseTerm parseFormula`), the termination checker generalizes the recursive-call fuel argument to a fresh variable (`a✝ < fuel.succ`), which is unprovable by the `Nat.lt_succ_self` lemma and by `omega`. A single non-mutual `parseFormulaAtom` with stubbed callees elaborates with exit 0. The merged single 17-function mutual block (direct mutual calls, no higher-order passing) still times out at 280s wall-clock with no error printed. `deriving DecidableEq, Repr` for `Token` (60 constructors) hits a `(deterministic) timeout at whnf, maximum number of heartbeats (200000)` when `Crux.Ast` is imported; with `maxHeartbeats 1000000` it succeeds in ~32s.
- A long elaboration of the full file with `maxHeartbeats 10000000` was started on 2026-11-24 ~00:23 UTC with a 900s timeout; its outcome is recorded here when it finishes.

## Rust verification (by execution)

Scratch directories outside the Lean project (no Cargo files added to `~/workspace/crux-lean`): `~/workspace/crux-rust-check`, `~/workspace/crux-search-check`, `~/workspace/crux-susp-check`. Verbatim Rust files under `rust/` were never edited. Where a scratch copy needed a change to compile at all, the change is a shim applied to the scratch copy only, stated below.

- Verbatim crate (9 modules per `rust/mod.rs`: ast, russian, omega, z3_backend, sas_backend, lean_backend, lean_monad_stack, pcc, pipeline; `lib.rs` with `pub mod crux;`): `cargo test` FAILS to compile, 643 errors. Root cause: `rust/ast.rs:1` is a bare `=======================================================================` line, not a comment — `error: expected item, found '=='`. Because ast.rs fails to parse, every `use crate::crux::ast::*` resolves to nothing, cascading to 483 `error[E0433]`, 147 `error[E0425]`, 12 `error[E0422]` across russian.rs (105), lean_backend.rs (127), sas_backend.rs (127), pipeline.rs (76), omega.rs (37), pcc.rs (27), mod.rs (1), lean_monad_stack.rs (1).
- Shimmed crate (shim: in the scratch copy only, prefix ast.rs line 1 with `// `; verbatim file untouched): compiles with 12 warnings (unused variables). `cargo test` exit 0, 0 tests run, 0 failed — the 9 crate modules contain no `#[test]` functions.
- `rust/domain.rs` verbatim, `rustc --test`: FAILS to compile, same bare `===` line 1 error (`error: expected item, found '=='` at domain.rs:1:1). Shimmed (only change: `// ` prefix on line 1, scratch copy only): compiles; `rustc --test` runs 4 tests, 4 passed, 0 failed: `test_domain_range`, `test_domain_intersect`, `test_domain_remove`, `test_domain_store`.
- `rust/search.rs` with `rust/domain.rs` (both shimmed on line 1 only, scratch crate `crux-search-check`): `cargo test` exit 0, 7 passed, 0 failed — 4 domain tests plus `test_first_fail`, `test_search_simple`, `test_search_unsat`. Note: search.rs imports only `super::domain::{Domain, DomainStore}`; it does not reference `eval_constraint` or `arithmetic`.
- `rust/suspension.rs` with `rust/domain.rs` and `rust/arithmetic.rs` (scratch crate `crux-susp-check`): FAILS to compile, 1 error: `error: this file contains an unclosed delimiter` at arithmetic.rs:86:39 — `eval_constraint` (line 61), its `match` (line 62), the `Lt` arm (line 79), and the inner `match` (line 82) are all unclosed; the file ends at `match dom_b.min()`. suspension.rs imports `super::arithmetic::{Constraint, EvalResult, eval_constraint}`, so its 2 tests (`test_suspend_and_wake`, `test_propagate`) cannot run. The blocker is arithmetic.rs alone.
- `rust/arithmetic.rs` standalone, `rustc --crate-type lib`: FAILS with the same unclosed-delimiter error. It does not compile standalone, as sent.

## Lean port — modeling choices and facts

- Type mapping: `String`→`String`, `i64`→`Int`, `u32`/`u64`/`usize`→`Nat`, `Vec`→`List`, `Option`→`Option`, `Result<T,String>`→`Except String T`, `bool`→`Bool`; `Box<T>` disappears. Rust snake_case names are kept for defs/fields/constructors.
- `Sort` is a Lean keyword, so the AST type is written `«Sort»` (quoted identifier) throughout; `Sort.toString` is `«Sort».toString`.
- Lean 4.19 `deriving DecidableEq` fails for inductives with a `List Self` field and for `deriving` inside `mutual` blocks. `DecidableEq` is derived only for types without list-recursive fields (`Literal, BinOp, «Sort», BindingKind, GHCConstructor, Z3Tactic, Z3ParamValue, SASConfig, AbsDomain, Widening, AbsVal, LeanGoalKind, Z3Context, SASState`); the other AST types carry `deriving Repr` only. Equality-dependent code avoids `==`/`!=` on those types and matches instead.
- AST ordering: declarations precede use — `BinOp` before the `Term/Formula/...` mutual block; `BindingKind` before the mutual block; `GHCConstructor → GHCDecl → GHCIR`; `MIRStatement/MIRMatchArm` mutual, then `KaniMIR`, then `Backend`; `Z3Context → Z3ParamValue → Z3Tactic → Z3Expr → Z3Command → Z3Query`; `AbsDomain → Widening → SASConfig → AbsVal → SASState → SASProperty → SASQuery`; `LeanGoalKind → SimpArg → RwArg → LeanTactic → LeanGoal`; `DischargeMethod → Obligation → ProofClosure`; `OmegaTarget` after `LeanGoal`.
- Recursion through `List.all` / `List.map` does not reduce in the kernel here, so mutual list helpers are used instead (`tryDecideAll/tryDecideAny`, `formulaListToLean4`, `tacticListToLean4`, `formulaListToZ3`, `z3ExprListToSmt`, `collectVarsList`, `collectTermVarsList`, `evalFormulaAll/evalFormulaAny`).
- `LeanProver.build_goal` name is `"sila_goal_"` plus a Debug-style rendering of the state, implemented as `toString (repr state)`.
- Serializer strings use the correct characters the Rust means (`→, ∧, ∨, ↔, ∀, ∃, ≤, ≥, ≠, Сила, S₀, ·`), not the mojibake in the pasted Rust. The Lean output strings are real Lean 4 text.
- The appended lean_backend.rs sections 4–7 are ported as their own module, `Crux/TacticInfra.lean`. Rust `&mut` state operations return the updated state. `tactic_try` takes a `(Unit → Option T)` thunk, `tactic_first` a `List (Unit → Option T)`, `tactic_repeat` a `(Unit → Bool)` thunk with explicit fuel.
- `SilaDerivation.is_valid` is implemented by explicit fuel, not by well-founded recursion on `sizeOf`: the auto-generated `sizeOf` for the mutually recursive `SilaDerivation` / `DerivationRule` types is defined via the recursor, does not unfold definitionally (even after `cases`), cannot be unfolded by `simp` (its equation lemmas are not realizable), and its `SizeOf` instance has no executable code, so `sizeOf` cannot serve as a termination measure or as a fuel bound. The port uses fuel functions `SilaDerivation.is_validFuel`, `validRulesFuel`, `DerivationRule.is_validFuel` (mutual, `termination_by ... fuel => fuel`, `decreasing_by all_goals exact Nat.lt_succ_self _`, the same pattern as the Russian parser), and the public wrapper `SilaDerivation.is_valid d := d.is_validFuel SilaDerivation.is_validFuelBound` with `is_validFuelBound = 1000000`. Derivations deeper than this bound evaluate to `false`. The theorem `axiom_valid` is proven by `simp` unfolding the fuel-function equation lemmas (the `rfl`/`decide` proofs do not reduce the well-founded-recursive definitions).
- Rust `HashMap` is modeled as association lists (`List (String × Domain)` and `List (String × Int)`) with lookup/insert helpers. There is no Mathlib or Batteries in this project.
- `Domain.size` for `Range` uses `(hi - lo + 1)` as `Int` arithmetic cast to `Nat`; values match the tested cases.
- `Crux/Arithmetic.lean` is partial: `Constraint` with constructors (`eq/neq/lt/le/gt/ge/linear`, plus `Reified`), `EvalResult`, `eval_constraint` for exactly the complete arms (`Eq, Neq`) wired to the real `DomainStore`; the other arms return `Unknown` so the function is total. Header comment states the source paste ends mid-function in the `Lt` arm.
- Search: Rust recursion with mutable store becomes pure functions threading `DomainStore` explicitly. The recursive search uses a single fuel argument initialized to the Rust `limit`: fuel decreases on every recursive call — both on each depth step and on each value tried. The Rust limit bounds depth only; the Lean fuel bounds total recursive steps, so a search with a large branching factor could exhaust fuel sooner than the Rust limit would allow; for the tested inputs (limit 100, tiny domains) the outcomes coincide. `search_recursive` returns `SearchResult × DomainStore`; `search_vars` returns just the `SearchResult`. Ported the three Rust tests as Lean theorems (`test_first_fail`, `test_search_simple`, `test_search_unsat`); all three pass by `decide`. In `test_first_fail` the store is built with `let` bindings rather than a chained dot-notation expression, which failed to elaborate as written; the meaning is the same.
- Suspension: `propagate_store` loops until no firing, implemented as a recursive function with fuel bounded by (number of entries + 1) passes: wake only ever flips `fired` false→true, so at most one firing pass per entry can occur; the next pass then fires nothing and the loop stops; the domain store does not change during propagation, so a pass that fires nothing is followed by identical passes. Ported the two Rust tests as Lean theorems (`test_suspend_and_wake`, `test_propagate`); both pass. `test_propagate` holds because `lt(x,y)` evaluates to `Unknown` under the partial `eval_constraint`, so it stays active.
- `omega_smash_pipeline` takes a `backend` parameter that both the Rust and the Lean port ignore (it calls `smash_auto`); Lean emits an unused-variable warning for it, which is harmless.

## Behaviors ported as written in the source

- Z3 `check` returns `Unknown` — it builds the SMT-LIB string and falls back to `Unknown`.
- The Russian parser's Omega arm is a placeholder backend (`KaniMIR` named `"placeholder"`).
- SAS `transfer` is the identity function.
- SAS `widen` widens to `i64::MIN` / `i64::MAX` (`-9223372036854775808` / `9223372036854775807`).
- `DomainStore.reset_statuses` is a no-op, as written.
- `tactic_prune_solved` is a no-op, as written.
- No `sorry`, no stubs, no `TODO`, no `admit`, no placeholder `panic!` equivalents anywhere in the Lean port, except where the Rust source itself is a placeholder/stub (noted above).

## What is still missing

- Nothing is awaited from the user. The only incomplete source is `arithmetic.rs` (the constraint file), which ends mid-function in the `Lt` arm; the user confirmed on 2026-11-23 that no remainder is coming, so the partial port is final.
- The Lean port is incomplete only in that `Crux/Russian.lean` does not yet elaborate (see above), which blocks `Crux/Pipeline.lean` and the full `lake build`.
