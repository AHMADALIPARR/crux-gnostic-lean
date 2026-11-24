# CRUX — Lean 4 Port

CRUX is a port of the CRUX / SILA / OMEGA-SMASHER Rust stack to Lean 4. It mirrors the Rust crate module for module: a recursive state IR with a Russian-syntax front end, a dual backend (GHC | Kani), an OMEGA smasher dispatching to Z3, SAS, and Lean provers, proof-carrying certificates, a pipeline driver, constraint search, and suspension propagation.

## Modules

- `Crux.Ast` — the recursive state IR: terms, formulas, states, backends, Z3 and SAS queries, Lean goals and tactics, obligations, proof closures.
- `Crux.LeanMonadStack` — Lean 4 monad-layer tables: MetaM, TacticM, MacroM, MonadQuotation, and the recursive tactic layer.
- `Crux.LeanBackend` — the Lean prover: goal construction, tactic and macro dispatch, and the Lean 4 serializers.
- `Crux.TacticInfra` — tactic-state operations, focus management, macro scopes, and recursive goals.
- `Crux.Domain` — constraint domains (Range, Set, Fixed, Free) and the domain store.
- `Crux.Arithmetic` — constraint evaluation over the domain store (partial: the source file ends mid-function in the `Lt` arm).
- `Crux.Z3Backend` — the Z3 solver front end and SMT-LIB query builder.
- `Crux.SasBackend` — the SAS abstract-interpretation analyzer.
- `Crux.Omega` — the OMEGA smasher: Z3, then Lean, then SAS, in that priority order.
- `Crux.Pcc` — proof-carrying code: derivations, certificates, and certified states.
- `Crux.Russian` — the Russian-syntax lexer and recursive-descent parser.
- `Crux.Pipeline` — the pipeline driver: parse, lower, dispatch to a backend, smash, and close.
- `Crux.Search` — constraint search over the domain store.
- `Crux.Suspension` — suspension entries and propagation.

The `rust/` directory holds the Rust sources verbatim as sent, mojibake included.

## Build

The project uses Lean 4.19.0 (`leanprover/lean4:v4.19.0`) with no dependencies and no Mathlib, pure Lean 4 core. The toolchain lives at `~/.elan/bin`. Build with:

```
export PATH="$HOME/.elan/bin:$PATH"
lake build
```
