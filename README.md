<!-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0 -->
<!-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab -->

# crux-gnostic-lean

[![CI](https://github.com/AHMADALIPARR/crux-gnostic-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/AHMADALIPARR/crux-gnostic-lean/actions/workflows/ci.yml)
[![License: AGPL-3.0 OR SnapKitty Opaque 1.0](https://img.shields.io/badge/license-AGPL--3.0--only%20OR%20SnapKitty%20Opaque%201.0-blue)](LICENSE)
![Lean 4.19.0](https://img.shields.io/badge/Lean-4.19.0-black)
![Zig 0.17.1](https://img.shields.io/badge/Zig-0.17.1-orange)
![Nim 2.4.2](https://img.shields.io/badge/Nim-2.4.2-yellow)

Two Lean 4 libraries, one for a constraint-and-proof pipeline and one for Abjad arithmetic, both pinned to Lean 4.19.0 with no package dependencies and no Mathlib.

**CRUX** is the Lean 4 port of the CRUX / SILA / OMEGA-SMASHER stack. It gives a recursive state IR a Russian-syntax front end, constraint domains and search, an OMEGA smasher that tries Z3, then Lean, then SAS, proof-carrying certificates, a pipeline driver, and suspension propagation.

**Gnostic Arabic** is a Lean 4 development of the Abjad matrix: the twenty-eight Arabic letters and their values, Jamāl/Jalāl polarity, the 3×3 Allah wafq, decoherence quadrants, pillar constants, and the Al-Hamid matrix, with the corresponding identities stated as theorems.

## Features

### CRUX (`crux-lean`)

- `Crux.Ast` — the recursive state IR: terms, formulas, states, backends, Z3 and SAS queries, Lean goals and tactics, obligations, and proof closures.
- `Crux.LeanMonadStack` — Lean 4 monad-layer tables: MetaM, TacticM, MacroM, MonadQuotation, and the recursive tactic layer.
- `Crux.LeanBackend` — the Lean prover: goal construction, tactic and macro dispatch, and the Lean 4 serializers.
- `Crux.TacticInfra` — tactic-state operations, focus management, macro scopes, and recursive goals.
- `Crux.Domain` — constraint domains (Range, Set, Fixed, Free) and the domain store, as association lists.
- `Crux.Arithmetic` — constraint evaluation over the domain store. `Eq` and `Neq` are decided from a variable's value or domain; the remaining constructors return `Unknown`.
- `Crux.Z3Backend` — the Z3 solver front end and SMT-LIB query builder. `check` builds the SMT-LIB query and returns `Unknown`.
- `Crux.SasBackend` — the SAS abstract-interpretation analyzer over interval domains, with a fuel-bounded fixpoint.
- `Crux.Omega` — the OMEGA smasher: Z3, then Lean, then SAS, in that priority order.
- `Crux.Pcc` — proof-carrying code: derivations, certificates, and certified states.
- `Crux.Russian` — the Russian-syntax lexer and recursive-descent parser, with Cyrillic keywords and a fuel-bounded descent.
- `Crux.Pipeline` — the pipeline driver: parse, lower, dispatch to a backend, smash, and close.
- `Crux.Search` — constraint search over the domain store, fuel-bounded by the search limit.
- `Crux.Suspension` — suspension entries and propagation over watched variables.

### Gnostic Arabic (`gnostic-arabic-lean`)

- `GnosticArabic.AbjadMatrix` — `ArabicLetter` and Abjad values, polarity, digit root, equilibrium, the 3×3 Allah wafq (`Wafq.verify`), decoherence quadrants, hieroglyph decoding, the Al-Hamid matrix, and the four pillars.
- Theorems, all proved by `decide`, record the letter-sum identities (`test_al_hamid`, `test_allah_equilibrium`), the wafq row, column, and diagonal sums (`test_wafq_allah_rows_columns`, `test_wafq_allah_diagonals`), quadrant polarity, the kenoma/pleroma threshold, the Al-Hamid matrix invariants, and the pillar constants.

## Quick start

The toolchain is Lean 4.19.0 (`leanprover/lean4:v4.19.0`). Install [elan](https://github.com/leanprover/elan) if it is not already on your `PATH`, then build either project:

```
export PATH="$HOME/.elan/bin:$PATH"
cd gnostic-arabic-lean && lake build
cd ../crux-lean && lake build
```

Each `lakefile.lean` turns off `autoImplicit` and `relaxedAutoImplicit`. `lake-manifest.json` lists no packages. `lake build` compiles the default library in that folder (`GnosticArabic` or `Crux`).

## Usage

Import the root module of the project you want:

```lean
import Crux
```

```lean
import GnosticArabic
```

`import Crux` brings in every CRUX module listed above. `import GnosticArabic` brings in `GnosticArabic.AbjadMatrix`. Definitions live in the `Crux` and `GnosticArabic` namespaces.

## CRUX compiler (Zig)

`zig/` is a standalone CRUX compiler written in Zig 0.17.1. It lexes and parses the Russian syntax, lowers it to the recursive state IR, and emits SMT-LIB 2 for Z3, Lean 4 source, the SAS abstract-interpretation report, CUDA C for the SAS analysis, and proof-carrying certificates. When `z3` is on `PATH`, `check`, `run` and `cert` call it; `--lean` also runs `lean` on goals Z3 leaves open.

```
cd zig
zig build                 # zig-out/bin/crux, zig-out/lib/libcrux.a, zig-out/include/crux.h
zig build test
./zig-out/bin/crux check examples/basics.crux
```

| Command | Output |
|---|---|
| `crux lex FILE` | tokens with `line:column` |
| `crux parse FILE` | AST of every item |
| `crux lower FILE` | lowered state, formula and backend |
| `crux emit-smt FILE` | SMT-LIB 2 (32-bit bit-vectors) |
| `crux emit-lean FILE` | Lean 4 file, core Lean only |
| `crux emit-sas FILE` | SAS fixpoint report per goal |
| `crux emit-cuda FILE` | CUDA C running the SAS analysis; also builds as plain C++ |
| `crux cert FILE` | certificates as JSON, with SHA-256 of the SMT, Lean and CUDA artifacts |
| `crux check FILE` | OMEGA verdict per goal: Z3, then Lean, then SAS |
| `crux run FILE` | full pipeline report per goal |
| `crux solve FILE` | finite-domain search over integer constraints |
| `crux macros` | OMEGA and Lean tactic macro tables |
| `crux abjad letters \| value WORD... \| digit-root N \| wafq \| constants \| quadrant STEP` | the Abjad matrix |

Options: `-o PATH`, `--no-z3`, `--lean[=TOOLCHAIN]`, `--timeout MS`. Parse errors are reported as `FILE:line:col: error: message`.

A source file is a list of items separated by `;`, each optionally named with `theorem NAME :`, `lemma NAME :` or `example :`:

```
theorem bound_five : сила(S0[x := 2 + 3], x = 5);
theorem double : для_всех n : Int. n * 2 = n + n
```

```
$ ./zig-out/bin/crux emit-smt examples/states.crux
; SMT-LIB 2 generated by `crux emit-smt examples/states.crux`
; goal bound_five
(set-logic QF_BV)
(set-option :produce-models true)
(declare-const x (_ BitVec 32))
(assert (= x (_ bv5 32)))
...
$ ./zig-out/bin/crux solve examples/solve.crux
split_ten: SAT x = 3, y = 7
coins: SAT a = 6, b = 5
impossible: UNSAT
```

The keywords are `равенство`, `импликация`, `конъюнкция`, `дизъюнкция`, `отрицание`, `для_всех`, `существует`, `рекурсия`, `состояние`, `сила`, `омега` and `доказательство`, alongside the operators `∧ ∨ ¬ → ↔ ∀ ∃ μ ν ≤ ≥ ≠`. More programs are in `zig/examples/`.

## Nim bindings

`nim/` wraps `libcrux`, the C ABI the Zig build installs (`zig/include/crux.h`), for Nim 2.4.2.

```
cd zig && zig build
cd ../nim
nim c -r tests/test_crux.nim      # or: nimble test
nim c crux_cli.nim
./crux_cli emit-lean ../zig/examples/basics.crux
```

```nim
import crux

echo emitSmt("равенство(x + 1, 1 + x)")
echo abjadValue("الله")            # 66
try:
  discard parse("сила(")
except CruxError as e:
  echo e.msg                       # <input>:1:6: error: ...
```

The module exposes `lex`, `parse`, `lower`, `emitSmt`, `emitLean`, `emitSas`, `emitCuda`, `cert`, `check`, `run`, `solve`, `abjadValue`, `digitRoot`, `letterValue`, `wafqAllahVerify` and `wafqAllahSums`. `-d:cruxPrefix=PATH` points it at another `zig-out`.

## Layout

```
crux-lean/
  Crux.lean                 root imports
  Crux/                     AST, backends, OMEGA, PCC, parser, pipeline
  lakefile.lean
  lean-toolchain            leanprover/lean4:v4.19.0
  lake-manifest.json
  README.md
  STATUS.md
gnostic-arabic-lean/
  GnosticArabic.lean        root import
  GnosticArabic/
    AbjadMatrix.lean
  lakefile.lean
  lean-toolchain            leanprover/lean4:v4.19.0
  lake-manifest.json
  README.md
  STATUS.md
zig/
  build.zig, build.zig.zon  Zig 0.17.1 build: crux executable, libcrux, tests
  src/                      lexer, parser, IR, Z3/Lean/SAS/CUDA backends, OMEGA, PCC, Abjad, CLI, C ABI
  include/crux.h            C header for libcrux
  examples/                 .crux programs
nim/
  crux.nim                  bindings over libcrux
  crux_cli.nim              CLI over the bindings
  tests/test_crux.nim
  crux.nimble
LICENSE
LICENSE-AGPL-3.0
LICENSE-SnapKitty-Opaque-1.0
```

## Requirements

- Lean 4.19.0, installed through elan from the `lean-toolchain` file in each project folder.
- No Mathlib, no Lake packages, and no other language toolchains to compile the libraries.
- Zig 0.17.1 for the compiler in `zig/`; Nim 2.4.2 for the bindings in `nim/`. Z3 is optional.

## License

Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab.

This project is dual licensed. You may use, modify and distribute it under the terms of either the GNU Affero General Public License, version 3 only (see [LICENSE-AGPL-3.0](LICENSE-AGPL-3.0)), or the SnapKitty Opaque License 1.0 (see [LICENSE-SnapKitty-Opaque-1.0](LICENSE-SnapKitty-Opaque-1.0)), at your option.

SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
