import Lake
open Lake DSL

package Crux where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib Crux where
  roots := #[`Crux]
