import Lake
open Lake DSL

package «GnosticArabic» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib «GnosticArabic» where
  roots := #[`GnosticArabic]
