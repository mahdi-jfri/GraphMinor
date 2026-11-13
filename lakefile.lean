import Lake
open Lake DSL

package «GraphMinor» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "b63f6e8a68d220e3b3bc4f3792bb53650d375f24"

/-- The formalization. `GraphMinor.lean` imports every file under `GraphMinor/`. -/
@[default_target]
lean_lib «GraphMinor»

/-- Checks: the axioms used, the counterexamples to statements of the papers, and the definitions
evaluated on small graphs. -/
@[default_target]
lean_lib «Checks» where
  globs := #[.submodules `Checks]

/-- The three main theorems, stated with `sorry`, for comparator. -/
@[default_target]
lean_lib «Challenge»

/-- The three main theorems, proved. -/
@[default_target]
lean_lib «Solution»

/-- Thomason's bound, stated with `sorry`, for comparator. -/
@[default_target]
lean_lib «ChallengeThomason»

/-- Thomason's bound, proved. -/
@[default_target]
lean_lib «SolutionThomason»
