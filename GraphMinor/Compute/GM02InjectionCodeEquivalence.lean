module

public import GraphMinor.Compute.GM02InjectionEquivalence
public import GraphMinor.Compute.GM02InjectionCodes

/-!
# Completeness of the coded injection search

Every injection is represented by a valid candidate code. Combining
this with the injection-search equivalence gives exactly the condition
needed to close the outer counting loop: an isomorphic topologically
contained copy exists exactly when some valid coded test succeeds.
-/

public section
namespace GraphMinor.Compute
open Graph GraphMinor.GM02

/-- Scanning all valid codes is equivalent to finding an isomorphic contained copy of the fixed pattern. -/
theorem gm02_exists_injectionCode_iff (G H : GM02EdgeListInput) :
    (∃ L : Graph ℕ ℕ, TopologicallyContains G.graph L ∧ Nonempty (Iso H.graph L)) ↔
      ∃ code < (G.n + 1) ^ H.n, ∃ hv : gm02InjectionCodeValid G.n H.n code,
        TopologicallyContains G.graph
          (gm02InjectedPattern G H (gm02InjectionOfCode G.n H.n code hv)).H := by
  rw [gm02_exists_injectedPattern_iff]
  constructor
  · rintro ⟨f, ht⟩
    obtain ⟨code, hc, hv, hf⟩ := exists_gm02InjectionCode G.n H.n f
    exact ⟨code, hc, hv, hf.symm ▸ ht⟩
  · rintro ⟨code, _, hv, ht⟩
    exact ⟨gm02InjectionOfCode G.n H.n code hv, ht⟩

end GraphMinor.Compute
