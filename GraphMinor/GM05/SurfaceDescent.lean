module

public import GraphMinor.GM05.GenusListOrder
public import GraphMinor.GM05.SurfaceGenus
public import GraphMinor.GM19.Defs2

/-!
# No infinite descent of surface genera

Graph Minors V, (8.9), orders orientable surfaces by their nonincreasing
component-genus lists, with proper prefixes incomparable. Apply the proved
well-founded order on such lists to the lists of the actual surface
components. Surfaces, orientability, and handle models are those already
used by the library.
-/

public section

namespace GraphMinor.GM05

open Surface GM19

universe u v

/-- The strict surface-genus comparison of Graph Minors V, page 112.
The comparison is at the first unequal component genus and does not
compare a list to a proper prefix of itself. -/
@[expose] def SurfaceGenusLT {S : Type u} [TopologicalSpace S]
    {T : Type v} [TopologicalSpace T] (hS : IsClosedSurface S) (hT : IsClosedSurface T) : Prop :=
  GenusListLT (surfaceGenusList S hS) (surfaceGenusList T hT)

/-- Graph Minors V, (8.9), page 112:
"There is no infinite sequence $\Sigma_1, \Sigma_2, \dots$ of orientable surfaces with $g(\Sigma_{i+1}) < g(\Sigma_i)$ ($i = 1, 2, \dots$)."
The proof uses well-foundedness of the multiset order on component genera. -/
theorem theorem_8_9_proof (S : ℕ → Type u) (τ : ∀ n,TopologicalSpace (S n))
    (hS : ∀ n,@IsClosedSurface (S n) (τ n))
    (_hO : ∀ n,@IsOrientableSurface (S n) (τ n)) :
    ¬∀ n,@SurfaceGenusLT (S (n+1)) (τ (n+1)) (S n) (τ n) (hS (n+1)) (hS n) := by
  exact genusList_no_descending (fun n ↦ @surfaceGenusList (S n) (τ n) (hS n))
    (fun n ↦ @surfaceGenusList_sorted (S n) (τ n) (hS n))

end GraphMinor.GM05
