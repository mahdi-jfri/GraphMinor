module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM08.Section9Boundary
import GraphMinor.GM08.Section7

/-!
# Graph Minors VIII (9.2): bounded tree-width of truncations

If the original drawing has no boundary-linked nest, (9.1) excludes the
same nest from every truncation. The nest-or-tree-width theorem (7.1)
then supplies a bound depending only on the nest parameters.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- Graph Minors VIII, (9.2), page 270: when `r,s ≥ k`, drawings without a
boundary-linked `(r,s)`-nest have all truncations of bounded tree-width.
Properness is the drawing condition of Section 5(iii), page 262. -/
theorem theorem_9_2_proof (k r s : ℕ) (hr : k ≤ r) (hs : k ≤ s) :
    ∃ w : ℕ, ∀ {S : Type u} [TopologicalSpace S] (_hS : IsClosedDisc (univ : Set S))
      (D : Drawing S), D.IsProper → (D.V ∩ discBd (univ : Set S)).ncard = k →
      (∀ N : DrawingNest D univ r s, ¬ IsBoundaryLinkedNest D univ N) →
      ∀ Dstar : Drawing S, IsTruncation D univ Dstar → DrawingTreeWidthLE Dstar w := by
  obtain ⟨w, hw⟩ := theorem_7_1_proof.{u} r s
  refine ⟨w, fun {S} _ hS D hprop hk hno Dstar htrunc => ?_⟩
  have hEmpty : IsEmpty (DrawingNest Dstar univ r s) := by
    refine ⟨fun N => ?_⟩
    have hlinked := theorem_9_1_proof hS hprop htrunc
      (by rwa [hk]) (by rwa [hk]) N
    exact hno (N.ofSubdrawing htrunc.isSubdrawing) hlinked
  exact hw Dstar univ hS (subset_univ _) hEmpty

end GraphMinor.GM08
