module

public import GraphMinor.GM07.Defs
public import GraphMinor.GM19.CutMap
import GraphMinor.GM07.Section2Base
import GraphMinor.GM07.MinimalNet
import GraphMinor.GM07.PullForest

/-!
# Lifting the first edges of paths to the net disc

In VII (4.6), page 225, each path edge at a boundary vertex has a lift
incident with a single point of the fibre. The net surjection is a cutting
map along its seam, and an edge meets that seam only at its ends. We lift
the closed edge as a line, retaining its injectivity and its chosen ends.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

universe u

/-- The surjection of a net is a cutting map along its seam. -/
theorem Net.isCutMap_seam {S : Type u} [TopologicalSpace S] (N : Net S) :
    GM19.IsCutMap N.φ N.seamU := by
  refine ⟨N.quotientMap_φ.continuous, N.quotientMap_φ.surjective,
    ?_, N.finite_fiber, ?_⟩
  · intro x hx y _ hxy
    have hxbd : x ∉ bd N.D := by
      rw [← N.preimage_seamU]
      exact hx
    exact N.interior_inj x hxbd y hxy
  · rw [N.preimage_seamU]

/-- The lift of a non-loop edge in the normal net, as used for the first
edges of the paths in VII (4.6), page 225. -/
theorem Net.exists_lift_closed_normal_edge {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {G J : Drawing S}
    (hJ : N.IsSeamGraphFor J) (hnorm : G.IsNormal J.U)
    {e : Set S} (he : e ∈ G.E) {a b : S} (hab : a ≠ b)
    (hends : closure e ∩ G.V = {a, b}) (hline : IsLineWithEnds (closure e) a b) :
    ∃ (L : Set N.D) (a' b' : N.D), IsLineWithEnds L a' b' ∧
      N.φ a' = a ∧ N.φ b' = b ∧ N.φ '' L = closure e ∧
      InjOn N.φ L ∧ ∀ x, N.φ x ∈ closure e \ {a, b} → x ∈ L := by
  have : CompactSpace N.D := N.isSurface_D.1
  have : T2Space N.D := N.isSurface_D.2.1
  have : T2Space S := hS.2.1
  have hmeet : closure e ∩ J.U ⊆ {a, b} := by
    intro x hx
    rw [← hends]
    exact ⟨hx.1, hnorm ⟨hx.2, G.closure_subset_U he hx.1⟩⟩
  have hcut : GM19.IsCutMap N.φ J.U := hJ.2.1 ▸ N.isCutMap_seam
  exact exists_lift_closed_edge hcut J.isClosed_U hab hline hmeet

end GraphMinor.GM07
