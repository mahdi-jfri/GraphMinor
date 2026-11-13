module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5RegionBoundaryFirstVertex
import GraphMinor.GM06.Section5FirstContactOriginalGraph
import GraphMinor.GM06.Section5FirstContactPoints
import GraphMinor.GM06.Section5Reduction4Apply
import GraphMinor.GM06.Section5StripBoundary
import GraphMinor.GM06.Section5NextContact
import GraphMinor.GM06.Section5NoReduction1
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# The region path reaches the next linkage path

For VI (5.1), page 129, follow the region boundary to its first new
linkage contact. A return to the old path would give Reduction 4.
The strip closure excludes all paths except the old and the next,
so the contact is on the next path. Reduction 1 at the next initial
vertex excludes that vertex as the terminal contact. This constructs
the path Qᵢ used before the cyclic splicing.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- At a start of larger valency in the unreduced situation of
VI (5.1), the first region-boundary path reaches Pᵢ₊₁ away from its
start, and otherwise avoids the linkage. -/
theorem exists_first_region_path_to_next_linkage
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) ≠ 1) :
    ∃ v ∈ (L.pathDrawing (finSuccCycle i)).V,
      v ≠ cylinderM1Point k (finSuccCycle i) ∧ ∃ Q : Drawing ClosedCylinder,
        IsSubpathOf G Q (cylinderM1Point k i) v ∧
        Q.U ⊆ closure (cylinderRegion k G i) ∧
        Q.U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i, v} ∧
        Q.U ∩ (⋃ j : Fin k, (L.pathDrawing j).U) ⊆ {cylinderM1Point k i, v} := by
  obtain ⟨F, Q, v, hGF, hFU, hFV, hvL, hvs, hQF, hQR, hQcontacts, hC1⟩ :=
    exists_region_boundary_prefix_first_linkage_vertex L hk hG hθ hno i
  have hQG := first_contact_prefix_isSubdrawing_original L hG i hGF hFU hFV hQF.1 hQF.2.2 hQcontacts hC1
  obtain ⟨hmeet, hconf⟩ := first_contact_prefix_point_contact_and_strip L hk hG hθ hno i hval
    hQG hQF.2.2 hQR hQcontacts
  obtain ⟨j, hvj⟩ := mem_iUnion.mp hvL
  have hvr : v ∈ closure (cylinderRegion k G i) :=
    hQR (Q.V_subset_U (isPathDrawing_end_vertices hQF.2.2).2)
  have hsPi : cylinderM1Point k i ∈ (L.pathDrawing i).U :=
    (L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).1
  have hjnoti : j ≠ i := by
    intro hji
    subst j
    apply hno
    apply reduction4_applies_of_first_return_region_path L hk hG hθ hno i hval hvj hvs hQG hQF.2.2 hQR
    · intro y hy
      exact hmeet ⟨hy.1, mem_iUnion.mpr ⟨i, hy.2⟩⟩
    · intro l hli
      apply disjoint_left.mpr
      intro y hyQ hyl
      have hyPi : y ∈ (L.pathDrawing i).U := by
        rcases hmeet ⟨hyQ, mem_iUnion.mpr ⟨l, hyl⟩⟩ with hys | hyv
        · exact hys.symm ▸ hsPi
        · exact (mem_singleton_iff.mp hyv).symm ▸ (L.pathDrawing i).V_subset_U hvj
      exact disjoint_left.mp (L.pairwise_disjoint hli.symm) hyPi hyl
  have hjsucc : j = finSuccCycle i := by
    by_contra hjs
    exact disjoint_left.mp (disjoint_closure_region_path_of_not_neighbour L hG hθ i j hjnoti hjs)
      hvr ((L.pathDrawing j).V_subset_U hvj)
  subst j
  obtain ⟨e, heQ, hve⟩ := exists_terminal_edge hQF.2.2
  have heG := hQG.2 heQ
  have heStrip : e ⊆ cylinderStrip L i := by
    intro x hx
    rcases hconf ((heQ.2.1 hx).1) with hxS | hxEnds
    · exact hxS
    · apply False.elim
      apply (heG.2.1 hx).2
      rcases hxEnds with hxs | hxv
      · exact hxs.symm ▸ (L.isSubdrawing i).1.1 (isPathDrawing_end_vertices (L.isPath i)).1
      · exact (mem_singleton_iff.mp hxv).symm ▸ (L.isSubdrawing (finSuccCycle i)).1.1 hvj
  have hvne : v ≠ cylinderM1Point k (finSuccCycle i) := by
    intro hvstart
    apply hno
    apply reduction1_applies_of_incident_edge_in_strip L hk hG heG (hvstart ▸ hve)
    rw [finPredCycle_finSuccCycle]
    exact heStrip
  exact ⟨v, hvj, hvne, Q, ⟨hQG, hQG.U_subset, hQF.2.2⟩, hQR, hconf, hmeet⟩

end GraphMinor.GM06
