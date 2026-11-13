module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5DeletedStartComponents
import GraphMinor.GM06.Section5Components
import GraphMinor.GM06.Section3Basic
import GraphMinor.GM11.Walks

/-!
# Reaching the sole linkage after deleting its initial vertex

Without Reduction 2, every component left after deleting the initial
vertex meets the linkage. A walk inside that component therefore
reaches the linkage without using the deleted vertex. This supplies
the original walk lifted into the punctured cut drawing in the
one-path proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11

/-- A vertex other than the initial vertex can reach the sole linkage
by a graph walk which avoids that initial vertex, when Reduction 2 does not apply. -/
theorem exists_original_walk_to_linkage_avoiding_initial_of_no_reduction2
    {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G)
    (hno2 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction2Step 1 G L H M)
    {x : ClosedCylinder} (hx : x ∈ G.V) (hxs : x ≠ cylinderM1Point 1 0) :
    ∃ v ∈ (L.pathDrawing 0).V, ∃ W : GraphWalk G.toGraph x v,
      ∀ z ∈ W.support, z ≠ cylinderM1Point 1 0 := by
  let s := cylinderM1Point 1 0
  let H := induceDrawing G (G.V \ {s})
  have hHG : H.IsSubdrawing G := induceDrawing_isSubdrawing G sdiff_subset
  have hHV : H.V = G.V \ {s} := induceDrawing_V G sdiff_subset
  have hxH : x ∈ H.V := hHV.symm ▸ ⟨hx, hxs⟩
  let K := compOf H.toGraph x
  have hK : IsGraphComponent K H.toGraph := isGraphComponent_compOf hxH
  have hKi : IsGraphComponent K (G.toGraph.induce (G.V \ {s})) := by
    rw [← induceDrawing_toGraph_eq_induce G sdiff_subset]
    exact hK
  obtain ⟨j, v, hvK, hvP⟩ := deleted_start_component_meets_linkage_of_no_reduction2 L hG hno2 0 hKi
  have hj : j = 0 := Subsingleton.elim _ _
  rw [hj] at hvP
  have hxK : x ∈ Graph.vertexSet K := self_mem_reachSet hxH
  obtain ⟨W⟩ := hK.2.1.2 x hxK v hvK
  have hle : H.toGraph ≤ G.toGraph :=
    { vertexSet_mono := hHG.1
      isLink_mono := fun _ _ _ hl => (hHG.isLink_iff hl.1).mp hl }
  let hKG := hK.1.trans hle
  refine ⟨v, hvP, W.mono hKG, ?_⟩
  intro z hz
  rw [GraphWalk.support_mono hKG W] at hz
  have hzH : z ∈ H.V := hK.1.vertexSet_mono (W.mem_vertexSet_of_mem_support hz)
  rw [hHV] at hzH
  exact hzH.2


/-- A vertex other than the initial vertex can reach the sole linkage
by a graph walk which avoids that initial vertex, when no reduction applies. -/
theorem exists_original_walk_to_linkage_avoiding_initial
    {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hno : ¬ Section5AnyReductionApplies 1 G L)
    {x : ClosedCylinder} (hx : x ∈ G.V) (hxs : x ≠ cylinderM1Point 1 0) :
    ∃ v ∈ (L.pathDrawing 0).V, ∃ W : GraphWalk G.toGraph x v,
      ∀ z ∈ W.support, z ≠ cylinderM1Point 1 0 := by
  exact exists_original_walk_to_linkage_avoiding_initial_of_no_reduction2 L hG
    (fun H M hH h2 => hno ⟨H, M, hH, Or.inr (Or.inl h2)⟩) hx hxs

end GraphMinor.GM06
