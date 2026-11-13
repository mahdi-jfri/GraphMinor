module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section5NoReduction2
import GraphMinor.GM11.Forest
public import GraphMinor.GM11.Section5
import GraphMinor.GM11.Walks

/-!
# An initial vertex has no loop in the unreduced drawing

For the boundary-contact argument of VI (5.1), page 129, a loop at
an initial vertex would be a branch attached only at that vertex.
No linkage path uses a loop. Delete it and put its one-edge drawing
on the other side of a separation. The linkage is retained, so this
would be Reduction 2.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

/-- Deleting a loop at an initial vertex gives a concrete Reduction 2,
with all given paths retained, as used by VI (5.7), page 133. -/
theorem exists_reduction2_of_initial_loop
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) (e : Set ClosedCylinder)
    (hLoop : G.toGraph.IsLink e (cylinderM1Point k i) (cylinderM1Point k i)) :
    ∃ L₁ : CylinderLinkage k (G.deleteEdge e),
      IsCylinderSection5Drawing k (G.deleteEdge e) ∧
      Section5Reduction2Step k G L (G.deleteEdge e) L₁ := by
  have heNot (j : Fin k) : e ∉ (L.pathDrawing j).E := by
    intro heP
    have hl : (L.pathDrawing j).toGraph.IsLink e (cylinderM1Point k i) (cylinderM1Point k i) :=
      ((L.isSubdrawing j).1.isLink_iff heP).mpr hLoop
    let W := GraphWalk.cons hl (GraphWalk.nil hl.right_mem)
    have hW : W.IsSimpleClosed :=
      ⟨List.nodup_singleton _, List.nodup_singleton _⟩
    have hlen := isGraphForest_of_isPathDrawing (L.isPath j) _ W hW
    change (1 : ℕ) = 0 at hlen
    exact Nat.one_ne_zero hlen
  let F := G.deleteEdge e
  let H := G.span {cylinderM1Point k i} {e}
  have hFV : F.V = G.V := GM11.deleteEdge_V G e
  have hFE : F.E = G.E \ {e} := deleteEdge_E G e
  have hFG : F.IsSubdrawing G := ⟨by rw [hFV], by rw [hFE]; exact sdiff_subset⟩
  have hHG : H.IsSubdrawing G := Drawing.span_isSubdrawing G _ _
  have hHE : H.E = {e} := by
    rw [Drawing.span_E]
    exact inter_eq_left.mpr (singleton_subset_iff.mpr hLoop.1)
  have hHV : H.V ⊆ {cylinderM1Point k i} := by
    rw [Drawing.span_V, Drawing.spanV]
    rintro x (hx | hx)
    · exact hx.1
    · obtain ⟨f, ⟨hf, _⟩, hxf⟩ := mem_iUnion₂.mp hx
      have hfe := mem_singleton_iff.mp hf
      subst f
      rw [hLoop.2.2.2] at hxf
      simpa only [mem_insert_iff, mem_singleton_iff, or_self] using hxf
  have hFle : F.toGraph ≤ G.toGraph := {
    vertexSet_mono := hFG.1
    isLink_mono := fun e a b hl => (hFG.isLink_iff hl.1).mp hl }
  have hHle : H.toGraph ≤ G.toGraph := {
    vertexSet_mono := hHG.1
    isLink_mono := fun e a b hl => (hHG.isLink_iff hl.1).mp hl }
  have hsep : IsGraphSeparation G.toGraph F.toGraph H.toGraph := by
    refine ⟨hFle, hHle, ?_, ?_, ?_⟩
    · change F.V ∪ H.V = G.V
      rw [hFV, union_eq_left.mpr hHG.1]
    · change F.E ∪ H.E = G.E
      rw [hFE, hHE]
      exact sdiff_union_of_subset (singleton_subset_iff.mpr hLoop.1)
    · change Disjoint F.E H.E
      rw [hFE, hHE]
      exact disjoint_left.mpr fun f hfF hfH => hfF.2 hfH
  have hpaths : ∀ j, (L.pathDrawing j).IsSubdrawing F := by
    intro j
    constructor
    · rw [hFV]
      exact (L.isSubdrawing j).1.1
    · rw [hFE]
      intro f hf
      refine ⟨(L.isSubdrawing j).1.2 hf, ?_⟩
      intro heq
      have hfe := mem_singleton_iff.mp heq
      exact heNot j (hfe ▸ hf)
  have hne : F.toGraph ≠ G.toGraph := by
    intro heq
    have heF : e ∈ Graph.edgeSet F.toGraph := by
      rw [heq]
      exact hLoop.1
    change e ∈ F.E at heF
    rw [hFE] at heF
    exact heF.2 (mem_singleton e)
  exact exists_reduction2_of_linkage_separation L hG i hsep
    (fun _ hx => hHV hx.2) hne hpaths

/-- A loop at an initial vertex permits Reduction 2, so it is absent
in the unreduced situation of VI (5.1), page 129. -/
theorem not_isLoop_at_initial_of_no_reduction2
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁) (i : Fin k) (e : Set ClosedCylinder) :
    ¬ G.toGraph.IsLink e (cylinderM1Point k i) (cylinderM1Point k i) := by
  intro hLoop
  obtain ⟨L₁, hG₁, hRed⟩ := exists_reduction2_of_initial_loop L hG i e hLoop
  exact hno _ L₁ hG₁ hRed

/-- The absence of all Section 5 reductions implies the corresponding
conclusion obtained by excluding Reduction 2 alone. -/
theorem not_isLoop_at_initial_of_no_section5_reduction
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k) (e : Set ClosedCylinder) :
    ¬ G.toGraph.IsLink e (cylinderM1Point k i) (cylinderM1Point k i) := by
  exact not_isLoop_at_initial_of_no_reduction2 L hG
    (fun G₁ L₁ hG₁ hRed => hno ⟨G₁, L₁, hG₁, Or.inr (Or.inl hRed)⟩) i e

end GraphMinor.GM06
