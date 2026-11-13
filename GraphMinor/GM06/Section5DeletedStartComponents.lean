module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5VertexSeparation
import GraphMinor.GM06.Section5Components
import GraphMinor.GM06.Section5NoReduction2
import GraphMinor.GM06.Section3Basic
import GraphMinor.GM11.Walks

/-!
# Components left after removing an initial vertex

For the boundary-contact argument of VI (5.1), page 129, remove one
initial vertex. A component missing every linkage vertex is attached
to the rest of G only at that initial vertex. The attachment
separation keeps the whole linkage on its other side, so Reduction 2
would remove the component. Thus every remaining component meets the
linkage away from the removed initial vertex.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

/-- After deleting an initial vertex, every graph component still
contains a linkage vertex if Reduction 2 is unavailable. This is the
branch exclusion used in VI (5.1), page 129. -/
theorem deleted_start_component_meets_linkage_of_no_reduction2
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁) (i : Fin k)
    {K : Graph ClosedCylinder (Set ClosedCylinder)}
    (hK : IsGraphComponent K (G.toGraph.induce (G.V \ {cylinderM1Point k i}))) :
    ∃ j : Fin k, ∃ x ∈ Graph.vertexSet K, x ∈ (L.pathDrawing j).V := by
  classical
  by_contra hnone
  have hX : Graph.vertexSet K ⊆ G.V := by
    intro x hx
    have hh := hK.1.vertexSet_mono hx
    change x ∈ G.V \ {cylinderM1Point k i} at hh
    exact hh.1
  have hport : ∀ e a b, G.toGraph.IsLink e a b → a ∈ Graph.vertexSet K →
      b ∈ Graph.vertexSet K ∨ b = cylinderM1Point k i := by
    intro e a b hl ha
    by_cases hb : b = cylinderM1Point k i
    · exact Or.inr hb
    · apply Or.inl
      have haD : a ∈ G.V \ {cylinderM1Point k i} := hK.1.vertexSet_mono ha
      have hbD : b ∈ G.V \ {cylinderM1Point k i} :=
        ⟨hl.right_mem, fun hh => hb (mem_singleton_iff.mp hh)⟩
      have hlD : (G.toGraph.induce (G.V \ {cylinderM1Point k i})).IsLink e a b :=
        ⟨hl, haD, hbD⟩
      exact (hK.mem_iff_of_isLink hlD).mp ha
  obtain ⟨H, hsep, hoverlap⟩ := exists_separation_of_set_attached_at_vertex G hX hport
  have hpaths : ∀ j : Fin k,
      (L.pathDrawing j).IsSubdrawing (induceDrawing G (G.V \ Graph.vertexSet K)) := by
    intro j
    apply subdrawing_induce_of_vertices_subset (L.isSubdrawing j).1 sdiff_subset
    intro x hx
    refine ⟨(L.isSubdrawing j).1.1 hx, ?_⟩
    intro hxK
    exact hnone ⟨j, x, hxK, hx⟩
  obtain ⟨x, hx⟩ := hK.2.1.1
  have hne : (induceDrawing G (G.V \ Graph.vertexSet K)).toGraph ≠ G.toGraph := by
    intro heq
    have hxF : x ∈ Graph.vertexSet (induceDrawing G (G.V \ Graph.vertexSet K)).toGraph := by
      rw [heq]
      exact hX hx
    change x ∈ (induceDrawing G (G.V \ Graph.vertexSet K)).V at hxF
    rw [induceDrawing_V G sdiff_subset] at hxF
    exact hxF.2 hx
  obtain ⟨L₁, hG₁, hRed⟩ := exists_reduction2_of_linkage_separation L hG i hsep hoverlap hne hpaths
  exact hno _ L₁ hG₁ hRed

/-- The absence of all Section 5 reductions implies the corresponding
conclusion obtained by excluding Reduction 2 alone. -/
theorem deleted_start_component_meets_linkage
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    {K : Graph ClosedCylinder (Set ClosedCylinder)}
    (hK : IsGraphComponent K (G.toGraph.induce (G.V \ {cylinderM1Point k i}))) :
    ∃ j : Fin k, ∃ x ∈ Graph.vertexSet K, x ∈ (L.pathDrawing j).V := by
  exact deleted_start_component_meets_linkage_of_no_reduction2 L hG
    (fun G₁ L₁ hG₁ hRed => hno ⟨G₁, L₁, hG₁, Or.inr (Or.inl hRed)⟩) i hK

end GraphMinor.GM06
