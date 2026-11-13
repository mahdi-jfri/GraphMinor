module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM11.ArcDrawings
import GraphMinor.GM11.RadialBasics
import Mathlib.Tactic

/-!
# Cuff arcs for the input drawing before linkage search

The rotation input of VI (5.11), page 134, must also describe the
cuff directions used by (5.7). Adjoin the two cuffs to the given
proper cylinder drawing, without assuming a linkage exists. The
prescribed boundary vertices already meet each cuff. Draw its arcs
between those vertices and glue along the common vertex sets.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11

/-- Every intended input drawing has a drawing with the cuff arcs
adjoined and exactly the same vertices, independently of feasibility. -/
theorem alg511_exists_drawing_with_cuffs {k : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) :
    ∃ (F D₁ D₂ : Drawing ClosedCylinder), G.IsSubdrawing F ∧
      F.U = G.U ∪ bd ClosedCylinder ∧ F.V = G.V ∧
      D₁.U = cylinderCuff1 ∧ D₂.U = cylinderCuff2 ∧
      D₁.V = G.V ∩ cylinderCuff1 ∧ D₂.V = G.V ∩ cylinderCuff2 ∧
      F.E = G.E ∪ (D₁.E ∪ D₂.E) := by
  let i : Fin k := ⟨0, hG.1⟩
  have hsV : cylinderM1Point k i ∈ G.V := by
    have hs : cylinderM1Point k i ∈ G.V ∩ bd ClosedCylinder := by
      rw [hG.2.2]
      exact Or.inl ⟨i, rfl⟩
    exact hs.1
  have htV : cylinderM2Point k i ∈ G.V := by
    have ht : cylinderM2Point k i ∈ G.V ∩ bd ClosedCylinder := by
      rw [hG.2.2]
      exact Or.inr ⟨i, rfl⟩
    exact ht.1
  obtain ⟨D₁, hU₁, hV₁⟩ := exists_drawing_on_oArc isOArc_cylinderCuff1
    (G.finite_V.inter_of_left cylinderCuff1) ⟨cylinderM1Point k i, hsV, rfl⟩ inter_subset_right
  obtain ⟨D₂, hU₂, hV₂⟩ := exists_drawing_on_oArc isOArc_cylinderCuff2
    (G.finite_V.inter_of_left cylinderCuff2) ⟨cylinderM2Point k i, htV, rfl⟩ inter_subset_right
  have hmeet : D₁.U ∩ D₂.U ⊆ D₁.V ∩ D₂.V := by
    rw [hU₁, hU₂]
    intro x hx
    exact False.elim (disjoint_left.mp disjoint_cylinderCuffs hx.1 hx.2)
  let B := D₁.glue D₂ hmeet
  have hBU : B.U = bd ClosedCylinder := by
    change D₁.U ∪ D₂.U = _
    rw [hU₁, hU₂, bd_closedCylinder]
  have hBV : B.V = G.V ∩ bd ClosedCylinder := by
    change D₁.V ∪ D₂.V = _
    rw [hV₁, hV₂, bd_closedCylinder, inter_union_distrib_left]
  have hGB : G.U ∩ B.U ⊆ G.V ∩ B.V := by
    rw [hBU, hBV]
    intro x hx
    exact ⟨hG.2.1 ⟨hx.2, hx.1⟩, hG.2.1 ⟨hx.2, hx.1⟩, hx.2⟩
  let F := G.glue B hGB
  refine ⟨F, D₁, D₂, ⟨subset_union_left, ?_⟩, ?_, ?_, hU₁, hU₂, hV₁, hV₂, ?_⟩
  · rw [Drawing.glue_E]
    exact subset_union_left
  · change G.U ∪ B.U = _
    rw [hBU]
  · change G.V ∪ B.V = G.V
    rw [hBV]
    exact union_eq_left.mpr inter_subset_left
  · change (G.glue B hGB).E = _
    rw [Drawing.glue_E]
    change G.E ∪ (D₁.glue D₂ hmeet).E = _
    rw [Drawing.glue_E]

end GraphMinor.GM06
