module

public import GraphMinor.GM06.Alg34LoopInstance
public import GraphMinor.GM06.Alg34InducedLoopBounds
public import GraphMinor.GM06.Alg34GapComponentsCorrect
import GraphMinor.GM06.Alg34InteriorComponentCorrect

/-!
# Intended loop instances under deletion and component restriction

The proved induced representation supplies the new drawing and division.
Its restricted division remains cross-free and covers exactly the new
boundary. The fixed numerical bounds are inherited from the induced
bounds. Interior deletion also preserves the answer and strictly lowers
work, while component restriction prepares each independent child.
-/

public section
namespace GraphMinor.Compute

open Set Surface GM06
universe u

/-- Every materialized component retains the geometric and numerical loop conditions. -/
theorem gm06LoopInstance_component {X : GM06GapInput} (hX : gm06LoopInstance.{u} X)
    {M E Q : ℕ} (hB : gm06LoopBounds M E Q X) (a : Fin X.drawing.n) :
    gm06LoopInstance.{u} (X.componentGapData a) ∧ gm06LoopBounds M E Q (X.componentGapData a) := by
  obtain ⟨I, ⟨h⟩, hCF⟩ := hX
  haveI : T2Space I.S := t2Space_of_isClosedDiscSpace I.hDisc
  obtain ⟨hr, hp, hD, hb, _⟩ := h.componentGapData_valid I.hDisc I.hProper I.hΔ I.hΔ_eq a
  have hcf := h.drawing.inducedDivision_crossFree (X.drawing.componentVertices a) hCF
  obtain ⟨hnr, he, hcell, hreg, hcuff, hdiv⟩ := h.inducedGapInput_loop_bounds I.hDisc I.hProper Q
    hB.2.2.1 hB.2.2.2.2.1 hB.2.2.2.2.2 (X.drawing.componentVertices a)
  let I' : DiscDivInstance.{u} := {
    S := I.S, hDisc := I.hDisc,
    G := induceDrawing I.G (h.drawing.vertexImage (X.drawing.componentVertices a)), hProper := hp,
    Δ := h.drawing.inducedDivision (X.drawing.componentVertices a), hΔ := hD, hΔ_eq := hb }
  exact ⟨⟨I', hr, hcf⟩,
    ⟨hnr.trans hB.1, he.trans hB.2.1, hcell.trans hB.2.2.1, hreg, hcuff, hdiv⟩⟩

/-- Deleting a selected interior component retains the loop conditions,
preserves its answer and strictly lowers its work charge. -/
theorem gm06LoopInstance_interior {X : GM06GapInput} (hX : gm06LoopInstance.{u} X)
    {M E Q : ℕ} (hB : gm06LoopBounds M E Q X) (a : Fin X.drawing.n)
    (ha : X.drawing.isInteriorComponent a = true) :
    gm06LoopInstance.{u} (X.interiorGapData a) ∧ gm06LoopBounds M E Q (X.interiorGapData a) ∧
      (IsFeasible X.drawing.graph X.drawing.divisionSet ↔
        IsFeasible (X.interiorGapData a).drawing.graph (X.interiorGapData a).drawing.divisionSet) ∧
      (X.interiorGapData a).drawing.workWeight (M + 1) < X.drawing.workWeight (M + 1) := by
  obtain ⟨I, ⟨h⟩, hCF⟩ := hX
  haveI : T2Space I.S := t2Space_of_isClosedDiscSpace I.hDisc
  have hr := h.interiorGapData_rep I.hDisc I.hProper a ha I.hΔ I.hΔ_eq.subset
  have hp : (induceDrawing I.G
      (I.G.V \ (GM06.compOf I.G.toGraph (h.drawing.vertex a).val).vertexSet)).IsProper :=
    induceDrawing_isProper I.G I.hProper sdiff_subset
  have hb := h.interiorGapData_boundary a ha I.hΔ I.hΔ_eq
  obtain ⟨hnr, he, hcell, hreg, hcuff, hdiv⟩ := h.inducedGapInput_loop_bounds I.hDisc I.hProper Q
    hB.2.2.1 hB.2.2.2.2.1 hB.2.2.2.2.2 (X.drawing.interiorComponentSurvivors a)
  let I' : DiscDivInstance.{u} := {
    S := I.S, hDisc := I.hDisc,
    G := induceDrawing I.G (I.G.V \ (GM06.compOf I.G.toGraph (h.drawing.vertex a).val).vertexSet),
    hProper := hp, Δ := I.Δ, hΔ := I.hΔ, hΔ_eq := hb }
  exact ⟨⟨I', hr, hCF⟩,
    ⟨hnr.trans hB.1, he.trans hB.2.1, hcell.trans hB.2.2.1, hreg, hcuff, hdiv⟩,
    h.drawing.interiorComponentData_feasible_iff a ha I.hΔ I.hΔ_eq.subset,
    gm06InteriorComponentData_workWeight_lt (M + 1) X.drawing a⟩

end GraphMinor.Compute
