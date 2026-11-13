module

public import GraphMinor.GM06.Alg34GapInducedRep
public import GraphMinor.GM06.Alg34GapDivisionRestriction
public import GraphMinor.Compute.GM06Alg34GapComponentData
import GraphMinor.GM06.Alg34BranchCorrect
import GraphMinor.GM06.Section3Basic

/-!
# Correct augmented component branch inputs

Every selected component has the full induced gap interpretation. Its
proper drawing is connected, and restricting the old boundary division
preserves the division and boundary-cover conditions. The existing
VI (3.3)(iv) proof then transfers to the augmented canonical component
list by reading each entry's base drawing.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- Materializing any supplied component label gives a connected proper
represented component with a valid division covering its boundary vertices. -/
theorem componentGapData_valid (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hproper : G.IsProper) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ = G.V ∩ bd S) (a : Fin X.drawing.n) :
    let vs := X.drawing.componentVertices a
    let G' := induceDrawing G (h.drawing.vertexImage vs)
    let Δ' := h.drawing.inducedDivision vs
    Nonempty (GM06GapInputRep (X.componentGapData a) G' Δ') ∧
      G'.IsProper ∧ IsDivision Δ' ∧ divisionUnion Δ' = G'.V ∩ bd S ∧
      IsGraphConnected G'.toGraph := by
  dsimp only
  refine ⟨h.inducedGapInput_rep hS hproper _,
    induceDrawing_isProper G hproper (h.drawing.vertexImage_subset _),
    h.drawing.inducedDivision_isDivision _ hD, h.drawing.inducedDivision_boundary _ hbd, ?_⟩
  rw [h.drawing.component_vertexImage a, induceDrawing_toGraph_of_component G
    (isGraphComponent_compOf (h.drawing.vertex a).property)]
  exact (isGraphComponent_compOf (h.drawing.vertex a).property).2.1

/-- The augmented component list has exactly the conjunction of answers
prescribed by the proved VI (3.3)(iv) reduction. -/
theorem componentGapInputs_feasible_iff (h : GM06GapInputRep X G Δ)
    (hs : X.drawing.hasSplitBlock = false) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ = G.V ∩ bd S) (hk : 2 ≤ X.drawing.componentRoots.length) :
    IsFeasible X.drawing.graph X.drawing.divisionSet ↔
      ∀ Y ∈ X.componentGapInputs, IsFeasible Y.drawing.graph Y.drawing.divisionSet := by
  have hb := h.drawing.componentInputs_list_feasible_iff hs hD hbd hk
  rw [← X.componentGapInputs_drawings] at hb
  constructor
  · intro hf Y hY
    exact hb.mp hf Y.drawing (List.mem_map.mpr ⟨Y, hY, rfl⟩)
  · intro hf
    apply hb.mpr
    intro y hy
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hy
    exact hf Y hY

end GraphMinor.Compute.GM06GapInputRep
