module

public import GraphMinor.GM06.Alg34GapInducedRep
public import GraphMinor.Compute.GM06Alg34GapInteriorData
import GraphMinor.GM06.Alg34InteriorComponentCorrect
import GraphMinor.GM06.Alg34SingletonExhaustCorrect

/-!
# Correct augmented deletion of a boundary-disjoint component

Apply the full retained-gap interpretation to the selected induced
subdrawing. The existing component-image and division-restriction
lemmas identify it with the deletion in VI (3.3)(ii). The division
stays fixed, the drawing stays proper, and feasibility is preserved.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- The augmented component payload represents exactly the actual
component deletion and unchanged division in VI (3.3)(ii). -/
theorem interiorGapData_rep (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hproper : G.IsProper) (a : Fin X.drawing.n)
    (ha : X.drawing.isInteriorComponent a = true) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ ⊆ G.V ∩ bd S) :
    Nonempty (GM06GapInputRep (X.interiorGapData a)
      (induceDrawing G (G.V \ (GM06.compOf G.toGraph (h.drawing.vertex a).val).vertexSet)) Δ) := by
  have hr := h.inducedGapInput_rep hS hproper (X.drawing.interiorComponentSurvivors a)
  rw [h.drawing.interiorComponent_vertexImage a,
    h.drawing.interiorComponent_inducedDivision a ha hD hbd] at hr
  exact hr

/-- A selected interior component's augmented deletion retains a proper
represented drawing, the same boundary division, and the same finite
feasibility answer by the proved VI (3.3)(ii) equivalence. -/
theorem interiorGapData_correct (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hproper : G.IsProper) (a : Fin X.drawing.n)
    (ha : X.drawing.isInteriorComponent a = true) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ ⊆ G.V ∩ bd S) :
    ∃ G' : Drawing S, Nonempty (GM06GapInputRep (X.interiorGapData a) G' Δ) ∧
      G'.IsProper ∧ divisionUnion Δ ⊆ G'.V ∩ bd S ∧
      (IsFeasible X.drawing.graph X.drawing.divisionSet ↔
        IsFeasible (X.interiorGapData a).drawing.graph (X.interiorGapData a).drawing.divisionSet) := by
  obtain ⟨hr⟩ := h.interiorGapData_rep hS hproper a ha hD hbd
  exact ⟨_, ⟨hr⟩, induceDrawing_isProper G hproper sdiff_subset,
    fun p hp => ⟨hr.drawing.divisionUnion_subset hp, (hbd hp).2⟩,
    h.drawing.interiorComponentData_feasible_iff a ha hD hbd⟩

end GraphMinor.Compute.GM06GapInputRep
