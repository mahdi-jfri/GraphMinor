module

public import GraphMinor.GM06.Alg34GapSingletonCorrect
public import GraphMinor.GM06.Alg34GapInteriorCorrect
import GraphMinor.GM06.Alg34GapDivisionRestriction
import GraphMinor.GM06.Alg34InteriorComponentCorrect
import GraphMinor.GM06.Alg34SingletonExhaustCorrect

/-!
# Boundary coverage survives the deletion phases

The union of the restricted division is the old union restricted to
surviving vertices. Apply this identity to each singleton deletion and
to a boundary-disjoint component deletion. Repeating the singleton
step retains full boundary coverage, as required before dualization.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- The singleton division after deletion covers exactly the new boundary vertices. -/
theorem singletonGapData_boundary (h : GM06GapInputRep X G Δ)
    (v : Fin X.drawing.n) (hD : IsDivision Δ)
    (hv : {(h.drawing.vertex v).val} ∈ Δ)
    (hbd : divisionUnion Δ = G.V ∩ bd S) :
    divisionUnion (Δ \ {{(h.drawing.vertex v).val}}) =
      (induceDrawing G (G.V \ {(h.drawing.vertex v).val})).V ∩ bd S := by
  have hb := h.drawing.inducedDivision_boundary (X.drawing.singletonSurvivors v) hbd
  rw [h.drawing.singleton_vertexImage v,
    h.drawing.singleton_inducedDivision v hD h.drawing.divisionUnion_subset hv] at hb
  exact hb

/-- Full singleton exhaustion preserves full boundary coverage as well as
properness, division validity and the finite feasibility answer. -/
theorem reduceSingletons_boundary_correct (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hproper : G.IsProper) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ = G.V ∩ bd S) :
    ∃ (G' : Drawing S) (Δ' : Set (Set S)),
      Nonempty (GM06GapInputRep (gm06GapReduceSingletons X) G' Δ') ∧
      G'.IsProper ∧ IsDivision Δ' ∧ divisionUnion Δ' = G'.V ∩ bd S ∧
      (IsFeasible X.drawing.graph X.drawing.divisionSet ↔
        IsFeasible (gm06GapReduceSingletons X).drawing.graph
          (gm06GapReduceSingletons X).drawing.divisionSet) := by
  induction X using gm06GapReduceSingletons.induct generalizing G Δ with
  | case1 X hnone =>
    rw [gm06GapReduceSingletons, hnone]
    exact ⟨G, Δ, ⟨h⟩, hproper, hD, hbd, Iff.rfl⟩
  | case2 X v hfind ih =>
    have hv := h.drawing.findSingleton_mem v hfind
    obtain ⟨hnew⟩ := h.singletonGapData_rep hS hproper v hD hv
    have hD' : IsDivision (Δ \ {{(h.drawing.vertex v).val}}) :=
      ⟨hD.1.subset sdiff_subset, fun δ hδ => hD.2.1 δ hδ.1, hD.2.2.subset sdiff_subset⟩
    have hp' : (induceDrawing G (G.V \ {(h.drawing.vertex v).val})).IsProper :=
      induceDrawing_isProper G hproper sdiff_subset
    have hb' := h.singletonGapData_boundary v hD hv hbd
    obtain ⟨G', Δ', hr, hp, hdiv, hb, hf⟩ := ih hnew hp' hD' hb'
    rw [gm06GapReduceSingletons, hfind]
    exact ⟨G', Δ', hr, hp, hdiv, hb,
      (h.drawing.singletonData_feasible_iff v hD h.drawing.divisionUnion_subset hv).trans hf⟩

/-- Deleting a component disjoint from the boundary retains the same
boundary-covering division. -/
theorem interiorGapData_boundary (h : GM06GapInputRep X G Δ)
    (a : Fin X.drawing.n) (ha : X.drawing.isInteriorComponent a = true)
    (hD : IsDivision Δ) (hbd : divisionUnion Δ = G.V ∩ bd S) :
    divisionUnion Δ =
      (induceDrawing G (G.V \ (GM06.compOf G.toGraph (h.drawing.vertex a).val).vertexSet)).V ∩ bd S := by
  have hb := h.drawing.inducedDivision_boundary (X.drawing.interiorComponentSurvivors a) hbd
  rw [h.drawing.interiorComponent_vertexImage a,
    h.drawing.interiorComponent_inducedDivision a ha hD hbd.subset] at hb
  exact hb

end GraphMinor.Compute.GM06GapInputRep
