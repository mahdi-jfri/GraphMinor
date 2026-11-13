module

public import GraphMinor.GM06.Alg34GapInducedRep
public import GraphMinor.Compute.GM06Alg34GapSingletonData
import GraphMinor.GM06.Alg34SingletonExhaustCorrect

/-!
# Singleton exhaustion preserves the augmented geometric input

The retained-gap interpretation survives every induced deletion. For a
found singleton, the existing vertex and division restriction equalities
identify that deletion with VI (3.3)(i). Repeat along the finite augmented
recursion, keeping a proper drawing and a valid division at every step.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- The augmented singleton payload represents exactly the drawing and
division obtained in VI (3.3)(i), including the updated gap incidence. -/
theorem singletonGapData_rep (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hproper : G.IsProper) (v : Fin X.drawing.n)
    (hD : IsDivision Δ) (hv : {(h.drawing.vertex v).val} ∈ Δ) :
    Nonempty (GM06GapInputRep (X.singletonGapData v)
      (induceDrawing G (G.V \ {(h.drawing.vertex v).val}))
      (Δ \ {{(h.drawing.vertex v).val}})) := by
  have hr := h.inducedGapInput_rep hS hproper (X.drawing.singletonSurvivors v)
  rw [h.drawing.singleton_vertexImage v,
    h.drawing.singleton_inducedDivision v hD h.drawing.divisionUnion_subset hv] at hr
  exact hr

/-- Exhausting the augmented singleton reductions retains a proper
represented drawing, a valid division, and exactly the original finite
feasibility answer, using the proved VI (3.3)(i) equivalence at each step. -/
theorem reduceSingletons_correct (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hproper : G.IsProper) (hD : IsDivision Δ) :
    ∃ (G' : Drawing S) (Δ' : Set (Set S)),
      Nonempty (GM06GapInputRep (gm06GapReduceSingletons X) G' Δ') ∧
      G'.IsProper ∧ IsDivision Δ' ∧
      (IsFeasible X.drawing.graph X.drawing.divisionSet ↔
        IsFeasible (gm06GapReduceSingletons X).drawing.graph
          (gm06GapReduceSingletons X).drawing.divisionSet) := by
  induction X using gm06GapReduceSingletons.induct generalizing G Δ with
  | case1 X hnone =>
    rw [gm06GapReduceSingletons, hnone]
    exact ⟨G, Δ, ⟨h⟩, hproper, hD, Iff.rfl⟩
  | case2 X v hfind ih =>
    have hv := h.drawing.findSingleton_mem v hfind
    obtain ⟨hnew⟩ := h.singletonGapData_rep hS hproper v hD hv
    have hD' : IsDivision (Δ \ {{(h.drawing.vertex v).val}}) :=
      ⟨hD.1.subset sdiff_subset, fun δ hδ => hD.2.1 δ hδ.1, hD.2.2.subset sdiff_subset⟩
    have hproper' : (induceDrawing G (G.V \ {(h.drawing.vertex v).val})).IsProper :=
      induceDrawing_isProper G hproper sdiff_subset
    obtain ⟨G', Δ', hrep', hp', hD'', hfeas'⟩ := ih hnew hproper' hD'
    rw [gm06GapReduceSingletons, hfind]
    exact ⟨G', Δ', hrep', hp', hD'',
      (h.drawing.singletonData_feasible_iff v hD h.drawing.divisionUnion_subset hv).trans hfeas'⟩

end GraphMinor.Compute.GM06GapInputRep
