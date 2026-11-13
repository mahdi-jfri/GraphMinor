module

public import GraphMinor.GM06.Alg34GapReductionBoundary
public import GraphMinor.GM06.Alg34RestrictionCrossFree
import GraphMinor.GM06.Alg34SingletonExhaustCorrect

/-!
# Geometric conditions through complete singleton exhaustion

The singleton restriction is the paper's deleted singleton block.
Its boundary coverage and cross-freeness follow from induced division
restriction. Repeat these facts together with representation, properness,
division validity and feasibility equivalence through the full phase.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- Singleton exhaustion retains all geometric conditions used by the
next driver phase, and preserves the finite feasibility answer. -/
theorem reduceSingletons_crossFree_correct (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hp : G.IsProper) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ = G.V ∩ bd S) (hCF : IsCrossFree (bd S) Δ) :
    ∃ (G' : Drawing S) (Δ' : Set (Set S)),
      Nonempty (GM06GapInputRep (gm06GapReduceSingletons X) G' Δ') ∧
      G'.IsProper ∧ IsDivision Δ' ∧ divisionUnion Δ' = G'.V ∩ bd S ∧
      IsCrossFree (bd S) Δ' ∧
      (IsFeasible X.drawing.graph X.drawing.divisionSet ↔
        IsFeasible (gm06GapReduceSingletons X).drawing.graph
          (gm06GapReduceSingletons X).drawing.divisionSet) := by
  induction X using gm06GapReduceSingletons.induct generalizing G Δ with
  | case1 X hnone =>
    rw [gm06GapReduceSingletons, hnone]
    exact ⟨G, Δ, ⟨h⟩, hp, hD, hbd, hCF, Iff.rfl⟩
  | case2 X v hfind ih =>
    have hv := h.drawing.findSingleton_mem v hfind
    obtain ⟨hnew⟩ := h.singletonGapData_rep hS hp v hD hv
    have hD' : IsDivision (Δ \ {{(h.drawing.vertex v).val}}) :=
      ⟨hD.1.subset sdiff_subset, fun δ hδ => hD.2.1 δ hδ.1, hD.2.2.subset sdiff_subset⟩
    have hp' : (induceDrawing G (G.V \ {(h.drawing.vertex v).val})).IsProper :=
      induceDrawing_isProper G hp sdiff_subset
    have hb' := h.singletonGapData_boundary v hD hv hbd
    have hcf' := h.drawing.inducedDivision_crossFree (X.drawing.singletonSurvivors v) hCF
    rw [h.drawing.singleton_inducedDivision v hD h.drawing.divisionUnion_subset hv] at hcf'
    obtain ⟨G', Δ', hr, hp'', hD'', hb, hcf, hf⟩ := ih hnew hp' hD' hb' hcf'
    rw [gm06GapReduceSingletons, hfind]
    exact ⟨G', Δ', hr, hp'', hD'', hb, hcf,
      (h.drawing.singletonData_feasible_iff v hD h.drawing.divisionUnion_subset hv).trans hf⟩

end GraphMinor.Compute.GM06GapInputRep
