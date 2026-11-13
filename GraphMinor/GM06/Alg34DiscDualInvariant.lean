module

public import GraphMinor.GM06.Alg34DiscArrayBounds
public import GraphMinor.GM06.Alg34DualGapCorrect
import GraphMinor.GM06.DualExists
import GraphMinor.GM06.Section2Dual

/-!
# Geometric conditions after the plain dual update

The plain update is the canonical augmented dual at the supplied cuff.
VI (3.2) preserves its answer, and VI (2.1) gives cross-freeness of the
dual division. Thus the next singleton phase starts with all geometric
conditions used by the reduction loop.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- The plain finite dual preserves the answer and retains all geometric
conditions required by the following reductions. -/
theorem discDualData_crossFree_correct (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hp : G.IsProper) (hc : IsGraphConnected G.toGraph)
    (hR : 0 < X.drawing.regions.length) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ = G.V ∩ bd S) (hCF : IsCrossFree (bd S) Δ) :
    ∃ D Δ', Nonempty (GM06GapInputRep X.discDualData D Δ') ∧ D.IsProper ∧
      IsDivision Δ' ∧ divisionUnion Δ' = D.V ∩ bd S ∧ IsCrossFree (bd S) Δ' ∧
      (IsFeasible X.drawing.graph X.drawing.divisionSet ↔
        IsFeasible X.discDualData.drawing.graph X.discDualData.drawing.divisionSet) := by
  obtain ⟨c, heq⟩ := h.discDualData_eq_cuff hS hR
  obtain ⟨D, hd⟩ := exists_isDiscDualDrawing hS hp hc
  obtain ⟨hr, hp', hD', hb', hf⟩ :=
    (h.gap c).dualGapInput_correct hS hc hd hR hD hbd hCF
  have hcf' : IsCrossFree (bd S) (dualDivision (bd S) (D.V ∩ bd S) Δ) :=
    GraphMinor.GM06.theorem_2_1_proof (bd S) (D.V ∩ bd S) Δ hS.isOArc_bd hD
      (hbd ▸ inter_subset_right) (hbd.symm ▸ hd.2.2.2.2.1)
  refine ⟨D, dualDivision (bd S) (D.V ∩ bd S) Δ, ?_, hp', hD', hb', hcf', ?_⟩
  · rw [heq]
    exact hr
  · rw [heq]
    exact hf

end GraphMinor.Compute.GM06GapInputRep
