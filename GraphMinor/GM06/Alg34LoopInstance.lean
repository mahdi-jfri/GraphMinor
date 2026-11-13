module

public import GraphMinor.GM06.Alg34DiscDualExhaust
public import GraphMinor.GM06.Alg34TerminalBounds
public import GraphMinor.Compute.GM06Alg34LoopBounds
import GraphMinor.Compute.GM06Alg34DiscRep

/-!
# Intended disc instances reached by the reduction loop

A finite input represents a proper disc drawing with a division covering
its boundary, and its current division is cross-free. These are exactly
the geometric conditions used after the initial crossing check. They
are proof conditions on reached states, expressed using the existing
disc-instance type and the supplied-label interpretation.
-/

@[expose] public section
namespace GraphMinor.Compute

open Set Surface GM06
universe u

/-- The geometric conditions of a current problem after the crossing check. -/
def gm06LoopInstance (X : GM06GapInput) : Prop :=
  ∃ I : DiscDivInstance.{u}, Nonempty (GM06GapInputRep X I.G I.Δ) ∧ I.IsCrossFreeInst

/-- Singleton exhaustion retains an intended disc instance and every fixed
numerical bound, preserves its answer, and cannot increase its work charge. -/
theorem gm06LoopInstance_singletons {X : GM06GapInput} (hX : gm06LoopInstance.{u} X)
    {M E Q : ℕ} (hB : gm06LoopBounds M E Q X) :
    gm06LoopInstance.{u} (gm06GapReduceSingletons X) ∧
      gm06LoopBounds M E Q (gm06GapReduceSingletons X) ∧
      (IsFeasible X.drawing.graph X.drawing.divisionSet ↔
        IsFeasible (gm06GapReduceSingletons X).drawing.graph (gm06GapReduceSingletons X).drawing.divisionSet) ∧
      (gm06GapReduceSingletons X).drawing.workWeight (M + 1) ≤ X.drawing.workWeight (M + 1) := by
  obtain ⟨I, ⟨h⟩, hCF⟩ := hX
  haveI : T2Space I.S := t2Space_of_isClosedDiscSpace I.hDisc
  obtain ⟨G', Δ', hr, hp, hD, hb, hcf, hf⟩ :=
    h.reduceSingletons_crossFree_correct I.hDisc I.hProper I.hΔ I.hΔ_eq hCF
  obtain ⟨hn, he, hr'⟩ := h.reduceSingletons_counts_le I.hDisc I.hProper I.hΔ
  obtain ⟨hcell, hnr⟩ := h.reduceSingletons_cellCount_le I.hDisc I.hProper I.hΔ
  obtain ⟨hreg, hcuff, hdiv⟩ := h.reduceSingletons_sections_le I.hDisc I.hProper I.hΔ Q
    hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2.1 hB.2.2.2.2.2
  let I' : DiscDivInstance.{u} := {
    S := I.S, hDisc := I.hDisc, G := G', hProper := hp, Δ := Δ', hΔ := hD, hΔ_eq := hb }
  exact ⟨⟨I', hr, hcf⟩,
    ⟨hnr.trans hB.1, he.trans hB.2.1, hcell.trans hB.2.2.1, hreg, hcuff, hdiv⟩,
    hf, gm06GapReduceSingletons_workWeight_le (M + 1) X⟩

/-- A valid division on a null current instance is feasible. -/
theorem gm06LoopInstance_null_feasible {X : GM06GapInput} (hX : gm06LoopInstance.{u} X)
    (hn : X.drawing.n = 0) : IsFeasible X.drawing.graph X.drawing.divisionSet := by
  obtain ⟨I, ⟨h⟩, _⟩ := hX
  exact X.drawing.feasible_of_n_eq_zero hn (h.drawing.division_isDivision I.hΔ)

/-- The connected stuck branch retains an intended disc instance and fixed
bounds, preserves its answer, and strictly lowers the queue charge. -/
theorem gm06LoopInstance_dual {X : GM06GapInput} (hX : gm06LoopInstance.{u} X)
    {M E Q : ℕ} (hB : gm06LoopBounds M E Q X) (hn : 0 < X.drawing.n)
    (hI : X.drawing.findInteriorComponent = none)
    (hSing : gm06FindSingleton X.drawing.division = none)
    (hk : X.drawing.componentRoots.length ≤ 1) :
    gm06LoopInstance.{u} (gm06GapReduceSingletons X.discDualData) ∧
      gm06LoopBounds M E Q (gm06GapReduceSingletons X.discDualData) ∧
      (IsFeasible X.drawing.graph X.drawing.divisionSet ↔
        IsFeasible (gm06GapReduceSingletons X.discDualData).drawing.graph
          (gm06GapReduceSingletons X.discDualData).drawing.divisionSet) ∧
      (gm06GapReduceSingletons X.discDualData).drawing.workWeight (M + 1) < X.drawing.workWeight (M + 1) := by
  obtain ⟨I, ⟨h⟩, hCF⟩ := hX
  haveI : T2Space I.S := t2Space_of_isClosedDiscSpace I.hDisc
  have hc := h.drawing.connected_of_roots_length_le_one hn hk
  obtain ⟨G', Δ', hr, hp, hD, hb, hcf, hf, hnr, he, hcell, hreg, hcuff, hdiv, hwork⟩ :=
    h.discDualExhaust_correct I.hDisc I.hProper hc I.hΔ I.hΔ_eq hCF hn hI hSing M Q hB.1 hB.2.2.1
  let I' : DiscDivInstance.{u} := {
    S := I.S, hDisc := I.hDisc, G := G', hProper := hp, Δ := Δ', hΔ := hD, hΔ_eq := hb }
  exact ⟨⟨I', hr, hcf⟩, ⟨hnr, he.trans hB.2.1, hcell, hreg, hcuff, hdiv⟩, hf, hwork⟩

end GraphMinor.Compute
