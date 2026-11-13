module

public import GraphMinor.GM06.Alg34GapInteriorCorrect
public import GraphMinor.GM06.Alg34GapDiscLayout
public import GraphMinor.Compute.GM06Alg34GapInteriorStep

/-!
# Correct interior-component search and deletion for every disc input

A failed search leaves the represented instance unchanged. A successful
search supplies the proved interior-component test, so the augmented
component-deletion correctness theorem applies. Combining these cases
with the exact RAM execution gives the driver a complete cubic-time
search/deletion step with an exact success flag.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- One finite interior search/deletion step retains a proper represented
instance with the same boundary division and feasibility answer. -/
theorem interiorStepData_correct (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hproper : G.IsProper) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ ⊆ G.V ∩ bd S) :
    ∃ G' : Drawing S, Nonempty (GM06GapInputRep X.interiorStepData G' Δ) ∧
      G'.IsProper ∧ divisionUnion Δ ⊆ G'.V ∩ bd S ∧
      (IsFeasible X.drawing.graph X.drawing.divisionSet ↔
        IsFeasible X.interiorStepData.drawing.graph X.interiorStepData.drawing.divisionSet) := by
  cases hf : X.drawing.findInteriorComponent with
  | none =>
    rw [GM06GapInput.interiorStepData, hf]
    exact ⟨G, ⟨h⟩, hproper, hbd, Iff.rfl⟩
  | some a =>
    have ha : X.drawing.isInteriorComponent a = true := List.find?_some hf
    rw [GM06GapInput.interiorStepData, hf]
    exact h.interiorGapData_correct hS hproper a ha hD hbd

/-- The interior-component RAM step is correct for every proper represented
disc instance, with cubic time and logarithmic words in the supplied input. -/
theorem interiorStep_program_correct (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hproper : G.IsProper) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ ⊆ G.V ∩ bd S)
    {c : ℕ} (hc : 3 ≤ c) {s : State} (hinput : s.arrs 0 = X.drawing.words)
    (hgap : s.arrs 47 = X.discGapWords) :
    ∃ (s' : State) (t : ℕ) (G' : Drawing S),
      Exec (wordSize c X.drawing.size) gm06GapInteriorStepProg s s' t ∧
      t ≤ 2000 * (X.drawing.size + 2) ^ 3 ∧
      s'.arrs 0 = X.interiorStepData.drawing.words ∧ s'.arrs 47 = X.interiorStepData.discGapWords ∧
      s'.regs 6600 = (if X.drawing.findInteriorComponent.isSome then 1 else 0) ∧
      Nonempty (GM06GapInputRep X.interiorStepData G' Δ) ∧ G'.IsProper ∧
      divisionUnion Δ ⊆ G'.V ∩ bd S ∧ (IsFeasible G.toGraph Δ ↔ IsFeasible G'.toGraph Δ) := by
  obtain ⟨s', t, he, ht, hin, hgap', hflag, _⟩ :=
    gm06GapInteriorStepProg_exec X (h.disc_layout hS) hc hinput hgap
  obtain ⟨G', ⟨hr⟩, hp, hbd', hfeas⟩ := h.interiorStepData_correct hS hproper hD hbd
  exact ⟨s', t, G', he, ht, hin, hgap', hflag, ⟨hr⟩, hp, hbd',
    (h.drawing.feasible_iff hD).trans (hfeas.trans (hr.drawing.feasible_iff hD).symm)⟩

end GraphMinor.Compute.GM06GapInputRep
