module

public import GraphMinor.Compute.GM06Alg34GapSingletonComplexity
public import GraphMinor.GM06.Alg34GapSingletonCorrect
public import GraphMinor.GM06.Alg34GapDiscLayout

/-!
# Correct augmented singleton phase for every represented disc input

Combine the exact RAM execution with the geometric singleton
restriction proof. The resulting arrays represent a proper disc
drawing and a valid division, with no singleton block remaining and
with exactly the original feasibility answer. The time bound and word
size depend only on the original finite base input.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- The complete augmented singleton RAM phase is correct for every
proper represented disc drawing and division, with polynomial time
and logarithmic words in the supplied base input size. -/
theorem singletonExhaust_program_correct (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hproper : G.IsProper) (hD : IsDivision Δ)
    {s : State} (hinput : s.arrs 0 = X.drawing.words) (hgap : s.arrs 47 = X.discGapWords) :
    ∃ (s' : State) (t : ℕ) (G' : Drawing S) (Δ' : Set (Set S)),
      Exec (wordSize 21 X.drawing.size) gm06GapSingletonExhaustProg s s' t ∧
      t ≤ 4000 * (X.drawing.size + 2) ^ 22 ∧
      s'.arrs 0 = (gm06GapReduceSingletons X).drawing.words ∧
      s'.arrs 47 = (gm06GapReduceSingletons X).discGapWords ∧
      Nonempty (GM06GapInputRep (gm06GapReduceSingletons X) G' Δ') ∧
      G'.IsProper ∧ IsDivision Δ' ∧
      gm06FindSingleton (gm06GapReduceSingletons X).drawing.division = none ∧
      (IsFeasible G.toGraph Δ ↔ IsFeasible G'.toGraph Δ') := by
  obtain ⟨s', t, he, ht, hin, hgap', _, _⟩ :=
    gm06GapSingletonExhaustProg_exec_poly X (h.disc_layout hS) hinput hgap
  obtain ⟨G', Δ', ⟨hr⟩, hp, hD', hfeas⟩ := h.reduceSingletons_correct hS hproper hD
  exact ⟨s', t, G', Δ', he, ht, hin, hgap', ⟨hr⟩, hp, hD',
    gm06GapReduceSingletons_find_none X,
    (h.drawing.feasible_iff hD).trans (hfeas.trans (hr.drawing.feasible_iff hD').symm)⟩

end GraphMinor.Compute.GM06GapInputRep
