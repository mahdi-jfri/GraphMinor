module

public import GraphMinor.Compute.GM06Alg34SplitProg
public import GraphMinor.Compute.GM06Alg34Graph

/-!
# Correctness of the component-split rejection phase

The RAM program reads the original array and returns the finite
split-block complement. If that answer is zero, (3.3)(iii) rules out
finite feasibility. Transport across the supplied drawing bijections
then rules out feasibility of the represented instance itself.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S]

/-- The concrete component-split phase of (3.4) runs in cubic time and
rejects only infeasible represented instances, by (3.3)(iii). -/
theorem splitProg_rejection_correct {x : GM06DrawingData} {G : Drawing S}
    {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ) (hD : IsDivision Δ)
    {L : List (Fin x.n)} (hL : x.cuffs = [L]) {c : ℕ} (hc : 2 ≤ c)
    {s : State} (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06SplitProg s s' t ∧
      t ≤ 500 * (x.size + 1) ^ 3 ∧
      s'.regs 263 = (if !x.hasSplitBlock then 1 else 0) ∧
      (s'.regs 263 = 0 → ¬ IsFeasible G.toGraph Δ) := by
  obtain ⟨s', t, hex, ht, hflag, _, _, _, _⟩ := gm06SplitProg_exec x hL hc hinput
  refine ⟨s', t, hex, ht, hflag, ?_⟩
  intro hz hf
  have hs : x.hasSplitBlock = true := by
    cases hh : x.hasSplitBlock
    · simp only [hh, Bool.not_false, ↓reduceIte] at hflag
      omega
    · rfl
  exact x.not_feasible_of_hasSplitBlock hs ((h.feasible_iff hD).mp hf)

end GraphMinor.Compute.GM06DrawingRep
