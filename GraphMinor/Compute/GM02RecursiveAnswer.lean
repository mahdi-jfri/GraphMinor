module

public import GraphMinor.Compute.GM02TerminatedInput

/-!
# Reading the meaning of a recursive answer flag

The three printed outcomes are represented by flags one, zero, and two.
Unpack their correctness relation into either a width threshold or an
ordinary feasibility bit. Conversely, the exact feasibility bit gives a
correct ordinary answer. These elementary forms are used when returning
from the two child calls.
-/

public section
namespace GraphMinor.Compute

/-- Flag two of a correct recursive answer carries the width threshold. -/
theorem GM02SimpleTerminatedInput.width_of_recursiveCorrect_flag (x : GM02SimpleTerminatedInput)
    (q : ℕ) (s : State) (h : x.recursiveCorrect q s) (hflag : s.regs outReg = 2) : q ≤ x.width := by
  rcases h with ⟨h1, _⟩ | ⟨h0, _⟩ | ⟨_, hw⟩
  · omega
  · omega
  · exact hw

/-- A correct answer other than flag two is a bit deciding exactly feasibility. -/
theorem GM02SimpleTerminatedInput.bit_of_recursiveCorrect (x : GM02SimpleTerminatedInput)
    (q : ℕ) (s : State) (h : x.recursiveCorrect q s) (hflag : s.regs outReg ≠ 2) :
    s.regs outReg ≤ 1 ∧ (s.regs outReg = 1 ↔ x.A.Feasible (Graph.ofSimpleGraph x.G)) := by
  rcases h with ⟨h1, hf⟩ | ⟨h0, hf⟩ | ⟨h2, _⟩
  · exact ⟨by omega, ⟨fun _ => hf, fun _ => h1⟩⟩
  · exact ⟨by omega, ⟨fun h1 => by omega, fun hfeas => (hf hfeas).elim⟩⟩
  · exact (hflag h2).elim

/-- Any exact feasibility bit is a correct recursive answer. -/
theorem GM02SimpleTerminatedInput.recursiveCorrect_of_bit (x : GM02SimpleTerminatedInput)
    (q : ℕ) (s : State) (hbit : s.regs outReg ≤ 1)
    (hfeas : s.regs outReg = 1 ↔ x.A.Feasible (Graph.ofSimpleGraph x.G)) : x.recursiveCorrect q s := by
  by_cases h1 : s.regs outReg = 1
  · exact Or.inl ⟨h1, hfeas.mp h1⟩
  · exact Or.inr (Or.inl ⟨by omega, fun hf => h1 (hfeas.mpr hf)⟩)

end GraphMinor.Compute
