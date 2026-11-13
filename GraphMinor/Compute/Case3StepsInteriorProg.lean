module

public import GraphMinor.Compute.Algorithm97ScanAux
public import GraphMinor.Compute.Algorithm33Multigraph

/-!
# Testing whether a member meets the wall perimeter

The two bitsets use compact compass labels. The existing disjointness scan
therefore tests precisely whether the selected member avoids the whole wall
perimeter. Registers are shifted above the member routing data, and all
arrays are retained for the subsequent call of (7.2).
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Compare member array 30 with compact perimeter array 20. -/
def case3InteriorProg : Cmd :=
  .seq (.assign 91 (.reg 14)) (testDisjointInstProg.shift 3 90)

/-- The scan returns one exactly when the two vertex sets are disjoint,
using at most `19 n + 9` steps and preserving arrays and registers below 90. -/
theorem case3InteriorProg_exec {w n : ℕ} (A P : Finset (Fin n))
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) {s : State}
    (hA : IsBitSet A 30 s) (hP : IsBitSet P 20 s) (hrn : s.regs 14 = n) :
    ∃ s' t, Exec w case3InteriorProg s s' t ∧ t ≤ 19 * n + 9 ∧
      s'.regs 100 = (if Disjoint A P then 1 else 0) ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ r < 90, s'.regs r = s.regs r) := by
  let s₁ := s.setReg 91 n
  have hex₁ : Exec w (.assign 91 (.reg 14)) s s₁ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hrn, hn, ↓reduceIte])
  have hA₁ : IsBitSet A 27 (s₁.unshift 3 90) := by
    exact hA.of_arr_eq (by rfl)
  have hP₁ : IsBitSet P 17 (s₁.unshift 3 90) := by
    exact hP.of_arr_eq (by rfl)
  have hr₁ : (s₁.unshift 3 90).regs 1 = n := by
    simp only [State.unshift_regs, show 1 + (90 : ℕ) = 91 by decide, s₁, State.setReg_regs_self]
  obtain ⟨s_sub, t, hex, ht, hres, harr, _⟩ :=
    testDisjointInstProg_exec (n := n) A P hw hn (s := s₁.unshift 3 90) hA₁ hP₁ hr₁
  change t ≤ 7 + 19 * n at ht
  let s' := s₁.applyShifted 3 90 s_sub
  refine ⟨s', 2 + t, .seq hex₁ (Exec.shift_from 3 90 hex), by omega, ?_, ?_, ?_⟩
  · exact (State.applyShifted_regs_add 3 90 s₁ s_sub 10).trans hres
  · intro a
    by_cases ha : a < 3
    · rw [State.applyShifted_arrs_lt _ _ _ _ ha]
      rfl
    · obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le (by romega : 3 ≤ a)
      subst a
      rw [show 3 + b = b + 3 by omega, State.applyShifted_arrs_add, harr]
      rfl
  · intro r hr
    rw [State.applyShifted_regs_lt _ _ _ _ hr, State.setReg_regs_ne _ _ (by romega)]

end GraphMinor.Compute
