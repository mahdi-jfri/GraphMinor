module

public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Updating the replacement splice cuts at a boundary visit

While scanning a returned path, the first boundary index is saved only on the first visit.
Every visit sets the other cut to the next position. This file proves that constant-time
update used to prepare Lemma 1's reverse splice.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- On a boundary visit, save the first position if it still holds the length sentinel,
then save the position after this visit. -/
def liftCutVisitProg (src r_first r_after r_i : ℕ) : Cmd :=
  .seq (.ite (.op .eq (.reg r_first) (.len src))
      (.assign r_first (.reg r_i)) .skip)
    (.assign r_after (.op .add (.reg r_i) (.const 1)))

/-- The cut update saves the true first index and the position after the present visit.
The hypotheses give the scan's index values and register separation. It costs at most nine steps. -/
theorem liftCutVisitProg_exec {w : ℕ} (src r_first r_after r_i : ℕ)
    (hfi : r_first ≠ r_i) (hfa : r_first ≠ r_after)
    (f j n : ℕ) (s : State) (hfn : f ≤ j) (hjn : j < n)
    (hlen : (s.arrs src).length = n) (hi : s.regs r_i = j)
    (hfirst : s.regs r_first = if f < j then f else n) (hw : n + 1 < 2 ^ w) :
    ∃ s' t, Exec w (liftCutVisitProg src r_first r_after r_i) s s' t ∧ t ≤ 9 ∧
      s'.regs r_first = f ∧ s'.regs r_after = j + 1 ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ q, q ≠ r_first → q ≠ r_after → s'.regs q = s.regs q) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hlenEval : (Expr.len src).eval w s = some n := by
    have he := eval_len (w := w) (s := s) (a := src) rfl (by rw [hlen]; omega)
    simpa only [hlen] using he
  by_cases hfj : f < j
  · have hf : s.regs r_first = f := by simpa only [hfj, ↓reduceIte] using hfirst
    have hneq : f ≠ n := by omega
    have heq : (Expr.op .eq (.reg r_first) (.len src)).eval w s = some 0 := by
      simpa only [hneq, ↓reduceIte] using eval_eq (eval_reg hf (by omega)) hlenEval hw1
    refine ⟨s.setReg r_after (j + 1), 8,
      .seq (.ite_false heq (.skip s))
        (.assign (eval_add (eval_reg hi (by omega)) (eval_const hw1) (by omega))),
      by omega, by simp [hfa, hf], by simp, fun _ => rfl, ?_⟩
    intro q _ hq; simp [hq]
  · have hfeq : f = j := by omega
    have hf : s.regs r_first = n := by simpa only [hfj, ↓reduceIte] using hfirst
    have heq : (Expr.op .eq (.reg r_first) (.len src)).eval w s = some 1 := by
      simpa only [↓reduceIte] using eval_eq (eval_reg hf (by omega)) hlenEval hw1
    let s1 := s.setReg r_first j
    have hi1 : s1.regs r_i = j := by simp [s1, Ne.symm hfi, hi]
    refine ⟨s1.setReg r_after (j + 1), 9,
      .seq (.ite_true heq (by omega) (.assign (eval_reg hi (by omega))))
        (.assign (eval_add (eval_reg hi1 (by omega)) (eval_const hw1) (by omega))),
      by omega, by simp [s1, hfa, hfeq], by simp, fun _ => rfl, ?_⟩
    intro q hqf hqa; simp [s1, hqa, hqf]

end GraphMinor.Compute.Crossing
