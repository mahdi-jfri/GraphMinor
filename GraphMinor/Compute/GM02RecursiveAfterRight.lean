module

public import GraphMinor.Compute.GM02RecursiveReturnProgram
import GraphMinor.Compute.CrossingOpsBasic
import GraphMinor.Compute.CrossingOpsCycleTest

/-!
# Combining a pair of returned feasibility bits

After the right child returns, restore the parent's phase by removing
its side tag. The accumulator becomes its old value or the conjunction
of the two child bits. All intermediate words are bits, so this update
is safe in every word size exceeding the fixed control constants.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

private theorem pair_accumulator_eval {w : ℕ} (s : State) (ra rl rr : Reg)
    (a l r : ℕ) (ha : s.regs ra = a) (hl : s.regs rl = l) (hr : s.regs rr = r)
    (ha1 : a ≤ 1) (hl1 : l ≤ 1) (hr1 : r ≤ 1) (hw : 1 < 2 ^ w) :
    (.op .sub (.const 1) (.op .mul (.op .sub (.const 1) (.reg ra))
      (.op .sub (.const 1) (.op .mul (.reg rl) (.reg rr)))) : Expr).eval w s =
        some (1 - (1 - a) * (1 - l * r)) := by
  have hlr : l * r ≤ 1 := by simpa only [Nat.mul_one] using Nat.mul_le_mul hl1 hr1
  have hprod : (1 - a) * (1 - l * r) ≤ 1 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul (Nat.sub_le 1 a) (Nat.sub_le 1 (l * r))
  exact eval_sub (eval_const hw)
    (eval_mul (eval_sub (eval_const hw) (eval_reg ha (ha1.trans_lt hw)))
      (eval_sub (eval_const hw)
        (eval_mul (eval_reg hl (hl1.trans_lt hw)) (eval_reg hr (hr1.trans_lt hw)) (hlr.trans_lt hw)))
      (hprod.trans_lt hw))

/-- The parent's bit update is the disjunction over this pair of child answers. -/
theorem gm02RecursiveAccumulator_eq_one {a l r : ℕ} (ha : a ≤ 1) (hl : l ≤ 1) (hr : r ≤ 1) :
    1 - (1 - a) * (1 - l * r) = 1 ↔ a = 1 ∨ (l = 1 ∧ r = 1) := by
  have ha' : a = 0 ∨ a = 1 := by omega
  have hl' : l = 0 ∨ l = 1 := by omega
  have hr' : r = 0 ∨ r = 1 := by omega
  rcases ha' with rfl | rfl <;> rcases hl' with rfl | rfl <;>
    rcases hr' with rfl | rfl <;> decide

/-- The exact right-child continuation returns to scanning after updating one code. -/
theorem gm02RecursiveAfterRightProg_exec {w : ℕ} (q : ℕ) (s : State)
    (phase code aggregate leftAnswer rightAnswer : ℕ)
    (hphase : s.regs (gm02RecursiveControlBase q + 3) = phase + 2)
    (hcode : s.regs (gm02RecursiveControlBase q + 4) = code)
    (hagg : s.regs (gm02RecursiveControlBase q + 5) = aggregate)
    (hleft : s.regs (gm02RecursiveControlBase q + 6) = leftAnswer)
    (hright : s.regs outReg = rightAnswer)
    (hph : phase ≤ 1) (ha : aggregate ≤ 1) (hl : leftAnswer ≤ 1) (hr : rightAnswer ≤ 1)
    (hw : 3 < 2 ^ w) (hnext : code + 1 < 2 ^ w) :
    ∃ s', Exec w (gm02RecursiveAfterRightProg q) s s' 22 ∧
      s'.regs (gm02RecursiveControlBase q + 3) = phase ∧
      s'.regs (gm02RecursiveControlBase q + 4) = code + 1 ∧
      s'.regs (gm02RecursiveControlBase q + 5) = 1 - (1 - aggregate) * (1 - leftAnswer * rightAnswer) ∧
      s'.regs (gm02RecursiveControlBase q + 18) = 2 ∧ s'.arrs = s.arrs ∧
      (∀ r, r ∉ [gm02RecursiveControlBase q + 3, gm02RecursiveControlBase q + 4,
        gm02RecursiveControlBase q + 5, gm02RecursiveControlBase q + 18] → s'.regs r = s.regs r) := by
  let b := gm02RecursiveControlBase q
  have hbg := gm02RecursiveControlBase_ge q
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hphaseMod : (phase + 2) % 2 = phase := by omega
  let s₁ := s.setReg (b + 3) phase
  have he₁ : Exec w (.assign (b + 3) (.op .mod (.reg (b + 3)) (.const 2))) s s₁ 4 := by
    apply Exec.assign
    simpa only [hphaseMod] using
      eval_mod (eval_reg hphase (by omega : phase + 2 < 2 ^ w)) (eval_const h2) (by decide)
  let answer := 1 - (1 - aggregate) * (1 - leftAnswer * rightAnswer)
  let s₂ := s₁.setReg (b + 5) answer
  have he₂ : Exec w (.assign (b + 5) (.op .sub (.const 1)
      (.op .mul (.op .sub (.const 1) (.reg (b + 5)))
        (.op .sub (.const 1) (.op .mul (.reg (b + 6)) (.reg outReg)))))) s₁ s₂ 12 := by
    apply Exec.assign
    apply pair_accumulator_eval s₁ (b + 5) (b + 6) outReg aggregate leftAnswer rightAnswer
    · simpa [s₁] using hagg
    · simpa [s₁] using hleft
    · exact (State.setReg_regs_ne _ _ (by dsimp only [b, Reg, outReg] at *; omega)).trans hright
    · exact ha
    · exact hl
    · exact hr
    · exact h1
  let s₃ := s₂.setReg (b + 4) (code + 1)
  have he₃ : Exec w (.assign (b + 4) (.op .add (.reg (b + 4)) (.const 1))) s₂ s₃ 4 := by
    apply Exec.assign
    apply eval_add _ (eval_const h1) hnext
    apply eval_reg _ (by omega : code < 2 ^ w)
    simpa [s₂, s₁] using hcode
  let s₄ := s₃.setReg (b + 18) 2
  have he₄ : Exec w (.assign (b + 18) (.const 2)) s₃ s₄ 2 := Exec.assign (eval_const h2)
  refine ⟨s₄, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)), ?_, ?_, ?_, by simp [s₄, b], rfl, ?_⟩
  · simp [s₄, s₃, s₂, s₁, b]
  · simp [s₄, s₃, b]
  · simp [s₄, s₃, s₂, answer, b]
  · intro r hn
    have hn' : r ≠ b + 3 ∧ r ≠ b + 4 ∧ r ≠ b + 5 ∧ r ≠ b + 18 := by
      simpa [b] using hn
    simp only [s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ hn'.2.2.2,
      State.setReg_regs_ne _ _ hn'.2.1, State.setReg_regs_ne _ _ hn'.2.2.1,
      State.setReg_regs_ne _ _ hn'.1]

end GraphMinor.Compute
