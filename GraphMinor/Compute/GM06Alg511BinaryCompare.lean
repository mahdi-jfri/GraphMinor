module

public import GraphMinor.Compute.GM06Alg511BinarySigned
import Mathlib.Tactic

/-!
# Signed comparison with either representation of zero

Scan a signed magnitude row. A zero magnitude gives the answer
zero regardless of its sign. A nonzero magnitude gives its sign
as the negative-value test. Subtract the two supplied signed
operands and apply this test to obtain strict comparison. Both
scans are linear in the supplied digit counts, and all arithmetic
on magnitudes remains in binary arrays. This supplies comparison
for VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- At a nonzero digit, retain the supplied sign as the answer. -/
def gm06Alg511BinaryNegativeBody : Cmd :=
  .ite (.read 2002 (.reg 2411)) (.assign 0 (.reg 2402)) .skip

/-- Test negativity without converting a binary magnitude to a word. -/
def gm06Alg511BinaryNegativeProg : Cmd :=
  .seq (.assign 0 (.const 0))
    (.seq (.assign 2411 (.const 0))
      (forUp 2411 (.len 2002) gm06Alg511BinaryNegativeBody))

/-- The negativity scan is exact even for a zero magnitude with a
negative sign. It retains its entire supplied row and sign. -/
theorem gm06Alg511BinaryNegativeProg_exec {w : ℕ} (xs : List ℕ) (sign : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hlen : xs.length < 2 ^ w) (hsign : sign < 2)
    (hbits : ∀ d ∈ xs, d < 2) (ha : s.arrs 2002 = xs) (hs : s.regs 2402 = sign) :
    ∃ t u flag, Exec w gm06Alg511BinaryNegativeProg s t u ∧ u ≤ 7 + 11 * xs.length ∧
      Keeps [0, 2411] [] s t ∧ t.regs 0 = flag ∧ flag < 2 ∧
      (flag = 1 ↔ gm06Alg511BinarySignedValue sign xs < 0) := by
  have hsf : sign < 2 ^ w := hsign.trans_le (by omega)
  let s₁ := s.setReg 0 0
  let s₂ := s₁.setReg 2411 0
  have he₁ : Exec w (.assign 0 (.const 0)) s s₁ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  have he₂ : Exec w (.assign 2411 (.const 0)) s₁ s₂ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  let I : ℕ → State → Prop := fun i st => st.regs 2411 = i ∧ st.arrs 2002 = xs ∧ st.regs 2402 = sign ∧
    st.regs 0 = (if gm06Alg511BinaryValue (xs.take i) = 0 then 0 else sign) ∧ Keeps [0, 2411] [] s st
  have hI : I 0 s₂ := by
    refine ⟨by simp [s₂], ha, by simpa [s₂, s₁] using hs, ?_, ?_⟩
    · simp [s₂, s₁, gm06Alg511BinaryValue]
    · exact ((Keeps.refl _ _ s).setReg (by simp) 0).setReg (by simp) 0
  obtain ⟨st, ut, heLoop, htLoop, hEnd⟩ := Crossing.forUp_exec' I xs.length 4
    (r_i := 2411) (hi := .len 2002) (body := gm06Alg511BinaryNegativeBody) hw hlen
    (fun i hi st h => ⟨h.1, Crossing.eval_len h.2.1 hlen⟩)
    (by
      intro i hi st h
      obtain ⟨hidx, hrow, hsg, hflag, hk⟩ := h
      have hd : xs[i] < 2 := hbits _ (List.getElem_mem hi)
      have hread : (Expr.read 2002 (.reg 2411)).eval w st = some xs[i] := by
        simpa only [hrow] using Crossing.eval_read (a := 2002) (Crossing.eval_reg hidx (hi.trans hlen))
          (by simpa only [hrow] using hi) (by simpa only [hrow] using hd.trans_le (show 2 ≤ 2 ^ w by omega))
      have hnext := gm06Alg511BinaryValue_take_succ xs i hi
      by_cases hz : xs[i] = 0
      · have he : Exec w gm06Alg511BinaryNegativeBody st st 3 :=
          .ite_false (by simpa only [hz] using hread) (.skip _)
        refine ⟨st, 3, he, by decide, ?_, hidx⟩
        refine ⟨by simp, hrow, by simpa only [State.setReg_regs_ne _ _ (by decide : (2402 : ℕ) ≠ 2411)] using hsg, ?_,
          hk.setReg (by simp) (i + 1)⟩
        simpa only [State.setReg_regs_ne _ _ (by decide : (0 : ℕ) ≠ 2411), hnext, hz,
          Nat.mul_zero, Nat.add_zero] using hflag
      · let su := st.setReg 0 sign
        have he : Exec w gm06Alg511BinaryNegativeBody st su 4 :=
          .ite_true hread hz (.assign (Crossing.eval_reg hsg hsf))
        have hpos : 0 < gm06Alg511BinaryValue (xs.take (i + 1)) := by
          have hone : xs[i] = 1 := by omega
          rw [hnext, hone, Nat.mul_one]
          have hp := Nat.two_pow_pos i
          omega
        refine ⟨su, 4, he, le_rfl, ?_, by simpa only [su, State.setReg_regs_ne _ _ (by decide : (2411 : ℕ) ≠ 0)] using hidx⟩
        have hsg' : (su.setReg 2411 (i + 1)).regs 2402 = sign := by
          simpa only [su, State.setReg_regs_ne _ _ (by decide : (2402 : ℕ) ≠ 0),
            State.setReg_regs_ne _ _ (by decide : (2402 : ℕ) ≠ 2411)] using hsg
        refine ⟨by simp, hrow, hsg', ?_,
          (hk.setReg (show 0 ∈ [0, 2411] by simp) sign).setReg (show 2411 ∈ [0, 2411] by simp) (i + 1)⟩
        simp only [su, State.setReg_regs_ne _ _ (by decide : (0 : ℕ) ≠ 2411), State.setReg_regs_self,
          Nat.ne_of_gt hpos, ite_false]) s₂ hI
  obtain ⟨_, _, _, hflag, hk⟩ := hEnd
  let flag := if gm06Alg511BinaryValue xs = 0 then 0 else sign
  have hflag' : st.regs 0 = flag := by simpa only [List.take_length] using hflag
  refine ⟨st, 2 + (2 + ut), flag, .seq he₁ (.seq he₂ heLoop), ?_, hk, hflag', ?_, ?_⟩
  · simp only [Expr.cost] at htLoop
    omega
  · unfold flag
    split_ifs <;> omega
  · unfold flag gm06Alg511BinarySignedValue
    by_cases hz : gm06Alg511BinaryValue xs = 0
    · simp [hz]
    · by_cases hs1 : sign = 1
      · simp only [hz, hs1, ite_false, ite_true, true_iff]
        exact neg_lt_zero.mpr (Int.natCast_pos.mpr (Nat.pos_of_ne_zero hz))
      · simp only [hz, hs1, ite_false, false_iff]
        exact not_lt_of_ge (Int.natCast_nonneg _)

/-- Strict signed comparison subtracts the two binary integers
and tests the exact resulting signed magnitude for negativity. -/
def gm06Alg511BinarySignedLessProg : Cmd :=
  .seq gm06Alg511BinarySignedSubtractProg gm06Alg511BinaryNegativeProg

/-- Signed comparison has linear time in the supplied digit
counts, returns a Boolean and retains both original operands and
signs. No large integer is read or computed in a single word. -/
theorem gm06Alg511BinarySignedLessProg_exec {w : ℕ} (a b : List ℕ) (sa sb : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max a.length b.length + 1 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2) (hsa : sa < 2) (hsb : sb < 2)
    (hA : s.arrs 2000 = a) (hB : s.arrs 2001 = b)
    (hSA : s.regs 2400 = sa) (hSB : s.regs 2401 = sb) :
    ∃ t u flag, Exec w gm06Alg511BinarySignedLessProg s t u ∧
      u ≤ 270 + 280 * max a.length b.length ∧
      Keeps [0, 20, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2402, 2404, 2410, 2411]
        [2002, 2003, 2004, 2005] s t ∧ t.regs 0 = flag ∧ flag < 2 ∧
      (flag = 1 ↔ gm06Alg511BinarySignedValue sa a < gm06Alg511BinarySignedValue sb b) := by
  obtain ⟨st, u, out, sign, he, ht, hk, hout, hsign, hsignBit, hlen, hbits, hval⟩ :=
    gm06Alg511BinarySignedSubtractProg_exec a b sa sb s hw hsize habits hbbits hsa hsb hA hB hSA hSB
  obtain ⟨t, v, flag, he₂, ht₂, hk₂, hflag, hflagBit, hiff⟩ :=
    gm06Alg511BinaryNegativeProg_exec (w := w) out sign st (by omega) (by omega) hsignBit hbits hout hsign
  have hkeep : Keeps [0, 20, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2402, 2404, 2410, 2411]
      [2002, 2003, 2004, 2005] s t := (hk.mono (by simp) (by simp)).trans hk₂ (by simp) (by simp)
  refine ⟨t, u + v, flag, .seq he he₂, by omega, hkeep, hflag, hflagBit, ?_⟩
  rw [hval] at hiff
  exact hiff.trans (sub_lt_zero)

end GraphMinor.Compute
