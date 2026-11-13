module

public import GraphMinor.Compute.GM06Alg511BinaryNormalize
import Mathlib.Tactic

/-!
# Choosing the orientation with binary comparison

Compare the scaled target with the scaled current winding. If the
current value is larger, reverse the sign of both rows. The resulting
current value is at most the resulting target. Register 57 records
whether the graph, cuff orders, rotations and linkage must also be
reflected. Those geometric data are handled by their own reflection
programs. This file verifies the binary comparison and value changes
in the orientation step of VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Reverse both retained comparison values if the current value
is greater than the target, recording the branch in register 57. -/
def gm06Alg511BinaryOrientationProg : Cmd :=
  .seq (gm06Alg511BinaryRowLessProg 2801 2800)
    (.seq (.assign 57 (.reg 0))
      (.ite (.reg 57) (.seq (gm06Alg511BinaryNegateRowProg 2800) (gm06Alg511BinaryNegateRowProg 2801)) .skip))

/-- The executed binary orientation test retains all magnitude
digits, returns the exact reflection bit and gives an ordered pair
of comparison values. The cost is linear in the supplied widths. -/
theorem gm06Alg511BinaryOrientationProg_exec {w : ℕ} (sc st : ℕ) (current target : List ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max current.length target.length + 2 < 2 ^ w)
    (hsc : sc < 2) (hst : st < 2) (hc : ∀ d ∈ current, d < 2) (ht : ∀ d ∈ target, d < 2)
    (hC : s.arrs 2800 = sc :: current) (hT : s.arrs 2801 = st :: target) :
    ∃ t u flag sc' st', Exec w gm06Alg511BinaryOrientationProg s t u ∧
      u ≤ 420 + 350 * (current.length + target.length + 1) ∧
      Keeps [0, 20, 57, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2400, 2401, 2402, 2404, 2410, 2411]
        [2000, 2001, 2002, 2003, 2004, 2005, 2800, 2801] s t ∧
      t.regs 57 = flag ∧ flag < 2 ∧
      (flag = 1 ↔ gm06Alg511BinaryRowValue (st :: target) < gm06Alg511BinaryRowValue (sc :: current)) ∧
      t.arrs 2800 = sc' :: current ∧ t.arrs 2801 = st' :: target ∧ sc' < 2 ∧ st' < 2 ∧
      gm06Alg511BinaryRowValue (sc' :: current) =
        (if flag = 1 then -gm06Alg511BinaryRowValue (sc :: current) else gm06Alg511BinaryRowValue (sc :: current)) ∧
      gm06Alg511BinaryRowValue (st' :: target) =
        (if flag = 1 then -gm06Alg511BinaryRowValue (st :: target) else gm06Alg511BinaryRowValue (st :: target)) ∧
      gm06Alg511BinaryRowValue (sc' :: current) ≤ gm06Alg511BinaryRowValue (st' :: target) := by
  obtain ⟨s₁, u₁, flag, he₁, ht₁, hk₁, hf₁, hbit, hiff⟩ := gm06Alg511BinaryRowLessProg_exec (w := w)
    2801 2800 (by decide) (by decide) target current st sc s hw (by omega) ht hc hst hsc hT hC
  let s₂ := s₁.setReg 57 flag
  have he₂ : Exec w (.assign 57 (.reg 0)) s₁ s₂ 2 := .assign (Crossing.eval_reg hf₁ (hbit.trans_le (by omega)))
  let R := [0, 20, 57, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2400, 2401, 2402, 2404, 2410, 2411]
  let A := [2000, 2001, 2002, 2003, 2004, 2005, 2800, 2801]
  have hkeep₂ : Keeps R A s s₂ := (hk₁.mono (by simp [R]) (by simp [A])).setReg (by simp [R]) flag
  have hc₂ : s₂.arrs 2800 = sc :: current := (hk₁.2 2800 (by decide)).trans hC
  have ht₂ : s₂.arrs 2801 = st :: target := (hk₁.2 2801 (by decide)).trans hT
  by_cases hone : flag = 1
  · obtain ⟨s₃, he₃, hk₃, hc₃, hsc₃, hvc₃⟩ := gm06Alg511BinaryNegateRowProg_exec (w := w) 2800 sc current s₂ (by omega) hsc hc₂
    obtain ⟨t, he₄, hk₄, ht₄, hst₄, hvt₄⟩ := gm06Alg511BinaryNegateRowProg_exec (w := w) 2801 st target s₃ (by omega) hst
      ((hk₃.2 2801 (by decide)).trans ht₂)
    have hkeep : Keeps R A s t := (hkeep₂.trans hk₃ (by simp [R]) (by simp [A])).trans hk₄ (by simp [R]) (by simp [A])
    refine ⟨t, u₁ + (2 + (1 + (6 + 6))), flag, 1 - sc, 1 - st,
      .seq he₁ (.seq he₂ (.ite_true (Crossing.eval_reg (by simp [s₂]) (hbit.trans_le (by omega))) (by omega) (.seq he₃ he₄))),
      ?_, hkeep, ?_, hbit, hiff, (hk₄.2 2800 (by decide)).trans hc₃, ht₄, hsc₃, hst₄,
      by simpa only [hone, ite_true] using hvc₃, by simpa only [hone, ite_true] using hvt₄, ?_⟩
    · omega
    · exact (hk₄.1 57 (by decide)).trans ((hk₃.1 57 (by decide)).trans (by simp [s₂]))
    · rw [hvc₃, hvt₄]
      exact neg_le_neg (le_of_lt (hiff.mp hone))
  · have hzero : flag = 0 := by omega
    refine ⟨s₂, u₁ + (2 + (1 + 1)), flag, sc, st,
      .seq he₁ (.seq he₂ (.ite_false (Crossing.eval_reg (by simp [s₂, hzero]) (Nat.two_pow_pos w)) (.skip s₂))),
      ?_, hkeep₂, by simp [s₂], hbit, hiff, hc₂, ht₂, hsc, hst,
      by simp only [hone, ite_false], by simp only [hone, ite_false], ?_⟩
    · omega
    · exact le_of_not_gt (fun hh => hone (hiff.mpr hh))

end GraphMinor.Compute
