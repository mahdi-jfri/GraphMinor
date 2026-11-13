module

public import GraphMinor.Compute.GM06Alg511BinarySubtract
public import GraphMinor.Compute.TwoPathsRename
import Mathlib.Tactic

/-!
# Absolute binary subtraction with its sign

The unsigned subtractor returns its low columns and a borrow.
When there is a borrow, run the same subtractor with the operands
exchanged. The second subtraction then has no borrow. This returns
the absolute difference as a binary row and retains the original
borrow as the sign of the difference. Both operands are preserved.
The two passes cost linear time in the supplied digit counts.
This is the signed-arithmetic layer for VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Exchange the two operand addresses and retain all other addresses. -/
def gm06Alg511BinaryOperandSwap (r : ℕ) : ℕ :=
  if r = 2000 then 2001 else if r = 2001 then 2000 else r

/-- Exchanging the operand addresses twice restores every address. -/
theorem gm06Alg511BinaryOperandSwap_involutive : Function.Involutive gm06Alg511BinaryOperandSwap := by
  intro r
  by_cases h0 : r = 2000
  · subst r; decide
  by_cases h1 : r = 2001
  · subst r; decide
  simp [gm06Alg511BinaryOperandSwap, h0, h1]

/-- Subtract with the two input rows exchanged. -/
def gm06Alg511BinaryReverseSubtractProg : Cmd :=
  renameCmd gm06Alg511BinaryOperandSwap gm06Alg511BinarySubtractProg

private theorem reverse_subtract_exec {w : ℕ} (a b : List ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max a.length b.length + 1 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2)
    (hA : s.arrs 2000 = a) (hB : s.arrs 2001 = b) :
    ∃ t u, Exec w gm06Alg511BinaryReverseSubtractProg s t u ∧
      u ≤ 100 + 120 * max a.length b.length ∧
      Keeps [0, 20, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232]
        [2002, 2003, 2004, 2005] s t ∧
      t.arrs 2005 = (gm06Alg511BinarySubtractColumns (max a.length b.length) b a).take (max a.length b.length) ∧
      t.regs 0 = gm06Alg511BinarySubtractBorrow (max a.length b.length) b a := by
  let f := gm06Alg511BinaryOperandSwap
  have hf : Function.Involutive f := gm06Alg511BinaryOperandSwap_involutive
  let ss := renameState f s
  have hAA : ss.arrs 2000 = b := by simpa [ss, renameState, f, gm06Alg511BinaryOperandSwap] using hB
  have hBB : ss.arrs 2001 = a := by simpa [ss, renameState, f, gm06Alg511BinaryOperandSwap] using hA
  obtain ⟨t, u, he, ht, hk, hout, hflag⟩ := gm06Alg511BinarySubtractProg_exec b a ss hw
    (by simpa only [max_comm] using hsize) hbbits habits hAA hBB
  have hss : renameState f ss = s := by
    apply State.ext
    · funext r; exact congrArg s.regs (hf r)
    · funext ar; exact congrArg s.arrs (hf ar)
  have he' : Exec w gm06Alg511BinaryReverseSubtractProg s (renameState f t) u := by
    simpa only [gm06Alg511BinaryReverseSubtractProg, f, hss] using exec_renameCmd hf he
  refine ⟨renameState f t, u, he', by simpa only [max_comm] using ht, ?_, ?_, ?_⟩
  · constructor
    · intro r hr
      have hh := hk.1 (f r) (by
        dsimp only [f, gm06Alg511BinaryOperandSwap]
        split_ifs <;> simp_all)
      exact hh.trans (congrArg s.regs (hf r))
    · intro ar har
      have hh := hk.2 (f ar) (by
        dsimp only [f, gm06Alg511BinaryOperandSwap]
        split_ifs <;> simp_all)
      exact hh.trans (congrArg s.arrs (hf ar))
  · simpa only [renameState_arrs, show f 2005 = 2005 by rfl, max_comm] using hout
  · simpa only [renameState_regs, show f 0 = 0 by rfl, max_comm] using hflag

/-- The absolute difference is in array 2005. Register 2404 retains
one exactly when the original difference is negative. -/
def gm06Alg511BinaryAbsSubtractProg : Cmd :=
  .seq gm06Alg511BinarySubtractProg
    (.seq (.assign 2404 (.reg 0))
      (.ite (.reg 2404) gm06Alg511BinaryReverseSubtractProg .skip))

/-- Actual absolute subtraction and its sign are exact and linear
in supplied digit count. Leading zeros and either encoding of zero
are allowed, and the original operand arrays are retained. -/
theorem gm06Alg511BinaryAbsSubtractProg_exec {w : ℕ} (a b : List ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max a.length b.length + 1 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2)
    (hA : s.arrs 2000 = a) (hB : s.arrs 2001 = b) :
    ∃ t u out flag, Exec w gm06Alg511BinaryAbsSubtractProg s t u ∧
      u ≤ 210 + 240 * max a.length b.length ∧
      Keeps [0, 20, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2404]
        [2002, 2003, 2004, 2005] s t ∧
      t.arrs 2005 = out ∧ t.regs 2404 = flag ∧ flag < 2 ∧
      (flag = 1 ↔ gm06Alg511BinaryValue a < gm06Alg511BinaryValue b) ∧
      out.length = max a.length b.length ∧ (∀ d ∈ out, d < 2) ∧
      (gm06Alg511BinaryValue out : ℤ) = if flag = 1 then
        (gm06Alg511BinaryValue b : ℤ) - gm06Alg511BinaryValue a
      else (gm06Alg511BinaryValue a : ℤ) - gm06Alg511BinaryValue b := by
  let n := max a.length b.length
  let flag := gm06Alg511BinarySubtractBorrow n a b
  have hflag : flag < 2 := by unfold flag gm06Alg511BinarySubtractBorrow; omega
  have hiff : flag = 1 ↔ gm06Alg511BinaryValue a < gm06Alg511BinaryValue b :=
    gm06Alg511BinarySubtractBorrow_eq_one_iff n a b (Nat.le_max_left _ _) (Nat.le_max_right _ _) habits hbbits
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, hout₁, hf₁⟩ := gm06Alg511BinarySubtractProg_exec a b s hw hsize habits hbbits hA hB
  let s₂ := s₁.setReg 2404 flag
  have he₂ : Exec w (.assign 2404 (.reg 0)) s₁ s₂ 2 :=
    .assign (Crossing.eval_reg hf₁ (hflag.trans_le (by omega)))
  let R := [0, 20, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2404]
  let A := [2002, 2003, 2004, 2005]
  have hkeep : Keeps R A s s₂ := (hk₁.mono (by simp [R]) (by simp [A])).setReg (by simp [R]) flag
  have hf₂ : s₂.regs 2404 = flag := by simp [s₂]
  have hev : (Expr.reg 2404).eval w s₂ = some flag := Crossing.eval_reg hf₂ (hflag.trans_le (by omega))
  by_cases hz : flag = 0
  · let out := (gm06Alg511BinarySubtractColumns n a b).take n
    have he₃ : Exec w (.ite (.reg 2404) gm06Alg511BinaryReverseSubtractProg .skip) s₂ s₂ 2 :=
      .ite_false (by simpa only [hz] using hev) (.skip _)
    refine ⟨s₂, u₁ + (2 + 2), out, flag, .seq he₁ (.seq he₂ he₃), by omega,
      hkeep, ?_, hf₂, hflag, hiff, ?_, ?_, ?_⟩
    · simpa only [s₂, State.setReg_arrs] using hout₁
    · simp only [out, List.length_take, gm06Alg511BinarySubtractColumns, gm06Alg511BinaryAddDigits_length]; omega
    · intro d hd
      exact gm06Alg511BinaryAddDigits_words n a _ 1 habits (gm06Alg511BinaryComplementDigits_words n b)
        (by decide) d (List.mem_of_mem_take hd)
    · have hh := gm06Alg511BinarySubtractColumns_balance n a b (Nat.le_max_left _ _) (Nat.le_max_right _ _) habits hbbits
      change gm06Alg511BinaryValue out + gm06Alg511BinaryValue b = gm06Alg511BinaryValue a + 2 ^ n * flag at hh
      rw [hz] at hh
      simp only [hz, show (0 : ℕ) ≠ 1 by decide, ite_false]
      omega
  · have hone : flag = 1 := by omega
    obtain ⟨t, u₃, he₃, ht₃, hk₃, hout₃, hf₃⟩ := reverse_subtract_exec a b s₂ hw hsize habits hbbits
      ((hkeep.2 2000 (by decide)).trans hA) ((hkeep.2 2001 (by decide)).trans hB)
    let out := (gm06Alg511BinarySubtractColumns n b a).take n
    have hreverse : gm06Alg511BinarySubtractBorrow n b a = 0 := by
      have hr := gm06Alg511BinarySubtractBorrow_eq_one_iff n b a (Nat.le_max_right _ _) (Nat.le_max_left _ _) hbbits habits
      have hlt := hiff.mp hone
      unfold gm06Alg511BinarySubtractBorrow at hr ⊢
      omega
    have he₄ : Exec w (.ite (.reg 2404) gm06Alg511BinaryReverseSubtractProg .skip) s₂ t (1 + u₃) :=
      .ite_true hev hz he₃
    refine ⟨t, u₁ + (2 + (1 + u₃)), out, flag, .seq he₁ (.seq he₂ he₄), by omega,
      hkeep.trans hk₃ (by simp [R]) (by simp [A]), hout₃,
      (hk₃.1 2404 (by decide)).trans hf₂, hflag, hiff, ?_, ?_, ?_⟩
    · simp only [out, List.length_take, gm06Alg511BinarySubtractColumns, gm06Alg511BinaryAddDigits_length]; omega
    · intro d hd
      exact gm06Alg511BinaryAddDigits_words n b _ 1 hbbits (gm06Alg511BinaryComplementDigits_words n a)
        (by decide) d (List.mem_of_mem_take hd)
    · have hh := gm06Alg511BinarySubtractColumns_balance n b a (Nat.le_max_right _ _) (Nat.le_max_left _ _) hbbits habits
      rw [hreverse] at hh
      simp only [hone, ite_true]
      change gm06Alg511BinaryValue out + gm06Alg511BinaryValue a = _ at hh
      omega

/-- Absolute subtraction returns the exact signed difference with
linear time and logarithmic words in the total supplied bit count. -/
theorem gm06Alg511BinaryAbsSubtract_computes :
    ComputesRelInTime
      (fun x : List Bool × List Bool => x.1.length + x.2.length + 1)
      (fun x s => s.arrs 2000 = x.1.map Bool.toNat ∧ s.arrs 2001 = x.2.map Bool.toNat)
      (fun x s => s.regs 2404 < 2 ∧
        (if s.regs 2404 = 1 then -(gm06Alg511BinaryValue (s.arrs 2005) : ℤ)
          else (gm06Alg511BinaryValue (s.arrs 2005) : ℤ)) =
            (gm06Alg511BinaryValue (x.1.map Bool.toNat) : ℤ) - gm06Alg511BinaryValue (x.2.map Bool.toNat) ∧
        (∀ d ∈ s.arrs 2005, d < 2) ∧ (s.arrs 2005).length = max x.1.length x.2.length)
      gm06Alg511BinaryAbsSubtractProg (fun n => n + 1) := by
  refine ⟨450, 2, by decide, by decide, ?_⟩
  intro x s hs
  let a := x.1.map Bool.toNat
  let b := x.2.map Bool.toNat
  let size := x.1.length + x.2.length + 1
  let w := wordSize 2 size
  have hw : 3 < 2 ^ w := by
    have hp := pow_lt_two_pow_wordSize (c := 2) (by decide) size
    have hb : 3 ≤ size + 2 := by dsimp only [size]; omega
    have hh : 3 < (size + 2) ^ 2 := by nlinarith only [hb]
    exact hh.trans hp
  have hsize : max a.length b.length + 1 < 2 ^ w :=
    lt_two_pow_wordSize_of_le (c := 2) (n := size) (by decide) (by
      dsimp only [a, b, size]
      simp only [List.length_map]
      omega)
  have bits (xs : List Bool) : ∀ d ∈ xs.map Bool.toNat, d < 2 := by
    intro d hd
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
    cases q <;> decide
  obtain ⟨t, u, out, flag, he, ht, _, hout, hf, hflag, _, hlen, hbits, hval⟩ :=
    gm06Alg511BinaryAbsSubtractProg_exec a b s hw hsize (bits x.1) (bits x.2) hs.1 hs.2
  refine ⟨t, u, he, ?_, by simpa only [hf] using hflag, ?_, ?_, ?_⟩
  · have hm : max a.length b.length ≤ size := by
      dsimp only [a, b, size]
      simp only [List.length_map]
      omega
    dsimp only [size] at *
    omega
  · rw [hout, hf]
    change (if flag = 1 then -(gm06Alg511BinaryValue out : ℤ) else (gm06Alg511BinaryValue out : ℤ)) =
      (gm06Alg511BinaryValue a : ℤ) - gm06Alg511BinaryValue b
    by_cases hf1 : flag = 1
    · simp only [hf1, ite_true] at hval ⊢
      omega
    · simpa only [hf1, ite_false] using hval
  · simpa only [hout] using hbits
  · simpa only [hout, a, b, List.length_map] using hlen

end GraphMinor.Compute
