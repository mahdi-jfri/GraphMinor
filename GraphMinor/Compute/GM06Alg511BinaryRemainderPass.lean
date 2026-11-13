module

public import GraphMinor.Compute.GM06Alg511BinarySubtract
public import GraphMinor.Compute.GM06Alg511BinaryMultiplyPass
import Mathlib.Tactic

/-!
# A binary long-division column

The previous remainder is smaller than the positive divisor.
Prepend the next input bit to its little-endian row, which doubles
its value and adds the bit. This tentative value is less than twice
the divisor. One unsigned subtraction therefore suffices: retain
the tentative row if it borrows, and retain the difference otherwise.
The result is the exact next remainder. All magnitude arithmetic
stays in binary rows. This supplies the integrality test of VI
(5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- One modular reduction suffices below twice a positive divisor. -/
theorem gm06Alg511BinaryRemainderColumn_value (r b digit : ℕ)
    (_hb : 0 < b) (hr : r < b) (hd : digit < 2) :
    (if digit + 2 * r < b then digit + 2 * r else digit + 2 * r - b) = (digit + 2 * r) % b := by
  by_cases hlt : digit + 2 * r < b
  · rw [ite_eq_left hlt, Nat.mod_eq_of_lt hlt]
  · rw [ite_eq_right hlt, Nat.mod_eq_sub_mod (by omega : b ≤ digit + 2 * r), Nat.mod_eq_of_lt (by omega)]

/-- Retained rows 2501 and 2502 hold the divisor and remainder.
Register 2531 holds the next input bit. The shifted row is built
by the verified zero-shift program and its first digit is replaced. -/
def gm06Alg511BinaryRemainderPassProg : Cmd :=
  .seq (gm06Alg511CopyRowProg 2502 2301)
    (.seq (.assign 2233 (.const 1))
      (.seq gm06Alg511BinaryShiftOperandProg
        (.seq (.write 2001 (.const 0) (.reg 2531))
          (.seq (gm06Alg511CopyRowProg 2001 2000)
            (.seq (gm06Alg511CopyRowProg 2501 2001)
              (.seq gm06Alg511BinarySubtractProg
                (.ite (.reg 0) (gm06Alg511CopyRowProg 2000 2502)
                  (gm06Alg511CopyRowProg 2005 2502))))))))

private theorem remainder_pass_frame {w : ℕ} {s t : State} {u : ℕ}
    (he : Exec w gm06Alg511BinaryRemainderPassProg s t u) :
    Keeps [0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233]
      [2000, 2001, 2002, 2003, 2004, 2005, 2301, 2502] s t := by
  have hr : gm06Alg511BinaryRemainderPassProg.writtenRegs ⊆
      ([0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233] : List ℕ).toFinset := by decide
  have ha : gm06Alg511BinaryRemainderPassProg.writtenArrs ⊆
      ([2000, 2001, 2002, 2003, 2004, 2005, 2301, 2502] : List ℕ).toFinset := by decide
  exact ⟨fun r hn => he.regs_eq_of_not_mem_writtenRegs (fun hm => hn (List.mem_toFinset.mp (hr hm))),
    fun a hn => he.arrs_eq_of_not_mem_writtenArrs (fun hm => hn (List.mem_toFinset.mp (ha hm)))⟩

/-- The actual long-division pass returns the exact remainder,
with binary digits, bounded width and linear digit-count time.
The retained divisor and loop-index registers are unchanged. -/
theorem gm06Alg511BinaryRemainderPassProg_exec {w : ℕ} (b acc : List ℕ) (digit : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max (acc.length + 1) b.length + 1 < 2 ^ w)
    (hbits : ∀ d ∈ b, d < 2) (haccBits : ∀ d ∈ acc, d < 2) (hdigit : digit < 2)
    (hbpos : 0 < gm06Alg511BinaryValue b) (hrem : gm06Alg511BinaryValue acc < gm06Alg511BinaryValue b)
    (hB : s.arrs 2501 = b) (hAcc : s.arrs 2502 = acc) (hDigit : s.regs 2531 = digit) :
    ∃ t u out, Exec w gm06Alg511BinaryRemainderPassProg s t u ∧
      u ≤ 400 + 400 * (acc.length + b.length + 1) ∧
      Keeps [0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233]
        [2000, 2001, 2002, 2003, 2004, 2005, 2301, 2502] s t ∧
      t.arrs 2502 = out ∧ out.length ≤ max (acc.length + 1) b.length ∧ (∀ d ∈ out, d < 2) ∧
      gm06Alg511BinaryValue out = (digit + 2 * gm06Alg511BinaryValue acc) % gm06Alg511BinaryValue b := by
  let a := digit :: acc
  let n := max a.length b.length
  let flag := gm06Alg511BinarySubtractBorrow n a b
  have haLen : a.length = acc.length + 1 := List.length_cons
  have haBits : ∀ d ∈ a, d < 2 := by intro d hd; rcases List.mem_cons.mp hd with rfl | hd; exact hdigit; exact haccBits d hd
  have haFit : a.length < 2 ^ w := by omega
  have hbFit : b.length < 2 ^ w := by omega
  have haccFit : acc.length < 2 ^ w := by omega
  have hacWords : ∀ d ∈ acc, d < 2 ^ w := fun d hd => (haccBits d hd).trans_le (by omega)
  have hbWords : ∀ d ∈ b, d < 2 ^ w := fun d hd => (hbits d hd).trans_le (by omega)
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, hacc₁⟩ := gm06Alg511CopyRowProg_exec 2502 2301 (by decide) acc s
    (by omega) haccFit hacWords hAcc
  let s₂ := s₁.setReg 2233 1
  have he₂ : Exec w (.assign 2233 (.const 1)) s₁ s₂ 2 := .assign (Crossing.eval_const (by omega))
  obtain ⟨s₃, u₃, he₃, ht₃, hk₃, hshift⟩ := gm06Alg511BinaryShiftOperandProg_exec (w := w) acc 1 s₂
    (by omega) (by omega) haccBits hacc₁ (by simp [s₂])
  have hshift' : s₃.arrs 2001 = 0 :: acc := by simpa using hshift
  have hd₃ : s₃.regs 2531 = digit := (hk₃.1 2531 (by decide)).trans
    ((State.setReg_regs_ne _ _ (by decide : (2531 : ℕ) ≠ 2233)).trans ((hk₁.1 2531 (by decide)).trans hDigit))
  let s₄ := s₃.writeArr 2001 0 digit
  have he₄ : Exec w (.write 2001 (.const 0) (.reg 2531)) s₃ s₄ 3 :=
    .write (Crossing.eval_const (Nat.two_pow_pos w)) (Crossing.eval_reg hd₃ (hdigit.trans_le (by omega)))
      (by rw [hshift']; exact Nat.zero_lt_succ _)
  have htenta : s₄.arrs 2001 = a := by change (s₃.arrs 2001).set 0 digit = a; rw [hshift']; rfl
  obtain ⟨s₅, u₅, he₅, ht₅, hk₅, hA₅⟩ := gm06Alg511CopyRowProg_exec 2001 2000 (by decide) a s₄
    (by omega) haFit (fun d hd => (haBits d hd).trans_le (by omega)) htenta
  have hB₅ : s₅.arrs 2501 = b := (hk₅.2 2501 (by decide)).trans
    ((State.writeArr_arrs_ne _ _ _ (by decide : (2501 : ℕ) ≠ 2001)).trans
      ((hk₃.2 2501 (by decide)).trans ((hk₁.2 2501 (by decide)).trans hB)))
  obtain ⟨s₆, u₆, he₆, ht₆, hk₆, hB₆⟩ := gm06Alg511CopyRowProg_exec 2501 2001 (by decide) b s₅
    (by omega) hbFit hbWords hB₅
  obtain ⟨st, u₇, he₇, ht₇, hk₇, hlow, hflag⟩ := gm06Alg511BinarySubtractProg_exec a b s₆ hw
    (by simpa only [haLen] using hsize) haBits hbits ((hk₆.2 2000 (by decide)).trans hA₅) hB₆
  have hf : flag < 2 := by unfold flag gm06Alg511BinarySubtractBorrow; omega
  have hiff : flag = 1 ↔ gm06Alg511BinaryValue a < gm06Alg511BinaryValue b :=
    gm06Alg511BinarySubtractBorrow_eq_one_iff n a b (Nat.le_max_left _ _) (Nat.le_max_right _ _) haBits hbits
  have heval : (Expr.reg 0).eval w st = some flag := Crossing.eval_reg hflag (hf.trans_le (by omega))
  have hASt : st.arrs 2000 = a := (hk₇.2 2000 (by decide)).trans ((hk₆.2 2000 (by decide)).trans hA₅)
  have finish (t : State) (v : ℕ)
      (he : Exec w (.ite (.reg 0) (gm06Alg511CopyRowProg 2000 2502) (gm06Alg511CopyRowProg 2005 2502)) st t v) :
      Exec w gm06Alg511BinaryRemainderPassProg s t (u₁ + (2 + (u₃ + (3 + (u₅ + (u₆ + (u₇ + v))))))) :=
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ (.seq he₇ he))))))
  by_cases hone : flag = 1
  · obtain ⟨t, v, he₈, ht₈, _, hout⟩ := gm06Alg511CopyRowProg_exec 2000 2502 (by decide) a st
      (by omega) haFit (fun d hd => (haBits d hd).trans_le (by omega)) hASt
    have hne : flag ≠ 0 := by omega
    have he := finish t (1 + v) (.ite_true heval hne he₈)
    refine ⟨t, _, a, he, ?_, remainder_pass_frame he, hout, Nat.le_max_left _ _, haBits, ?_⟩
    · have hm : n ≤ acc.length + b.length + 1 := by dsimp only [n]; rw [haLen]; omega
      omega
    · have hlt := hiff.mp hone
      change gm06Alg511BinaryValue a = gm06Alg511BinaryValue a % gm06Alg511BinaryValue b
      exact (Nat.mod_eq_of_lt hlt).symm
  · have hz : flag = 0 := by omega
    let out := (gm06Alg511BinarySubtractColumns n a b).take n
    have houtLen : out.length = n := by simp only [out, List.length_take, gm06Alg511BinarySubtractColumns, gm06Alg511BinaryAddDigits_length]; omega
    have houtBits : ∀ d ∈ out, d < 2 := by
      intro d hd
      exact gm06Alg511BinaryAddDigits_words n a _ 1 haBits (gm06Alg511BinaryComplementDigits_words n b)
        (by decide) d (List.mem_of_mem_take hd)
    obtain ⟨t, v, he₈, ht₈, _, hout⟩ := gm06Alg511CopyRowProg_exec (w := w) 2005 2502 (by decide) out st
      (by omega) (by rw [houtLen]; dsimp only [n]; omega)
      (fun d hd => (houtBits d hd).trans_le (by omega)) hlow
    have he := finish t (1 + v) (.ite_false (by simpa only [hz] using heval) he₈)
    refine ⟨t, _, out, he, ?_, remainder_pass_frame he, hout, by rw [houtLen]; rfl, houtBits, ?_⟩
    · have hm : n ≤ acc.length + b.length + 1 := by dsimp only [n]; rw [haLen]; omega
      omega
    · have balance := gm06Alg511BinarySubtractColumns_balance n a b
        (Nat.le_max_left _ _) (Nat.le_max_right _ _) haBits hbits
      change gm06Alg511BinaryValue out + gm06Alg511BinaryValue b = gm06Alg511BinaryValue a + 2 ^ n * flag at balance
      rw [hz] at balance
      have hv : gm06Alg511BinaryValue out = gm06Alg511BinaryValue a - gm06Alg511BinaryValue b := by omega
      rw [hv]
      have hge : ¬ gm06Alg511BinaryValue a < gm06Alg511BinaryValue b := by
        intro hlt
        have hh := hiff.mpr hlt
        omega
      have hm := gm06Alg511BinaryRemainderColumn_value (gm06Alg511BinaryValue acc) (gm06Alg511BinaryValue b) digit hbpos hrem hdigit
      simpa only [gm06Alg511BinaryValue, ← show gm06Alg511BinaryValue a = digit + 2 * gm06Alg511BinaryValue acc from rfl,
        hge, ite_false] using hm

end GraphMinor.Compute
