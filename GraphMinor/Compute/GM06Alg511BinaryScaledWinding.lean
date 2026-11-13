module

public import GraphMinor.Compute.GM06Alg511BinaryRowArithmetic
public import GraphMinor.Compute.GM06Alg511BinaryPathCount
import Mathlib.Tactic

/-!
# The scaled winding numerator in binary

Use the path beginning at the first prescribed inner-cuff vertex.
Its scaled winding is the path count times its normalized edge-turn
sum plus its terminal outer-cuff index. Convert only those two
ordinary graph counts to binary, multiply and add with the verified
signed-row programs, and retain the original path-count register.
All turn magnitudes and intermediate winding values remain binary
rows. The cost is quadratic in the graph counts and turn-sum width.
This computes the numerator used by VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Convert an ordinary graph count to a positive signed binary
row, saving and restoring the original path-count register. -/
def gm06Alg511GraphCountRowProg (source dst : ℕ) : Cmd :=
  .seq (.assign 2920 (.reg 52))
    (.seq (.assign 52 (.reg source))
      (.seq gm06Alg511BinaryPathCountProg
        (.seq (.assign 52 (.reg 2920))
          (.seq (.assign 2402 (.const 0)) (gm06Alg511StoreBinaryRowProg 2600 dst 2402)))))

/-- The graph-count row is computed exactly in linear graph-count
time. The path count and every other register outside the explicit
conversion workspace are restored or retained. -/
theorem gm06Alg511GraphCountRowProg_exec {w : ℕ} (source dst : ℕ)
    (hsource : source ≠ 2920) (hdst : 2600 ≠ dst) (k n : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hkfit : k < 2 ^ w) (hnfit : n + 2 < 2 ^ w)
    (hk : s.regs 52 = k) (hn : s.regs source = n) :
    ∃ t u digits, Exec w (gm06Alg511GraphCountRowProg source dst) s t u ∧ u ≤ 100 * (n + 1) ∧
      Keeps [313, 2402, 2600, 2601, 2920] [2600, dst] s t ∧
      t.arrs dst = 0 :: digits ∧ digits.length = n + 1 ∧ (∀ d ∈ digits, d < 2) ∧
      gm06Alg511BinaryRowValue (0 :: digits) = (n : ℤ) := by
  let s₁ := s.setReg 2920 k
  let s₂ := s₁.setReg 52 n
  have he₁ : Exec w (.assign 2920 (.reg 52)) s s₁ 2 := .assign (Crossing.eval_reg hk hkfit)
  have hn₁ : s₁.regs source = n := (State.setReg_regs_ne _ _ hsource).trans hn
  have he₂ : Exec w (.assign 52 (.reg source)) s₁ s₂ 2 := .assign (Crossing.eval_reg hn₁ (by omega))
  obtain ⟨s₃, u₃, digits, he₃, ht₃, hk₃, hout₃, hlen, hbits, hval⟩ :=
    gm06Alg511BinaryPathCountProg_exec (w := w) n s₂ hw (by omega) (by simp [s₂])
  let s₄ := s₃.setReg 52 k
  let s₅ := s₄.setReg 2402 0
  have hbackup : s₃.regs 2920 = k := (hk₃.1 2920 (by decide)).trans (by simp [s₂, s₁])
  have he₄ : Exec w (.assign 52 (.reg 2920)) s₃ s₄ 2 := .assign (Crossing.eval_reg hbackup hkfit)
  have he₅ : Exec w (.assign 2402 (.const 0)) s₄ s₅ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  obtain ⟨t, u₆, he₆, ht₆, hk₆, hout⟩ := gm06Alg511StoreBinaryRowProg_exec (w := w) 2600 dst 2402 hdst 0 digits s₅
    (by omega) (by omega) (by decide) hbits hout₃ (by simp [s₅])
  let R := [52, 313, 2402, 2600, 2601, 2920]
  let A := [2600, dst]
  have hk₂ : Keeps R A s s₂ := ((Keeps.refl _ _ s).setReg (by simp [R]) k).setReg (by simp [R]) n
  have hk₅ : Keeps R A s s₅ := ((hk₂.trans hk₃ (by simp [R]) (by simp [A])).setReg (by simp [R]) k).setReg (by simp [R]) 0
  have hkeep : Keeps R A s t := hk₅.trans hk₆ (by simp [R]) (by simp [A])
  have hkFinal : t.regs 52 = k := (hk₆.1 52 (by decide)).trans (by simp [s₅, s₄])
  refine ⟨t, 2 + (2 + (u₃ + (2 + (2 + u₆)))), digits,
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ he₆)))), by omega,
    ⟨?_, hkeep.2⟩, hout, hlen, hbits, ?_⟩
  · intro r hr
    by_cases h52 : r = 52
    · subst r; exact hkFinal.trans hk.symm
    · exact hkeep.1 r (by simp only [R, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; tauto)
  · change (gm06Alg511BinaryValue digits : ℤ) = n
    exact congrArg (fun v : ℕ => (v : ℤ)) hval

/-- Convert the path count, multiply the retained turn sum, convert
the terminal cuff index and add it to the product. -/
def gm06Alg511BinaryScaledWindingProg : Cmd :=
  .seq (gm06Alg511GraphCountRowProg 52 2903)
    (.seq (gm06Alg511BinaryRowMultiplyProg 2903 2902 2903)
      (.seq (gm06Alg511GraphCountRowProg 46 2904)
        (gm06Alg511BinaryRowAddProg 2903 2904 2804)))

/-- The actual scaled-winding calculation gives precisely k times
the normalized turn sum plus the terminal index. The result is a
binary signed row, the original path count is retained, and no turn
magnitude or winding numerator is assumed to fit a word. -/
theorem gm06Alg511BinaryScaledWindingProg_exec {w : ℕ} (k j sign : ℕ) (acc : List ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : k + j + acc.length + 6 < 2 ^ w)
    (hsign : sign < 2) (hbits : ∀ d ∈ acc, d < 2)
    (hk : s.regs 52 = k) (hj : s.regs 46 = j) (hAcc : s.arrs 2902 = sign :: acc) :
    ∃ t u out sign', Exec w gm06Alg511BinaryScaledWindingProg s t u ∧
      u ≤ 2000 * (k + j + acc.length + 3) ^ 2 ∧
      Keeps [0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233, 2235, 2400, 2401, 2402, 2404, 2600, 2601, 2920]
        [2000, 2001, 2002, 2003, 2004, 2005, 2300, 2301, 2302, 2600, 2804, 2903, 2904] s t ∧
      t.arrs 2804 = sign' :: out ∧ sign' < 2 ∧ out.length ≤ k + j + acc.length + 3 ∧
      (∀ d ∈ out, d < 2) ∧
      gm06Alg511BinaryRowValue (sign' :: out) = (k : ℤ) * gm06Alg511BinaryRowValue (sign :: acc) + j := by
  obtain ⟨s₁, u₁, count, he₁, ht₁, hk₁, hc₁, hclen, hcbits, hcval⟩ :=
    gm06Alg511GraphCountRowProg_exec (w := w) 52 2903 (by decide) (by decide) k k s (by omega) (by omega) (by omega) hk hk
  obtain ⟨s₂, u₂, prod, prodSign, he₂, ht₂, hk₂, hp₂, hpsign, hplen, hpbits, hpval⟩ :=
    gm06Alg511BinaryRowMultiplyProg_exec (w := w) 2903 2902 2903 (by decide) (by decide) (by decide)
      count acc 0 sign s₁ hw (by omega) hcbits hbits (by decide) hsign hc₁ ((hk₁.2 2902 (by decide)).trans hAcc)
  obtain ⟨s₃, u₃, terminal, he₃, ht₃, hk₃, hj₃, hjlen, hjbits, hjval⟩ :=
    gm06Alg511GraphCountRowProg_exec (w := w) 46 2904 (by decide) (by decide) k j s₂ (by omega) (by omega) (by omega)
      ((hk₂.1 52 (by decide)).trans ((hk₁.1 52 (by decide)).trans hk))
      ((hk₂.1 46 (by decide)).trans ((hk₁.1 46 (by decide)).trans hj))
  obtain ⟨t, u₄, out, sign', he₄, ht₄, hk₄, hout, hsign', hlen, hbits', hval⟩ :=
    gm06Alg511BinaryRowAddProg_exec (w := w) 2903 2904 2804 (by decide) (by decide) (by decide)
      prod terminal prodSign 0 s₃ hw (by omega) hpbits hjbits hpsign (by decide)
      ((hk₃.2 2903 (by decide)).trans hp₂) hj₃
  let R := [0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233, 2235, 2400, 2401, 2402, 2404, 2600, 2601, 2920]
  let A := [2000, 2001, 2002, 2003, 2004, 2005, 2300, 2301, 2302, 2600, 2804, 2903, 2904]
  have hkeep : Keeps R A s t := (((hk₁.mono (by simp [R]) (by simp [A])).trans hk₂ (by simp [R]) (by simp [A])).trans hk₃
    (by simp [R]) (by simp [A])).trans hk₄ (by simp [R]) (by simp [A])
  refine ⟨t, u₁ + (u₂ + (u₃ + u₄)), out, sign', .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_,
    hkeep, hout, hsign', by omega, hbits', ?_⟩
  · have hm : max prod.length terminal.length ≤ k + j + acc.length + 2 := by omega
    have hwidth : count.length + acc.length + 1 ≤ k + j + acc.length + 3 := by omega
    have hp := Nat.mul_le_mul_left 700 (Nat.pow_le_pow_left hwidth 2)
    have hpos : 3 ≤ k + j + acc.length + 3 := by omega
    nlinarith only [ht₁, ht₂, ht₃, ht₄, hclen, hjlen, hplen, hm, hp, hpos]
  · rw [hval, hpval, hcval, hjval]

end GraphMinor.Compute
