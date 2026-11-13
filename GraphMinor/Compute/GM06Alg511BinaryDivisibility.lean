module

public import GraphMinor.Compute.GM06Alg511BinaryRemainder
public import GraphMinor.Compute.GM06Alg511BinaryCompare
import Mathlib.Tactic

/-!
# Divisibility of supplied binary integers

Compute the binary remainder, then scan its magnitude for a nonzero
bit. Return one exactly when the remainder is zero. The temporary
negative sign makes the existing negativity scan test for a nonzero
magnitude. The final complement turns that test into divisibility.
The program retains both operand rows. Its quadratic bound counts
supplied bits and never assumes their interpreted values fit words.
This implements the arithmetic test needed in VI (5.10)(i) and
(5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Decide divisibility by a positive binary divisor, using the
actual long-division and zero-scan programs. -/
def gm06Alg511BinaryDivisibilityProg : Cmd :=
  .seq gm06Alg511BinaryRemainderProg
    (.seq (.assign 2402 (.const 1))
      (.seq gm06Alg511BinaryNegativeProg (.assign 0 (.op .sub (.const 1) (.reg 0)))))

/-- The actual binary divisibility program returns one exactly
when the positive divisor divides the numerator. It restores both
operands and has quadratic digit-count time. -/
theorem gm06Alg511BinaryDivisibilityProg_exec {w : ℕ} (a b : List ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : a.length + b.length + 2 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2)
    (hbpos : 0 < gm06Alg511BinaryValue b) (hA : s.arrs 2000 = a) (hB : s.arrs 2001 = b) :
    ∃ t u flag, Exec w gm06Alg511BinaryDivisibilityProg s t u ∧
      u ≤ 2030 * (a.length + b.length + 1) ^ 2 ∧
      Keeps [0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233, 2402, 2411, 2530, 2531]
        [2002, 2003, 2004, 2005, 2301, 2500, 2501, 2502] s t ∧
      t.regs 0 = flag ∧ flag < 2 ∧ (flag = 1 ↔ gm06Alg511BinaryValue b ∣ gm06Alg511BinaryValue a) := by
  obtain ⟨st, u, out, he, ht, hk, hout, hlen, hbits, hval⟩ :=
    gm06Alg511BinaryRemainderProg_exec a b s hw hsize habits hbbits hbpos hA hB
  let s₁ := st.setReg 2402 1
  have he₁ : Exec w (.assign 2402 (.const 1)) st s₁ 2 := .assign (Crossing.eval_const (by omega))
  obtain ⟨su, v, nf, he₂, ht₂, hk₂, hnf, hnfBit, hiff⟩ :=
    gm06Alg511BinaryNegativeProg_exec (w := w) out 1 s₁ (by omega) (by omega) (by decide) hbits hout (by simp [s₁])
  let flag := 1 - nf
  let t := su.setReg 0 flag
  have he₃ : Exec w (.assign 0 (.op .sub (.const 1) (.reg 0))) su t 4 :=
    .assign (Crossing.eval_sub (Crossing.eval_const (by omega)) (Crossing.eval_reg hnf (hnfBit.trans_le (by omega))))
  let R := [0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233, 2402, 2411, 2530, 2531]
  let A := [2002, 2003, 2004, 2005, 2301, 2500, 2501, 2502]
  have hk₁ : Keeps R A s s₁ := (hk.mono (by simp [R]) (by simp [A])).setReg (by simp [R]) 1
  have hkFinal : Keeps R A s t := (hk₁.trans hk₂ (by simp [R]) (by simp [A])).setReg (by simp [R]) flag
  refine ⟨t, u + (2 + (v + 4)), flag, .seq he (.seq he₁ (.seq he₂ he₃)), ?_, hkFinal,
    by simp [t], by dsimp only [flag]; omega, ?_⟩
  · have hp : 1 ≤ a.length + b.length + 1 := by omega
    nlinarith only [ht, ht₂, hlen, hp]
  · have hn : nf = 1 ↔ gm06Alg511BinaryValue out ≠ 0 := by
      simpa only [gm06Alg511BinarySignedValue, ite_true, neg_lt_zero, Int.natCast_pos, Nat.pos_iff_ne_zero] using hiff
    have hz : flag = 1 ↔ gm06Alg511BinaryValue out = 0 := by dsimp only [flag]; omega
    rw [hval, ← Nat.dvd_iff_mod_eq_zero] at hz
    exact hz

/-- Divisibility has quadratic time in total supplied bit count
with logarithmic words for every positive binary divisor. -/
theorem gm06Alg511BinaryDivisibility_computes :
    ComputesRelInTime
      (fun x : List Bool × List Bool => x.1.length + x.2.length + 2)
      (fun x s => s.arrs 2000 = x.1.map Bool.toNat ∧ s.arrs 2001 = x.2.map Bool.toNat ∧
        0 < gm06Alg511BinaryValue (x.2.map Bool.toNat))
      (fun x s => s.regs 0 < 2 ∧ (s.regs 0 = 1 ↔
        gm06Alg511BinaryValue (x.2.map Bool.toNat) ∣ gm06Alg511BinaryValue (x.1.map Bool.toNat)))
      gm06Alg511BinaryDivisibilityProg (fun n => (n + 1) ^ 2) := by
  refine ⟨2030, 2, by decide, by decide, ?_⟩
  intro x s hs
  let a := x.1.map Bool.toNat
  let b := x.2.map Bool.toNat
  let size := x.1.length + x.2.length + 2
  let w := wordSize 2 size
  have hw : 3 < 2 ^ w := by
    have hp := pow_lt_two_pow_wordSize (c := 2) (by decide) size
    have hb : 3 ≤ size + 2 := by dsimp only [size]; omega
    have hh : 3 < (size + 2) ^ 2 := by nlinarith only [hb]
    exact hh.trans hp
  have hsize : a.length + b.length + 2 < 2 ^ w :=
    lt_two_pow_wordSize_of_le (c := 2) (n := size) (by decide) (by simp [a, b, size])
  have bits (xs : List Bool) : ∀ d ∈ xs.map Bool.toNat, d < 2 := by
    intro d hd
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
    cases q <;> decide
  obtain ⟨t, u, flag, he, ht, _, hflag, hbits, hiff⟩ :=
    gm06Alg511BinaryDivisibilityProg_exec a b s hw hsize (bits x.1) (bits x.2) hs.2.2 hs.1 hs.2.1
  refine ⟨t, u, he, ?_, by simpa only [hflag] using hbits, ?_⟩
  · have heq : a.length + b.length + 1 ≤ size + 1 := by simp [a, b, size]
    exact ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left heq 2))
  · simpa only [hflag] using hiff

end GraphMinor.Compute
