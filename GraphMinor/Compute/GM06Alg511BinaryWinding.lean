module

public import GraphMinor.Compute.GM06Alg511BinaryTurnSum
public import GraphMinor.Compute.GM06Alg511BinaryScaledWinding
import Mathlib.Tactic

/-!
# The full binary winding calculation

Sum the supplied normalized edge turns along the stored first path,
then multiply by the path count and add the terminal cuff index.
For the path starting at source index zero this is the integer
numerator of its winding over the path count. The proof composes
the actual binary scans and retains the original turn code, path
and graph counts. Its quadratic bound counts supplied bits, path
length and graph counts, never target or turn magnitudes. This is
the arithmetic phase of VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Compute the first path's turn sum and its scaled winding
numerator as binary signed rows. -/
def gm06Alg511BinaryWindingProg : Cmd :=
  .seq gm06Alg511BinaryTurnSumProg gm06Alg511BinaryScaledWindingProg

/-- The complete actual binary winding phase computes precisely
k times the oriented turn sum plus the terminal cuff index. -/
theorem gm06Alg511BinaryWindingProg_exec {w : ℕ} (k j : ℕ)
    (turns : List GM06Alg511BinaryInteger) (darts : List ℕ) (s : State) (hw : 3 < 2 ^ w)
    (hsize : k + j + darts.length + 2 * (gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)).length + 10 < 2 ^ w)
    (hdarts : ∀ d ∈ darts, d < 2 * turns.length)
    (hTurns : s.arrs 2900 = gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)) (hPath : s.arrs 12 = darts)
    (hk : s.regs 52 = k) (hj : s.regs 46 = j) :
    ∃ t u out sign, Exec w gm06Alg511BinaryWindingProg s t u ∧
      u ≤ 4000 * (k + j + darts.length + (gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)).length + 3) ^ 2 ∧
      Keeps [0, 7, 8, 9, 11, 20, 31, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233, 2235, 2400, 2401, 2402, 2404, 2600, 2601, 2910, 2911, 2920]
        [2000, 2001, 2002, 2003, 2004, 2005, 2300, 2301, 2302, 2600, 2804, 2901, 2902, 2903, 2904] s t ∧
      t.arrs 2804 = sign :: out ∧ sign < 2 ∧
      out.length ≤ k + j + darts.length + (gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)).length + 3 ∧
      (∀ d ∈ out, d < 2) ∧ gm06Alg511BinaryRowValue (sign :: out) =
        (k : ℤ) * (darts.map (gm06Alg511BinaryDartTurn turns)).sum + j := by
  let code := gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)
  change k + j + darts.length + 2 * code.length + 10 < 2 ^ w at hsize
  obtain ⟨s₁, u₁, acc, accSign, he₁, ht₁, hk₁, hacc, haccSign, haccLen, haccBits, haccVal⟩ :=
    gm06Alg511BinaryTurnSumProg_exec turns darts s hw (by change darts.length + 2 * code.length + 3 < 2 ^ w; omega) hdarts hTurns hPath
  change acc.length ≤ darts.length + code.length at haccLen
  obtain ⟨t, u₂, out, sign, he₂, ht₂, hk₂, hout, hsign, hlen, hbits, hval⟩ :=
    gm06Alg511BinaryScaledWindingProg_exec k j accSign acc s₁ hw (by omega) haccSign haccBits
      ((hk₁.1 52 (by decide)).trans hk) ((hk₁.1 46 (by decide)).trans hj) hacc
  let R := [0, 7, 8, 9, 11, 20, 31, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233, 2235, 2400, 2401, 2402, 2404, 2600, 2601, 2910, 2911, 2920]
  let A := [2000, 2001, 2002, 2003, 2004, 2005, 2300, 2301, 2302, 2600, 2804, 2901, 2902, 2903, 2904]
  have hkeep : Keeps R A s t := (hk₁.mono (by simp [R]) (by simp [A])).trans hk₂ (by simp [R]) (by simp [A])
  refine ⟨t, u₁ + u₂, out, sign, .seq he₁ he₂, ?_, hkeep, hout, hsign, by change out.length ≤ k + j + darts.length + code.length + 3; omega, hbits, ?_⟩
  · have hw₁ : darts.length + code.length + 1 ≤ k + j + darts.length + code.length + 3 := by omega
    have hw₂ : k + j + acc.length + 3 ≤ k + j + darts.length + code.length + 3 := by omega
    have hp₁ := Nat.mul_le_mul_left 2000 (Nat.pow_le_pow_left hw₁ 2)
    have hp₂ := Nat.mul_le_mul_left 2000 (Nat.pow_le_pow_left hw₂ 2)
    change u₁ ≤ 2000 * (darts.length + code.length + 1) ^ 2 at ht₁
    nlinarith only [ht₁, ht₂, hp₁, hp₂]
  · rw [hval, haccVal]

/-- The complete binary winding phase has quadratic time and
logarithmic words in supplied code/path lengths plus graph counts. -/
theorem gm06Alg511BinaryWinding_computes :
    ComputesRelInTime
      (fun x : (ℕ × ℕ) × (List GM06Alg511BinaryInteger × List ℕ) =>
        x.1.1 + x.1.2 + x.2.2.length + 2 * (gm06EncodeRows (x.2.1.map GM06Alg511BinaryInteger.words)).length + 10)
      (fun x s => s.arrs 2900 = gm06EncodeRows (x.2.1.map GM06Alg511BinaryInteger.words) ∧
        s.arrs 12 = x.2.2 ∧ s.regs 52 = x.1.1 ∧ s.regs 46 = x.1.2 ∧ ∀ d ∈ x.2.2, d < 2 * x.2.1.length)
      (fun x s => ∃ out sign, s.arrs 2804 = sign :: out ∧ sign < 2 ∧
        out.length ≤ x.1.1 + x.1.2 + x.2.2.length + (gm06EncodeRows (x.2.1.map GM06Alg511BinaryInteger.words)).length + 3 ∧
        (∀ d ∈ out, d < 2) ∧ gm06Alg511BinaryRowValue (s.arrs 2804) =
          (x.1.1 : ℤ) * (x.2.2.map (gm06Alg511BinaryDartTurn x.2.1)).sum + x.1.2)
      gm06Alg511BinaryWindingProg (fun n => (n + 1) ^ 2) := by
  refine ⟨4000, 2, by decide, by decide, ?_⟩
  intro x s hs
  let size := x.1.1 + x.1.2 + x.2.2.length + 2 * (gm06EncodeRows (x.2.1.map GM06Alg511BinaryInteger.words)).length + 10
  let w := wordSize 2 size
  have hw : 3 < 2 ^ w := by
    have hp := pow_lt_two_pow_wordSize (c := 2) (by decide) size
    have hb : 3 ≤ size + 2 := by dsimp only [size]; omega
    have hh : 3 < (size + 2) ^ 2 := by nlinarith only [hb]
    exact hh.trans hp
  have hsize : size < 2 ^ w := lt_two_pow_wordSize_of_le (c := 2) (n := size) (by decide) (by omega)
  obtain ⟨t, u, out, sign, he, ht, _, hout, hsign, hlen, hbits, hval⟩ :=
    gm06Alg511BinaryWindingProg_exec x.1.1 x.1.2 x.2.1 x.2.2 s hw hsize hs.2.2.2.2 hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1
  refine ⟨t, u, he, ?_, out, sign, hout, hsign, hlen, hbits, ?_⟩
  · have hwidth : x.1.1 + x.1.2 + x.2.2.length + (gm06EncodeRows (x.2.1.map GM06Alg511BinaryInteger.words)).length + 3 ≤ size + 1 := by
      dsimp only [size]; omega
    exact ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwidth 2))
  · simpa only [hout] using hval

end GraphMinor.Compute
