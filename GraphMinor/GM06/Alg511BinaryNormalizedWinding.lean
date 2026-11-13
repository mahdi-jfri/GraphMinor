module

public import GraphMinor.GM06.Alg511BinaryLoopValues
public import GraphMinor.GM06.Alg511ReflectedStoredPaths
import GraphMinor.Compute.GM06Alg511BinaryLoad
import GraphMinor.Compute.GM06Alg511BinaryIntegral
import Mathlib.Tactic

/-!
# Binary normalization and the actual orientation values

Compute the scaled current and target rows, then run their signed
binary comparison and conditional sign reversal. Dividing by the
positive scale k times the denominator magnitude gives exactly the
original winding and target, or their negatives in the reflected
branch. The resulting current value is at most the target.

The proof retains the actual linkage, interpreting the reflection
bit by its reflected linkage. All original drawing/path/turn input
arrays survive for the subsequent geometric-data reflection. This
is the binary value part of VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Normalize the two comparison values and choose their orientation. -/
def gm06Alg511BinaryNormalizeOrientationProg : Cmd :=
  .seq gm06Alg511BinaryNormalizeProg gm06Alg511BinaryOrientationProg

end GraphMinor.Compute

namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Compute.TwoPaths GraphMinor.Surface

private theorem normalize_orientation_time (k a d current X T u v : ℕ)
    (hX : X ≤ current + d) (hT : T ≤ k + 1 + a)
    (hu : u ≤ 3000 * (k + a + d + current + 5) ^ 2)
    (hv : v ≤ 420 + 350 * (X + T + 1)) :
    u + v ≤ 10000 * (k + a + d + current + 5) ^ 2 := by
  let N := k + a + d + current + 5
  have hlinear : X + T + 1 ≤ N := by dsimp only [N]; omega
  have hN : 5 ≤ N := by dsimp only [N]; omega
  have hpow : N ≤ N ^ 2 := Nat.le_self_pow (by decide) N
  change u + v ≤ 10000 * N ^ 2
  change u ≤ 3000 * N ^ 2 at hu
  nlinarith only [hu, hv, hlinear, hN, hpow]

/-- Normalization and comparison compute the exact winding and
target in the selected orientation. Large values remain binary
rows throughout, and the time is quadratic in supplied digit counts
plus the ordinary graph path count. -/
theorem alg511_binary_normalize_orientation_exec {w : ℕ} (x : GM06Alg511BinaryInput)
    {G : Drawing ClosedCylinder} (hk : 0 < x.pathCount) (L : CylinderLinkage x.pathCount G)
    (sw : ℕ) (current : List ℕ) (s : State) (hden : x.denominator.value ≠ 0)
    (hL : L.HasTheta ((gm06Alg511BinaryRowValue (sw :: current) : ℝ) / x.pathCount))
    (hw : 3 < 2 ^ w) (hsize : x.pathCount + x.numerator.digits.length + x.denominator.digits.length + current.length + 8 < 2 ^ w)
    (hsw : sw < 2) (hbits : ∀ v ∈ current, v < 2)
    (hK : s.regs 52 = x.pathCount) (hA : s.arrs 2702 = x.numerator.words)
    (hD : s.arrs 2703 = x.denominator.words) (hW : s.arrs 2804 = sw :: current) :
    ∃ t u flag sc st current' target', Exec w gm06Alg511BinaryNormalizeOrientationProg s t u ∧
      u ≤ 10000 * (x.pathCount + x.numerator.digits.length + x.denominator.digits.length + current.length + 5) ^ 2 ∧
      t.regs 57 = flag ∧ flag < 2 ∧ t.arrs 2800 = sc :: current' ∧ t.arrs 2801 = st :: target' ∧
      t.arrs 2802 = 0 :: x.denominator.digits.map Bool.toNat ∧ sc < 2 ∧ st < 2 ∧
      current'.length ≤ current.length + x.denominator.digits.length ∧ target'.length ≤ x.pathCount + 1 + x.numerator.digits.length ∧
      (∀ v ∈ current', v < 2) ∧ (∀ v ∈ target', v < 2) ∧
      ((gm06Alg511BinaryRowValue (t.arrs 2800) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs) =
        if flag = 1 then -((gm06Alg511BinaryRowValue (sw :: current) : ℝ) / x.pathCount)
          else (gm06Alg511BinaryRowValue (sw :: current) : ℝ) / x.pathCount) ∧
      ((gm06Alg511BinaryRowValue (t.arrs 2801) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs) =
        if flag = 1 then -x.toWindingInput.drawing.target else x.toWindingInput.drawing.target) ∧
      ((gm06Alg511BinaryRowValue (t.arrs 2800) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs) ≤
        (gm06Alg511BinaryRowValue (t.arrs 2801) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs)) ∧
      (flag = 0 → L.HasTheta ((gm06Alg511BinaryRowValue (t.arrs 2800) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs))) ∧
      (flag = 1 → (alg511ReflectedStoredLinkage hk L).HasTheta
        ((gm06Alg511BinaryRowValue (t.arrs 2800) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs))) ∧
      Keeps [0, 20, 57, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233, 2235,
          2400, 2401, 2402, 2404, 2410, 2411, 2600, 2601, 2920]
        [2000, 2001, 2002, 2003, 2004, 2005, 2300, 2301, 2302, 2600, 2800, 2801, 2802, 2903] s t := by
  have bool_bit (b : Bool) : b.toNat < 2 := by cases b <;> decide
  have digits_bits (bs : List Bool) : ∀ v ∈ bs.map Bool.toNat, v < 2 := by
    intro v hv
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hv
    exact bool_bit b
  obtain ⟨s₁, u₁, ts, target, cs, cur, he₁, ht₁, hk₁, hinc₁, htrow₁, hcrow₁,
    hts, hcs, htlen, hclen, htbits, hcbits, htvalue, hcvalue⟩ := gm06Alg511BinaryNormalizeProg_exec (w := w)
      x.pathCount x.numerator.negative.toNat x.denominator.negative.toNat sw
      (x.numerator.digits.map Bool.toNat) (x.denominator.digits.map Bool.toNat) current s hw
      (by simpa only [List.length_map] using (show x.pathCount + x.numerator.digits.length + x.denominator.digits.length + current.length + 5 < 2 ^ w by omega))
      (bool_bit _) (bool_bit _) hsw (digits_bits _) (digits_bits _) hbits hK
      (by simpa only [GM06Alg511BinaryInteger.words_eq] using hA)
      (by simpa only [GM06Alg511BinaryInteger.words_eq] using hD) hW
  obtain ⟨t, u₂, flag, sc, st, he₂, ht₂, hk₂, hflag, hflagBit, _, hcurrent, htarget, hsc, hst, hcurrentVal, htargetVal, hle⟩ :=
    gm06Alg511BinaryOrientationProg_exec (w := w) cs ts cur target s₁ hw (by simp only [List.length_map] at htlen hclen; omega)
      hcs hts hcbits htbits hcrow₁ htrow₁
  have hDpos : 0 < x.denominator.value.natAbs := Int.natAbs_pos.mpr hden
  have hDvalue : gm06Alg511BinaryRowValue (0 :: x.denominator.digits.map Bool.toNat) = (x.denominator.value.natAbs : ℤ) := by
    rw [x.denominator.natAbs_value]
    rfl
  have hcurRatio : (gm06Alg511BinaryRowValue (cs :: cur) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs) =
      (gm06Alg511BinaryRowValue (sw :: current) : ℝ) / x.pathCount := by
    rw [hcvalue, hDvalue]
    exact alg511_binary_scaled_current _ _ _ hDpos
  have htargetRatio : (gm06Alg511BinaryRowValue (ts :: target) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs) =
      x.toWindingInput.drawing.target := by
    rw [htvalue, ← GM06Alg511BinaryInteger.words_eq, gm06Alg511BinaryRowValue_integer]
    exact alg511_binary_scaled_target x.pathCount x.numerator x.denominator hk
  have hcurrentRatio : (gm06Alg511BinaryRowValue (t.arrs 2800) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs) =
      if flag = 1 then -((gm06Alg511BinaryRowValue (sw :: current) : ℝ) / x.pathCount)
        else (gm06Alg511BinaryRowValue (sw :: current) : ℝ) / x.pathCount := by
    rw [hcurrent, hcurrentVal]
    split_ifs <;> simp only [Int.cast_neg, neg_div, hcurRatio]
  have htargetRatio' : (gm06Alg511BinaryRowValue (t.arrs 2801) : ℝ) / ((x.pathCount : ℝ) * x.denominator.value.natAbs) =
      if flag = 1 then -x.toWindingInput.drawing.target else x.toWindingInput.drawing.target := by
    rw [htarget, htargetVal]
    split_ifs <;> simp only [Int.cast_neg, neg_div, htargetRatio]
  let R := [0, 20, 57, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233, 2235,
    2400, 2401, 2402, 2404, 2410, 2411, 2600, 2601, 2920]
  let A := [2000, 2001, 2002, 2003, 2004, 2005, 2300, 2301, 2302, 2600, 2800, 2801, 2802, 2903]
  have hkeep : Keeps R A s t := (hk₁.mono (by simp [R]) (by simp [A])).trans hk₂ (by simp [R]) (by simp [A])
  refine ⟨t, u₁ + u₂, flag, sc, st, cur, target, .seq he₁ he₂, ?_, hflag, hflagBit, hcurrent, htarget,
    (hk₂.2 2802 (by decide)).trans hinc₁, hsc, hst, by simpa only [List.length_map] using hclen,
    by simpa only [List.length_map] using htlen, hcbits, htbits, hcurrentRatio, htargetRatio', ?_, ?_, ?_, hkeep⟩
  · simpa only [List.length_map] using normalize_orientation_time _ _ _ _ _ _ _ _ hclen htlen ht₁ ht₂
  · apply (alg511_binary_scaled_le_iff hk hDpos _ _).mpr
    simpa only [hcurrent, htarget] using hle
  · intro hzero
    rw [hcurrentRatio]
    simpa only [hzero, Nat.zero_ne_one, ite_false] using hL
  · intro hone
    rw [hcurrentRatio]
    simpa only [hone, ite_true] using alg511_reflectedStoredLinkage_hasTheta hk L hL

end GraphMinor.GM06
