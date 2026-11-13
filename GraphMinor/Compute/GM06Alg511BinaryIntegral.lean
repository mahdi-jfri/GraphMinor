module

public import GraphMinor.Compute.GM06Alg511BinaryDivisibility
public import GraphMinor.Compute.GM06Alg511BinaryPathCount
public import GraphMinor.Compute.GM06Alg511Target
import Mathlib.Tactic

/-!
# The integrality check on binary target integers

VI (5.11), page 134, first checks that the path count times the
target is an integer. Read the numerator and denominator magnitude
rows from retained arrays 2700 and 2701. Convert the graph path
count, multiply the numerator magnitude by it, and decide binary
divisibility by the positive denominator magnitude. Signs do not
change this divisibility test. The returned Boolean is exactly
condition (5.10)(i), for either sign of the denominator.

All target arithmetic uses the verified binary programs. The
bound depends on the supplied digit counts and the path count,
which is bounded by the drawing vertex count. It does not depend
on the magnitudes of the target numerator or denominator.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The supplied magnitude row is exactly the absolute value of
the integer interpreted by its sign and bits. -/
theorem GM06Alg511BinaryInteger.natAbs_value (z : GM06Alg511BinaryInteger) :
    z.value.natAbs = gm06Alg511BinaryValue (z.digits.map Bool.toNat) := by
  cases z with
  | mk sign digits => cases sign <;> simp [GM06Alg511BinaryInteger.value]

/-- Convert the graph count, multiply its binary row with the
supplied numerator magnitude, then test denominator divisibility. -/
def gm06Alg511BinaryIntegralProg : Cmd :=
  .seq gm06Alg511BinaryPathCountProg
    (.seq (gm06Alg511CopyRowProg 2600 2000)
      (.seq (gm06Alg511CopyRowProg 2700 2001)
        (.seq gm06Alg511BinaryMultiplyProg
          (.seq (gm06Alg511CopyRowProg 2002 2000)
            (.seq (gm06Alg511CopyRowProg 2701 2001)
              gm06Alg511BinaryDivisibilityProg)))))

private theorem integral_frame {w : ℕ} {s t : State} {u : ℕ}
    (he : Exec w gm06Alg511BinaryIntegralProg s t u) :
    Keeps [0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233, 2235,
      2402, 2411, 2530, 2531, 2600, 2601]
      [2000, 2001, 2002, 2003, 2004, 2005, 2300, 2301, 2302, 2500, 2501, 2502, 2600] s t := by
  have hr : gm06Alg511BinaryIntegralProg.writtenRegs ⊆
      ([0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233, 2235,
        2402, 2411, 2530, 2531, 2600, 2601] : List ℕ).toFinset := by decide
  have ha : gm06Alg511BinaryIntegralProg.writtenArrs ⊆
      ([2000, 2001, 2002, 2003, 2004, 2005, 2300, 2301, 2302, 2500, 2501, 2502, 2600] : List ℕ).toFinset := by decide
  exact ⟨fun r hn => he.regs_eq_of_not_mem_writtenRegs (fun hm => hn (List.mem_toFinset.mp (hr hm))),
    fun a hn => he.arrs_eq_of_not_mem_writtenArrs (fun hm => hn (List.mem_toFinset.mp (ha hm)))⟩

/-- The actual arithmetic test of (5.10)(i) uses only binary
magnitude arithmetic and runs quadratically in graph count plus
supplied digit counts. Both retained target rows are unchanged. -/
theorem gm06Alg511BinaryIntegralProg_unsigned_exec {w : ℕ} (k : ℕ) (a b : List ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : k + a.length + b.length + 4 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2) (hbpos : 0 < gm06Alg511BinaryValue b)
    (hk : s.regs 52 = k) (hA : s.arrs 2700 = a) (hB : s.arrs 2701 = b) :
    ∃ t u flag, Exec w gm06Alg511BinaryIntegralProg s t u ∧
      u ≤ 2700 * (k + a.length + b.length + 2) ^ 2 ∧
      Keeps [0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233, 2235,
        2402, 2411, 2530, 2531, 2600, 2601]
        [2000, 2001, 2002, 2003, 2004, 2005, 2300, 2301, 2302, 2500, 2501, 2502, 2600] s t ∧
      t.regs 0 = flag ∧ flag < 2 ∧ (flag = 1 ↔ gm06Alg511BinaryValue b ∣ k * gm06Alg511BinaryValue a) := by
  have haFit : a.length < 2 ^ w := by omega
  have hbFit : b.length < 2 ^ w := by omega
  have aw : ∀ d ∈ a, d < 2 ^ w := fun d hd => (habits d hd).trans_le (by omega)
  have bw : ∀ d ∈ b, d < 2 ^ w := fun d hd => (hbbits d hd).trans_le (by omega)
  obtain ⟨s₁, u₁, count, he₁, ht₁, hk₁, hc₁, hclen, hcbits, hcval⟩ :=
    gm06Alg511BinaryPathCountProg_exec (w := w) k s (by omega) (by omega) hk
  have hcFit : count.length < 2 ^ w := by omega
  obtain ⟨s₂, u₂, he₂, ht₂, hk₂, hc₂⟩ := gm06Alg511CopyRowProg_exec 2600 2000 (by decide) count s₁
    (by omega) hcFit (fun d hd => (hcbits d hd).trans_le (by omega)) hc₁
  obtain ⟨s₃, u₃, he₃, ht₃, hk₃, ha₃⟩ := gm06Alg511CopyRowProg_exec 2700 2001 (by decide) a s₂
    (by omega) haFit aw ((hk₂.2 2700 (by decide)).trans ((hk₁.2 2700 (by decide)).trans hA))
  obtain ⟨s₄, u₄, prod, he₄, ht₄, hk₄, hp₄, hplen, hpbits, hpval⟩ :=
    gm06Alg511BinaryMultiplyProg_exec count a s₃ hw (by omega) hcbits habits
      ((hk₃.2 2000 (by decide)).trans hc₂) ha₃
  have hpFit : prod.length < 2 ^ w := by omega
  obtain ⟨s₅, u₅, he₅, ht₅, hk₅, hp₅⟩ := gm06Alg511CopyRowProg_exec 2002 2000 (by decide) prod s₄
    (by omega) hpFit (fun d hd => (hpbits d hd).trans_le (by omega)) hp₄
  have hb₅ : s₅.arrs 2701 = b := (hk₅.2 2701 (by decide)).trans ((hk₄.2 2701 (by decide)).trans
    ((hk₃.2 2701 (by decide)).trans ((hk₂.2 2701 (by decide)).trans ((hk₁.2 2701 (by decide)).trans hB))))
  obtain ⟨s₆, u₆, he₆, ht₆, hk₆, hb₆⟩ := gm06Alg511CopyRowProg_exec 2701 2001 (by decide) b s₅
    (by omega) hbFit bw hb₅
  obtain ⟨t, u₇, flag, he₇, ht₇, _, hflag, hbit, hiff⟩ :=
    gm06Alg511BinaryDivisibilityProg_exec prod b s₆ hw (by omega) hpbits hbbits hbpos
      ((hk₆.2 2000 (by decide)).trans hp₅) hb₆
  have he : Exec w gm06Alg511BinaryIntegralProg s t (u₁ + (u₂ + (u₃ + (u₄ + (u₅ + (u₆ + u₇)))))) :=
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ he₇)))))
  refine ⟨t, _, flag, he, ?_, integral_frame he, hflag, hbit, ?_⟩
  · let size := k + a.length + b.length + 2
    have hcsize : count.length + a.length + 1 ≤ size := by dsimp only [size]; omega
    have hpsize : prod.length + b.length + 1 ≤ size := by dsimp only [size]; omega
    have hmul := Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hcsize 2)
    have hdiv := Nat.mul_le_mul_left 2030 (Nat.pow_le_pow_left hpsize 2)
    have hpos : 2 ≤ size := by dsimp only [size]; omega
    dsimp only [size] at *
    nlinarith only [ht₁, ht₂, ht₃, ht₄, ht₅, ht₆, ht₇, hclen, hplen, hmul, hdiv, hpos]
  · simpa only [hpval, hcval] using hiff

/-- The bit returned on the two supplied signed target integers
is exactly condition (5.10)(i), including negative denominators. -/
theorem gm06Alg511BinaryIntegralProg_exec {w : ℕ} (k : ℕ)
    (a b : GM06Alg511BinaryInteger) (s : State) (hb : b.value ≠ 0)
    (hw : 3 < 2 ^ w) (hsize : k + a.digits.length + b.digits.length + 4 < 2 ^ w)
    (hk : s.regs 52 = k) (hA : s.arrs 2700 = a.digits.map Bool.toNat)
    (hB : s.arrs 2701 = b.digits.map Bool.toNat) :
    ∃ t u flag, Exec w gm06Alg511BinaryIntegralProg s t u ∧
      u ≤ 2700 * (k + a.digits.length + b.digits.length + 2) ^ 2 ∧
      t.regs 0 = flag ∧ flag < 2 ∧
      (flag = 1 ↔ ∃ m : ℤ, (k : ℝ) * ((a.value : ℝ) / (b.value : ℝ)) = m) := by
  have bits (xs : List Bool) : ∀ d ∈ xs.map Bool.toNat, d < 2 := by
    intro d hd
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hd
    cases q <;> decide
  have hbpos : 0 < gm06Alg511BinaryValue (b.digits.map Bool.toNat) := by
    rw [← b.natAbs_value]
    exact Int.natAbs_pos.mpr hb
  obtain ⟨t, u, flag, he, ht, _, hflag, hbit, hiff⟩ := gm06Alg511BinaryIntegralProg_unsigned_exec k
    (a.digits.map Bool.toNat) (b.digits.map Bool.toNat) s hw
    (by simpa only [List.length_map] using hsize) (bits _) (bits _) hbpos hk hA hB
  refine ⟨t, u, flag, he, by simpa only [List.length_map] using ht, hflag, hbit, ?_⟩
  have hdiv : gm06Alg511BinaryValue (b.digits.map Bool.toNat) ∣ k * gm06Alg511BinaryValue (a.digits.map Bool.toNat) ↔
      b.value ∣ (k : ℤ) * a.value := by
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_mul, Int.natAbs_natCast, a.natAbs_value, b.natAbs_value]
  exact hiff.trans (hdiv.trans (gm06Alg511_integral_iff k a.value b.value hb).symm)

/-- The target-integrality test has quadratic time and logarithmic
words in supplied target bits plus the graph path count. In a
cylinder instance the vertex count bounds that path count, so this
is a polynomial bound in the binary drawing input size. -/
theorem gm06Alg511BinaryIntegral_computes :
    ComputesRelInTime
      (fun x : ℕ × GM06Alg511BinaryInteger × GM06Alg511BinaryInteger =>
        x.1 + x.2.1.digits.length + x.2.2.digits.length + 4)
      (fun x s => x.2.2.value ≠ 0 ∧ s.regs 52 = x.1 ∧
        s.arrs 2700 = x.2.1.digits.map Bool.toNat ∧ s.arrs 2701 = x.2.2.digits.map Bool.toNat)
      (fun x s => s.regs 0 < 2 ∧ (s.regs 0 = 1 ↔
        ∃ m : ℤ, (x.1 : ℝ) * ((x.2.1.value : ℝ) / (x.2.2.value : ℝ)) = m))
      gm06Alg511BinaryIntegralProg (fun n => (n + 1) ^ 2) := by
  refine ⟨2700, 2, by decide, by decide, ?_⟩
  intro x s hs
  let size := x.1 + x.2.1.digits.length + x.2.2.digits.length + 4
  let w := wordSize 2 size
  have hw : 3 < 2 ^ w := by
    have hp := pow_lt_two_pow_wordSize (c := 2) (by decide) size
    have hb : 3 ≤ size + 2 := by dsimp only [size]; omega
    have hh : 3 < (size + 2) ^ 2 := by nlinarith only [hb]
    exact hh.trans hp
  have hsize : x.1 + x.2.1.digits.length + x.2.2.digits.length + 4 < 2 ^ w :=
    lt_two_pow_wordSize_of_le (c := 2) (n := size) (by decide) (by dsimp only [size]; omega)
  obtain ⟨t, u, flag, he, ht, hflag, hbit, hiff⟩ := gm06Alg511BinaryIntegralProg_exec x.1 x.2.1 x.2.2 s
    hs.1 hw hsize hs.2.1 hs.2.2.1 hs.2.2.2
  refine ⟨t, u, he, ?_, by simpa only [hflag] using hbit, ?_⟩
  · have hwidth : x.1 + x.2.1.digits.length + x.2.2.digits.length + 2 ≤ size + 1 := by
      dsimp only [size]; omega
    exact ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwidth 2))
  · simpa only [hflag] using hiff

end GraphMinor.Compute
