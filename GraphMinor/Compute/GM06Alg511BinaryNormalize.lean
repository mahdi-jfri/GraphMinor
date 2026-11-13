module

public import GraphMinor.Compute.GM06Alg511BinaryScaledWinding
import Mathlib.Tactic

/-!
# Binary values for the feasibility-loop comparison

Let W be the computed integer k times the initial linkage winding.
Replace the supplied denominator by its positive magnitude D. The
loop compares X = W D with T = k numerator sign(denominator), and
each successful successor adds D to X. These products are computed
by the verified binary multiplier. A negative denominator changes
only the sign of the target row.

This file verifies sign reversal and this preparation step of VI
(5.11), page 134. Integer magnitudes never enter ordinary registers.
The output widths and time depend on the supplied digit counts and
the ordinary graph path count.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Negate a retained signed binary row by changing its sign bit. -/
def gm06Alg511BinaryNegateRowProg (row : ℕ) : Cmd :=
  .write row (.const 0) (.op .sub (.const 1) (.read row (.const 0)))

/-- Sign reversal leaves the magnitude digits unchanged and negates
the exact integer, including either representation of zero. -/
theorem gm06Alg511BinaryNegateRowProg_exec {w : ℕ} (row sign : ℕ) (digits : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hs : sign < 2) (ha : s.arrs row = sign :: digits) :
    ∃ t, Exec w (gm06Alg511BinaryNegateRowProg row) s t 6 ∧ Keeps [] [row] s t ∧
      t.arrs row = (1 - sign) :: digits ∧ 1 - sign < 2 ∧
      gm06Alg511BinaryRowValue ((1 - sign) :: digits) = -gm06Alg511BinaryRowValue (sign :: digits) := by
  have hread : (Expr.read row (.const 0)).eval w s = some sign := by
    exact (Crossing.eval_read (a := row) (Crossing.eval_const (Nat.two_pow_pos w))
      (by rw [ha]; simp) (by simpa only [ha, List.getElem_cons_zero] using hs.trans_le (by omega))).trans (by simp [ha])
  let t := s.writeArr row 0 (1 - sign)
  have he : Exec w (gm06Alg511BinaryNegateRowProg row) s t 6 :=
    .write (Crossing.eval_const (Nat.two_pow_pos w)) (Crossing.eval_sub (Crossing.eval_const hw) hread)
      (by rw [ha]; simp)
  refine ⟨t, he, (Keeps.refl [] [row] s).writeArr (by simp) 0 _, by simp [t, ha], by omega, ?_⟩
  interval_cases sign <;> simp [gm06Alg511BinaryRowValue, gm06Alg511BinarySignedValue]

/-- Negate only when a computed Boolean condition is one. -/
def gm06Alg511BinaryNegateRowIfProg (row : ℕ) (cond : Expr) : Cmd :=
  .ite cond (gm06Alg511BinaryNegateRowProg row) .skip

/-- Conditional sign reversal is exact and has constant overhead
beyond the condition expression. It preserves every other array. -/
theorem gm06Alg511BinaryNegateRowIfProg_exec {w : ℕ} (row sign flag : ℕ) (digits : List ℕ)
    (cond : Expr) (s : State) (hw : 1 < 2 ^ w) (hs : sign < 2) (hf : flag < 2)
    (ha : s.arrs row = sign :: digits) (hc : cond.eval w s = some flag) :
    ∃ t u sign', Exec w (gm06Alg511BinaryNegateRowIfProg row cond) s t u ∧ u ≤ cond.cost + 6 ∧
      Keeps [] [row] s t ∧ t.arrs row = sign' :: digits ∧ sign' < 2 ∧
      gm06Alg511BinaryRowValue (sign' :: digits) =
        (if flag = 1 then -gm06Alg511BinaryRowValue (sign :: digits) else gm06Alg511BinaryRowValue (sign :: digits)) := by
  by_cases h : flag = 1
  · obtain ⟨t, he, hk, hr, hb, hv⟩ := gm06Alg511BinaryNegateRowProg_exec (w := w) row sign digits s hw hs ha
    exact ⟨t, cond.cost + 6, 1 - sign, .ite_true hc (by omega) he, by rfl, hk, hr, hb, by simpa only [h, ite_true] using hv⟩
  · have hz : flag = 0 := by omega
    exact ⟨s, cond.cost + 1, sign, .ite_false (by simpa only [hz] using hc) (.skip s),
      by omega, Keeps.refl _ _ s, ha, hs, by simp only [h, ite_false]⟩

/-- Copy the supplied denominator row and make its sign positive. -/
def gm06Alg511BinaryPositiveDenominatorProg : Cmd :=
  .seq (gm06Alg511CopyRowProg 2703 2802) (.write 2802 (.const 0) (.const 0))

/-- The positive denominator row retains exactly the supplied
magnitude digits, with linear copying cost and no other array change. -/
theorem gm06Alg511BinaryPositiveDenominatorProg_exec {w : ℕ} (sd : ℕ) (d : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hsize : d.length + 1 < 2 ^ w) (hs : sd < 2) (hb : ∀ digit ∈ d, digit < 2)
    (ha : s.arrs 2703 = sd :: d) :
    ∃ t u, Exec w gm06Alg511BinaryPositiveDenominatorProg s t u ∧ u ≤ 21 + 12 * d.length ∧
      Keeps [20] [2802] s t ∧ t.arrs 2802 = 0 :: d := by
  have hwords : ∀ v ∈ sd :: d, v < 2 ^ w := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hs.trans_le (by omega)
    · exact (hb v hv).trans_le (by omega)
  obtain ⟨st, u, he, ht, hk, hout⟩ := gm06Alg511CopyRowProg_exec (w := w) 2703 2802 (by decide) (sd :: d) s hw
    (by simpa only [List.length_cons] using hsize) hwords ha
  let t := st.writeArr 2802 0 0
  have hew : Exec w (.write 2802 (.const 0) (.const 0)) st t 3 :=
    .write (Crossing.eval_const (Nat.two_pow_pos w)) (Crossing.eval_const (Nat.two_pow_pos w)) (by rw [hout]; simp)
  exact ⟨t, u + 3, .seq he hew, by simp only [List.length_cons] at ht; omega,
    hk.writeArr (by simp) 0 0, by simp [t, hout]⟩

/-- Compute the positive increment D, scaled target T and scaled
current value X using binary rows only. -/
def gm06Alg511BinaryNormalizeProg : Cmd :=
  .seq gm06Alg511BinaryPositiveDenominatorProg
    (.seq (gm06Alg511GraphCountRowProg 52 2903)
      (.seq (gm06Alg511BinaryRowMultiplyProg 2903 2702 2801)
        (.seq (gm06Alg511BinaryNegateRowIfProg 2801 (.read 2703 (.const 0)))
          (gm06Alg511BinaryRowMultiplyProg 2804 2802 2800))))

/-- The loop's three binary rows have exact scaled values and
controlled widths. The supplied target pair and computed winding
row are retained. Time is quadratic in their supplied digit counts
plus the graph path count, with no magnitude word premise. -/
theorem gm06Alg511BinaryNormalizeProg_exec {w : ℕ} (k sn sd sw : ℕ) (a d current : List ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : k + a.length + d.length + current.length + 5 < 2 ^ w)
    (hsn : sn < 2) (hsd : sd < 2) (hsw : sw < 2)
    (ha : ∀ v ∈ a, v < 2) (hd : ∀ v ∈ d, v < 2) (hcurrent : ∀ v ∈ current, v < 2)
    (hk : s.regs 52 = k) (hA : s.arrs 2702 = sn :: a) (hD : s.arrs 2703 = sd :: d)
    (hW : s.arrs 2804 = sw :: current) :
    ∃ t u targetSign target currentSign current', Exec w gm06Alg511BinaryNormalizeProg s t u ∧
      u ≤ 3000 * (k + a.length + d.length + current.length + 5) ^ 2 ∧
      Keeps [20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2233, 2235, 2400, 2401, 2402, 2600, 2601, 2920]
        [2000, 2001, 2002, 2300, 2301, 2302, 2600, 2800, 2801, 2802, 2903] s t ∧
      t.arrs 2802 = 0 :: d ∧ t.arrs 2801 = targetSign :: target ∧ t.arrs 2800 = currentSign :: current' ∧
      targetSign < 2 ∧ currentSign < 2 ∧ target.length ≤ k + 1 + a.length ∧ current'.length ≤ current.length + d.length ∧
      (∀ v ∈ target, v < 2) ∧ (∀ v ∈ current', v < 2) ∧
      gm06Alg511BinaryRowValue (targetSign :: target) =
        (if sd = 1 then -((k : ℤ) * gm06Alg511BinaryRowValue (sn :: a)) else (k : ℤ) * gm06Alg511BinaryRowValue (sn :: a)) ∧
      gm06Alg511BinaryRowValue (currentSign :: current') =
        gm06Alg511BinaryRowValue (sw :: current) * gm06Alg511BinaryRowValue (0 :: d) := by
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, hinc₁⟩ := gm06Alg511BinaryPositiveDenominatorProg_exec (w := w) sd d s
    (by omega) (by omega) hsd hd hD
  obtain ⟨s₂, u₂, count, he₂, ht₂, hk₂, hcount₂, hclen, hcbits, hcvalue⟩ :=
    gm06Alg511GraphCountRowProg_exec (w := w) 52 2903 (by decide) (by decide) k k s₁
      (by omega) (by omega) (by omega) ((hk₁.1 52 (by decide)).trans hk) ((hk₁.1 52 (by decide)).trans hk)
  obtain ⟨s₃, u₃, target, prodSign, he₃, ht₃, hk₃, htarget₃, hpSign, hpLen, hpBits, hpVal⟩ :=
    gm06Alg511BinaryRowMultiplyProg_exec (w := w) 2903 2702 2801 (by decide) (by decide) (by decide)
      count a 0 sn s₂ hw (by omega) hcbits ha (by decide) hsn hcount₂
        ((hk₂.2 2702 (by decide)).trans ((hk₁.2 2702 (by decide)).trans hA))
  have hden₃ : s₃.arrs 2703 = sd :: d :=
    (hk₃.2 2703 (by decide)).trans ((hk₂.2 2703 (by decide)).trans ((hk₁.2 2703 (by decide)).trans hD))
  have hcond : (Expr.read 2703 (.const 0)).eval w s₃ = some sd := by
    exact (Crossing.eval_read (a := 2703) (Crossing.eval_const (Nat.two_pow_pos w))
      (by rw [hden₃]; simp) (by simpa only [hden₃, List.getElem_cons_zero] using hsd.trans_le (by omega))).trans (by simp [hden₃])
  obtain ⟨s₄, u₄, targetSign, he₄, ht₄, hk₄, htarget₄, htSign, htVal⟩ :=
    gm06Alg511BinaryNegateRowIfProg_exec (w := w) 2801 prodSign sd target (.read 2703 (.const 0)) s₃
      (by omega) hpSign hsd htarget₃ hcond
  have hinc₄ : s₄.arrs 2802 = 0 :: d := (hk₄.2 2802 (by decide)).trans
    ((hk₃.2 2802 (by decide)).trans ((hk₂.2 2802 (by decide)).trans hinc₁))
  have hwinding₄ : s₄.arrs 2804 = sw :: current := (hk₄.2 2804 (by decide)).trans
    ((hk₃.2 2804 (by decide)).trans ((hk₂.2 2804 (by decide)).trans ((hk₁.2 2804 (by decide)).trans hW)))
  obtain ⟨t, u₅, current', currentSign, he₅, ht₅, hk₅, hcurrent₅, hcSign, hcLen, hcBits, hcVal⟩ :=
    gm06Alg511BinaryRowMultiplyProg_exec (w := w) 2804 2802 2800 (by decide) (by decide) (by decide)
      current d sw 0 s₄ hw (by omega) hcurrent hd hsw (by decide) hwinding₄ hinc₄
  let R := [20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2233, 2235, 2400, 2401, 2402, 2600, 2601, 2920]
  let A := [2000, 2001, 2002, 2300, 2301, 2302, 2600, 2800, 2801, 2802, 2903]
  have hkeep : Keeps R A s t := ((((hk₁.mono (by simp [R]) (by simp [A])).trans hk₂ (by simp [R]) (by simp [A])).trans hk₃
    (by simp [R]) (by simp [A])).trans hk₄ (by simp [R]) (by simp [A])).trans hk₅ (by simp [R]) (by simp [A])
  refine ⟨t, u₁ + (u₂ + (u₃ + (u₄ + u₅))), targetSign, target, currentSign, current',
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ he₅))), ?_, hkeep,
    (hk₅.2 2802 (by decide)).trans hinc₄, (hk₅.2 2801 (by decide)).trans htarget₄, hcurrent₅,
    htSign, hcSign, by omega, hcLen, hpBits, hcBits, ?_, hcVal⟩
  · have ht₄' : u₄ ≤ 8 := ht₄
    let size := k + a.length + d.length + current.length + 5
    have hs₃ : count.length + a.length + 1 ≤ size := by dsimp only [size]; omega
    have hs₅ : current.length + d.length + 1 ≤ size := by dsimp only [size]; omega
    have hm₃ := Nat.mul_le_mul_left 700 (Nat.pow_le_pow_left hs₃ 2)
    have hm₅ := Nat.mul_le_mul_left 700 (Nat.pow_le_pow_left hs₅ 2)
    have hpos : 5 ≤ size := by dsimp only [size]; omega
    dsimp only [size] at *
    nlinarith only [ht₁, ht₂, ht₃, ht₄', ht₅, hm₃, hm₅, hpos]
  · rw [htVal, hpVal, hcvalue]

end GraphMinor.Compute
