module

public import GraphMinor.Compute.GM02RecursiveTime
import Mathlib.Tactic.Ring

/-!
# Polynomial overhead per recursive parent

Bound each compact encoding by a quadratic in the parent's vertex bound.
The code overhead includes both side-call constructions, both return
paths, absent-code dispatch, and loop control. Multiply by the fixed
catalogue range and add separator entry. A coefficient depending only
on width bounds this entire non-recursive work by one fixed polynomial.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Exhaustive entry and its enclosing loop dispatch. -/
def gm02RecursiveBaseTime (q : ℕ) : ℕ :=
  (4 + 2 * ((4 * q) * (4 * q)) + 4 * q) *
    (4 * ((4 * q) * (4 * q) + 4 * q) + 10) + 10

/-- Constant part of the combined per-code work bound. -/
noncomputable def gm02RecursiveCodeTimeConstant (q : ℕ) : ℕ :=
  2441 + 336 * q + 146 * gm02RecursiveBoundaryBound q +
    16 * (gm02RecursiveCodeBound q + 1) + 8 * (gm02RecursiveBoundaryBound q + 1) +
    4 * gm02RecursiveCodeBound q

/-- Linear part of the combined per-code work bound. -/
def gm02RecursiveCodeTimeLinear (q : ℕ) : ℕ := 852 + 56 * gm02RecursiveBoundaryBound q

/-- Combined work for both side constructions and continuations at one code. -/
noncomputable def gm02RecursiveCodeTime (q n : ℕ) : ℕ :=
  gm02RecursiveCodeTimeConstant q + gm02RecursiveCodeTimeLinear q * n + 668 * n ^ 2

/-- The combined code bound is the sum of the five verified work bounds and loop-control allowance. -/
theorem gm02RecursiveCodeTime_eq (q n : ℕ) :
    let N := gm02RecursiveBoundaryBound q
    let K := gm02RecursiveCodeBound q
    let E := 3 + 2 * n ^ 2 + n
    gm02RecursiveCodeTime q n =
      (384 + 84 * q + 73 * N + n * (143 + 28 * N) + 166 * n ^ 2 +
        8 * (K + 1) + 4 * (N + 1) + 17 * (E + 2 * n) + 16 * E) +
      (51 * (E + 2 * n) + 63 * n + 168 * q + 73 * N + n * (143 + 28 * N) +
        166 * n ^ 2 + 8 * (K + 1) + 4 * (N + 1) + 16 * E + 750) +
      (34 * (E + 2 * n) + 63 * n + 84 * q + 390) +
      (34 * (E + 2 * n) + 301) + (12 + 4 * K) + 100 := by
  dsimp only [gm02RecursiveCodeTime, gm02RecursiveCodeTimeConstant, gm02RecursiveCodeTimeLinear]
  ring

/-- The verified work bounds remain below the combined code overhead for every smaller input. -/
theorem gm02RecursiveCodeTime_work_le (q n size index edges enc leftEnc rightEnc : ℕ)
    (hsize : size ≤ n) (hindex : index ≤ 3 * q) (hedges : edges ≤ n ^ 2)
    (henc : enc ≤ 3 + 2 * n ^ 2 + n)
    (hleft : leftEnc ≤ 3 + 2 * n ^ 2 + n) (hright : rightEnc ≤ 3 + 2 * n ^ 2 + n) :
    let N := gm02RecursiveBoundaryBound q
    let K := gm02RecursiveCodeBound q
    (384 + 28 * index + 73 * N + size * (143 + 28 * N) + 166 * edges +
      8 * (K + 1) + 4 * (N + 1) + 17 * (enc + 2 * size) + 16 * leftEnc) +
    (51 * (enc + 2 * size) + 63 * size + 56 * index + 73 * N + size * (143 + 28 * N) +
      166 * edges + 8 * (K + 1) + 4 * (N + 1) + 16 * rightEnc + 750) +
    (34 * (enc + 2 * size) + 63 * size + 28 * index + 390) +
    (34 * (enc + 2 * size) + 301) + 28 ≤ gm02RecursiveCodeTime q n := by
  have hlinear := Nat.mul_le_mul_right (143 + 28 * gm02RecursiveBoundaryBound q) hsize
  have hformula := gm02RecursiveCodeTime_eq q n
  dsimp only at hformula ⊢
  omega

/-- Width-dependent constant cost of the finite boundary catalogue lookup. -/
def gm02RecursiveCatalogueTime (q : ℕ) : ℕ :=
  (4 + 3 * gm02RecursiveBoundaryBound q) *
    (4 * (gm02RecursiveBoundaryBound q * gm02RecursiveBoundaryBound q +
      gm02RecursiveBoundaryBound q + 1) + 10)

/-- All non-recursive work of a parent, including every possible code. -/
noncomputable def gm02RecursiveLocalTime (q n : ℕ) : ℕ :=
  (10000 * (q + 1) ^ 2 + 155) * (n + 1) ^ (q + 3) + 150 * n +
    (600 * q + 470 + gm02RecursiveCatalogueTime q) +
    gm02RecursiveCodeBound q * gm02RecursiveCodeTime q n

/-- One coefficient covers both exhaustive entry and all non-base local work. -/
noncomputable def gm02RecursiveTimeCoefficient (q : ℕ) : ℕ :=
  gm02RecursiveBaseTime q + (10000 * (q + 1) ^ 2 + 155) + 150 +
    (600 * q + 470 + gm02RecursiveCatalogueTime q) +
    gm02RecursiveCodeBound q *
      (gm02RecursiveCodeTimeConstant q + gm02RecursiveCodeTimeLinear q + 668) + 1

private theorem quadratic_le_mul_pow (a b c n d : ℕ) (hd : 2 ≤ d) :
    a + b * n + c * n ^ 2 ≤ (a + b + c) * (n + 1) ^ d := by
  have h1 : 1 ≤ (n + 1) ^ d := Nat.one_le_pow d _ (by omega)
  have hn : n ≤ (n + 1) ^ d := (Nat.le_succ n).trans (Nat.le_self_pow (by omega) _)
  have hn2 : n ^ 2 ≤ (n + 1) ^ d :=
    (Nat.pow_le_pow_left (Nat.le_succ n) 2).trans (Nat.pow_le_pow_right (by omega) hd)
  calc
    a + b * n + c * n ^ 2 ≤ a * (n + 1) ^ d + b * (n + 1) ^ d + c * (n + 1) ^ d :=
      Nat.add_le_add (Nat.add_le_add (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left a h1)
        (Nat.mul_le_mul_left b hn)) (Nat.mul_le_mul_left c hn2)
    _ = _ := by ring

/-- The combined code overhead is quadratic, with a coefficient fixed by width. -/
theorem gm02RecursiveCodeTime_le (q n : ℕ) :
    gm02RecursiveCodeTime q n ≤
      (gm02RecursiveCodeTimeConstant q + gm02RecursiveCodeTimeLinear q + 668) * (n + 1) ^ (q + 3) :=
  quadratic_le_mul_pow _ _ _ _ _ (by omega)

/-- Every parent's total local work fits the overhead polynomial used in the recurrence. -/
theorem gm02RecursiveLocalTime_le (q n : ℕ) :
    gm02RecursiveLocalTime q n ≤ gm02RecursiveTimeCoefficient q * (n + 1) ^ (q + 3) := by
  let P := (n + 1) ^ (q + 3)
  let A := 10000 * (q + 1) ^ 2 + 155
  let B := 600 * q + 470 + gm02RecursiveCatalogueTime q
  let D := gm02RecursiveCodeTimeConstant q + gm02RecursiveCodeTimeLinear q + 668
  have h1 : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hn : n ≤ P := (Nat.le_succ n).trans (Nat.le_self_pow (by omega) _)
  have hlinear : 150 * n ≤ 150 * P := Nat.mul_le_mul_left _ hn
  have hconstant : B ≤ B * P := Nat.le_mul_of_pos_right _ h1
  have hcodes := Nat.mul_le_mul_left (gm02RecursiveCodeBound q) (gm02RecursiveCodeTime_le q n)
  have hsmall : gm02RecursiveLocalTime q n ≤ (A + 150 + B + gm02RecursiveCodeBound q * D) * P := by
    calc
      gm02RecursiveLocalTime q n = A * P + 150 * n + B + gm02RecursiveCodeBound q * gm02RecursiveCodeTime q n := rfl
      _ ≤ A * P + 150 * P + B * P + gm02RecursiveCodeBound q * (D * P) :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left hlinear _) hconstant) hcodes
      _ = _ := by ring
  apply hsmall.trans
  apply Nat.mul_le_mul_right P
  dsimp only [A, B, D, gm02RecursiveTimeCoefficient]
  omega

/-- The same coefficient covers the complete base prefix and is positive. -/
theorem gm02RecursiveTimeCoefficient_base (q : ℕ) :
    gm02RecursiveBaseTime q ≤ gm02RecursiveTimeCoefficient q ∧ 1 ≤ gm02RecursiveTimeCoefficient q := by
  unfold gm02RecursiveTimeCoefficient
  omega

end GraphMinor.Compute
