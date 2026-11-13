module

public import GraphMinor.Compute.GM02RecursiveMemory
public import GraphMinor.GM02.AlternatingRecurrence
import Mathlib.Tactic.Ring

/-!
# An explicit bound for the alternating recursive running time

Count a fixed polynomial overhead per parent and at most two calls for
each catalogue code. A1 uses the three-quarter vertex bound for A2,
while A2 uses A1 at the same bound. Twice the bound plus the phase bit
makes this numerical recursion terminate. Its two phase restrictions
satisfy the paper's recurrences and hence grow polynomially.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.GM02

private theorem next_measure_lt (m q : ℕ) (h : 4 * q < m / 2) :
    (if m % 2 = 0 then 2 * (3 * (m / 2) / 4) + 1 else 2 * (m / 2)) < m := by
  have hm := Nat.mod_lt m (by decide : 0 < 2)
  split_ifs with heven
  · have hshrink : 3 * (m / 2) / 4 < m / 2 := by omega
    omega
  · omega

/-- Numerical upper bound with fixed polynomial overhead and the full catalogue branching factor. -/
noncomputable def gm02RecursiveTime (q C d m : ℕ) : ℕ :=
  if h : m / 2 ≤ 4 * q then C
  else C * (m / 2 + 1) ^ d + 2 * gm02RecursiveCodeBound q *
    gm02RecursiveTime q C d
      (if m % 2 = 0 then 2 * (3 * (m / 2) / 4) + 1 else 2 * (m / 2))
termination_by m
decreasing_by exact next_measure_lt m q (by omega)

/-- A1's exact numerical recurrence above the base bound. -/
theorem gm02RecursiveTime_A1 (q C d n : ℕ) (hn : 4 * q < n) :
    gm02RecursiveTime q C d (2 * n) = C * (n + 1) ^ d +
      2 * gm02RecursiveCodeBound q * gm02RecursiveTime q C d (2 * (3 * n / 4) + 1) := by
  rw [gm02RecursiveTime]
  simp only [Nat.mul_div_cancel_left n (by decide : 0 < 2), Nat.not_le.mpr hn,
    ↓reduceDIte, Nat.mul_mod_right, ↓reduceIte]

/-- A2's exact numerical recurrence above the base bound. -/
theorem gm02RecursiveTime_A2 (q C d n : ℕ) (hn : 4 * q < n) :
    gm02RecursiveTime q C d (2 * n + 1) = C * (n + 1) ^ d +
      2 * gm02RecursiveCodeBound q * gm02RecursiveTime q C d (2 * n) := by
  rw [gm02RecursiveTime]
  have hdiv : (2 * n + 1) / 2 = n := by omega
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  simp only [hdiv, Nat.not_le.mpr hn, ↓reduceDIte, hmod, Nat.one_ne_zero, ↓reduceIte]

/-- Both phases have the same fixed exhaustive cost below the base bound. -/
theorem gm02RecursiveTime_base (q C d m : ℕ) (hm : m / 2 ≤ 4 * q) :
    gm02RecursiveTime q C d m = C := by
  rw [gm02RecursiveTime, dite_eq_left hm]

/-- The numerical budget always includes the exhaustive base cost. -/
theorem gm02RecursiveTime_ge_base (q C d m : ℕ) : C ≤ gm02RecursiveTime q C d m := by
  rw [gm02RecursiveTime]
  split
  · exact le_rfl
  · have hpow : 1 ≤ (m / 2 + 1) ^ d := Nat.one_le_pow d _ (by omega)
    exact (Nat.le_mul_of_pos_right C hpow).trans (Nat.le_add_right _ _)

/-- The explicit A2 time budget is polynomial by II's alternating recurrence calculation. -/
theorem gm02RecursiveTime_polynomial (q C d : ℕ) (hq : 1 ≤ q) :
    let c := C + 2 * gm02RecursiveCodeBound q + 1
    ∀ n, gm02RecursiveTime q C d (2 * n + 1) ≤
      (c + 2 * (c + c * c) + 1) * (n + 1) ^ (8 * (c * c) + d) := by
  let c := C + 2 * gm02RecursiveCodeBound q + 1
  have hC : C ≤ c := by dsimp only [c]; omega
  have hK : 2 * gm02RecursiveCodeBound q ≤ c := by dsimp only [c]; omega
  apply alternating_recurrence_polynomial
    (fun n => gm02RecursiveTime q C d (2 * n))
    (fun n => gm02RecursiveTime q C d (2 * n + 1)) q c d hq
  · intro n hn
    rw [gm02RecursiveTime_base q C d _ (by omega)]
    exact hC
  · intro n hn
    rw [gm02RecursiveTime_A1 q C d n hn]
    calc
      C * (n + 1) ^ d + 2 * gm02RecursiveCodeBound q *
          gm02RecursiveTime q C d (2 * (3 * n / 4) + 1) ≤
        c * (n + 1) ^ d + c * gm02RecursiveTime q C d (2 * (3 * n / 4) + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_right _ hC) (Nat.mul_le_mul_right _ hK)
      _ = _ := (Nat.mul_add _ _ _).symm
  · intro n hn
    rw [gm02RecursiveTime_A2 q C d n hn]
    calc
      C * (n + 1) ^ d + 2 * gm02RecursiveCodeBound q * gm02RecursiveTime q C d (2 * n) ≤
        c * (n + 1) ^ d + c * gm02RecursiveTime q C d (2 * n) :=
          Nat.add_le_add (Nat.mul_le_mul_right _ hC) (Nat.mul_le_mul_right _ hK)
      _ = _ := (Nat.mul_add _ _ _).symm

end GraphMinor.Compute
