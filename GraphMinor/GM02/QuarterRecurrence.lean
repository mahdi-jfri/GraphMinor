module

public import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial bounds for the three-quarter recurrence

II, page 317, reduces the two running-time inequalities to a recurrence
with a constant multiplier and arguments at most three quarters as large.
A fixed power absorbs that multiplier. An elementary binomial bound
compares powers of five and four, giving a factor of two of spare budget.
Strong induction then bounds the recurrence by a polynomial.
-/

public section
namespace GraphMinor.GM02

private theorem four_pow_linear_le_five_pow (e : ℕ) : (e + 4) * 4 ^ e ≤ 4 * 5 ^ e := by
  induction e with
  | zero => decide
  | succ e ih =>
    calc
      (e + 1 + 4) * 4 ^ (e + 1) = 4 * (e + 5) * 4 ^ e := by rw [pow_succ]; ring
      _ ≤ 5 * ((e + 4) * 4 ^ e) := by nlinarith [Nat.zero_le (e * 4 ^ e)]
      _ ≤ 5 * (4 * 5 ^ e) := Nat.mul_le_mul_left 5 ih
      _ = 4 * 5 ^ (e + 1) := by rw [pow_succ]; ring

/-- A fixed exponent absorbs any fixed branching multiplier. -/
theorem branching_power_budget (B d : ℕ) :
    2 * B * 4 ^ (8 * B + d) ≤ 5 ^ (8 * B + d) := by
  have h := four_pow_linear_le_five_pow (8 * B)
  have hbase : 2 * B * 4 ^ (8 * B) ≤ 5 ^ (8 * B) := by
    have hsmall := Nat.mul_le_mul_right (4 ^ (8 * B)) (show 8 * B ≤ 8 * B + 4 by omega)
    have hc : 4 * (2 * B * 4 ^ (8 * B)) ≤ 4 * 5 ^ (8 * B) := by
      convert hsmall.trans h using 1
      ring
    exact Nat.le_of_mul_le_mul_left hc (by decide)
  have htail : 4 ^ d ≤ 5 ^ d := Nat.pow_le_pow_left (by decide) d
  calc
    2 * B * 4 ^ (8 * B + d) = (2 * B * 4 ^ (8 * B)) * 4 ^ d := by rw [pow_add]; ring
    _ ≤ 5 ^ (8 * B) * 5 ^ d := Nat.mul_le_mul hbase htail
    _ = 5 ^ (8 * B + d) := (pow_add _ _ _).symm

/-- Powers of shifted sizes contract enough to pay for a fixed branching
factor when the vertex count decreases by three quarters. -/
theorem quarter_power_budget {n m : ℕ} (hn : 4 ≤ n) (hm : 4 * m ≤ 3 * n) (B d : ℕ) :
    2 * B * (m + 1) ^ (8 * B + d) ≤ (n + 1) ^ (8 * B + d) := by
  let e := 8 * B + d
  have hratio : 5 * (m + 1) ≤ 4 * (n + 1) := by omega
  have hpow := Nat.pow_le_pow_left hratio e
  rw [Nat.mul_pow, Nat.mul_pow] at hpow
  have hbudget := branching_power_budget B d
  have hmul := (Nat.mul_le_mul_right ((m + 1) ^ e) hbudget).trans hpow
  have hscaled : 4 ^ e * (2 * B * (m + 1) ^ e) ≤ 4 ^ e * (n + 1) ^ e := by
    convert hmul using 1
    ring
  exact Nat.le_of_mul_le_mul_left hscaled (Nat.pow_pos (by decide))

/-- The running-time conclusion of the recurrence argument in Graph Minors
II, page 317. The hypotheses are numerical recurrence bounds; applications
must prove them for the actual program before invoking this lemma. -/
theorem quarter_recurrence_polynomial (f : ℕ → ℕ) (w A B d C₀ : ℕ) (hw : 1 ≤ w)
    (hsmall : ∀ n ≤ 4 * w, f n ≤ C₀)
    (hrec : ∀ n, 4 * w < n → f n ≤ A * (n + 1) ^ d + B * f (3 * n / 4)) :
    ∀ n, f n ≤ (C₀ + 2 * A + 1) * (n + 1) ^ (8 * B + d) := by
  let C := C₀ + 2 * A + 1
  let e := 8 * B + d
  intro n
  change f n ≤ C * (n + 1) ^ e
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hbase : n ≤ 4 * w
    · have hpow : 1 ≤ (n + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_le_succ (Nat.zero_le n))
      calc
        f n ≤ C₀ := hsmall n hbase
        _ ≤ C := by dsimp [C]; omega
        _ ≤ C * (n + 1) ^ e := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left C hpow
    · have hlarge : 4 * w < n := Nat.lt_of_not_ge hbase
      have hn : 4 ≤ n := by omega
      let m := 3 * n / 4
      have hm : 4 * m ≤ 3 * n := by
        simpa only [m, Nat.mul_comm] using Nat.div_mul_le_self (3 * n) 4
      have hmn : m < n := by omega
      have hchild := ih m hmn
      have hcontract : 2 * B * (m + 1) ^ e ≤ (n + 1) ^ e := quarter_power_budget hn hm B d
      have hp : (n + 1) ^ d ≤ (n + 1) ^ e :=
        Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) (by dsimp [e]; omega)
      have hA : 2 * A * (n + 1) ^ d ≤ C * (n + 1) ^ e :=
        Nat.mul_le_mul (by dsimp [C]; omega) hp
      have hB : 2 * (B * (C * (m + 1) ^ e)) ≤ C * (n + 1) ^ e := by
        convert Nat.mul_le_mul_left C hcontract using 1
        ring
      have hstep : f n ≤ A * (n + 1) ^ d + B * (C * (m + 1) ^ e) :=
        (hrec n hlarge).trans (Nat.add_le_add_left (Nat.mul_le_mul_left B hchild) _)
      have htotal : 2 * (A * (n + 1) ^ d + B * (C * (m + 1) ^ e)) ≤ 2 * (C * (n + 1) ^ e) := by
        nlinarith only [hA, hB]
      omega

end GraphMinor.GM02
