module
public import GraphMinor.Thomason.UniformTwoSizes
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# One cell of the interval certificate

Section 5 of the note `docs/thomason/uniform_minor_bound.tex` covers whole ranges of
`p` and of the normalized order `x = n / D` at once. Fix a cell: integers
`L ≤ p ≤ U`, and bounds `a C p s_L ≤ n ≤ C U s_U b` on the order of the reduced
graph, where `C = 67/25`. Let `π` bound the non-neighbour proportion `q / n`,
take `k` blocks per branch set and `A = (k + 1) / (k P)`. Put
`n₋ = C L s_L a` and `n₊ = C U s_U b`, and

* `F ≥ (2 ^ (k - 1) - 1) (π n₋ / (n₋ - k + 1)) ^ (k - 1)`,
* `((k + 1) / k) ^ (k + 1) (n₊ / 2) (n₋ / (n₋ - k)) ^ k π ^ (k ^ 2) ≤ P ^ (k + 1)`,
* `F + P < 1` and `(C s_L a / k - 1 / L) (1 - F - P) > 1 - 3 / U`.

Then `⌊n / k⌋` blocks of size `k` satisfy the hypothesis of the random block
lemma with `m = p - 2`. The losses are monotone in `n` and `π`, which is why
the cell bounds suffice; the choice of `A` replaces the optimization of the
note, formula (6), without any root.
-/

public section
namespace GraphMinor.Thomason.Uniform

/-- `n / (n - j)` decreases in `n`. -/
private theorem div_sub_le_div_sub {x y j : ℝ} (hj : 0 ≤ j) (hxj : j < x) (hxy : x ≤ y) :
    y / (y - j) ≤ x / (x - j) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The cell estimate. -/
theorem cell_bound (p n q k L U : ℕ) (sL sU a b π P F : ℝ)
    (hk : 1 ≤ k) (hL : 1 ≤ L) (hpL : L ≤ p) (hpU : p ≤ U) (hsL : 0 < sL) (ha : 0 < a)
    (hnlo : a * (67 / 25) * p * sL ≤ n) (hnhi : (n : ℝ) ≤ 67 / 25 * U * sU * b)
    (hq : (q : ℝ) ≤ π * n) (hπ : 0 ≤ π) (hP : 0 < P)
    (hkn : (k : ℝ) < 67 / 25 * L * sL * a)
    (hF : ((2 : ℝ) ^ (k - 1) - 1) * (π * (67 / 25 * L * sL * a) /
      (67 / 25 * L * sL * a - k + 1)) ^ (k - 1) ≤ F)
    (hH : (((k : ℝ) + 1) / k) ^ (k + 1) * ((67 / 25 * U * sU * b) / 2) *
      ((67 / 25 * L * sL * a) / (67 / 25 * L * sL * a - k)) ^ k * π ^ (k * k) ≤ P ^ (k + 1))
    (hFP : F + P < 1)
    (htest : 1 - 3 / (U : ℝ) < (67 / 25 * sL * a / k - 1 / L) * (1 - F - P)) :
    ((p : ℝ) - 2) - 1 < ((n / k : ℕ) : ℝ) * (1 - ((2 : ℝ) ^ (k - 1) - 1) *
        ((q : ℝ) / ((n : ℝ) - k + 1)) ^ (k - 1) - 1 / (((k : ℝ) + 1) / (k * P))) -
      ((n / k : ℕ) : ℝ) * (((n / k : ℕ) : ℝ) - 1) / 2 *
        (((k : ℝ) + 1) / (k * P) * (n * ((q : ℝ) / n) ^ k) / ((n : ℝ) - k)) ^ k := by
  set nlo : ℝ := 67 / 25 * L * sL * a with hnlo_def
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hpLR : (L : ℝ) ≤ p := by exact_mod_cast hpL
  have hpUR : (p : ℝ) ≤ U := by exact_mod_cast hpU
  have hpos_p : (0 : ℝ) < p := by linarith
  have hnlo_le : nlo ≤ n := by
    calc nlo = a * (67 / 25) * L * sL := by rw [hnlo_def]; ring
      _ ≤ a * (67 / 25) * p * sL := by gcongr
      _ ≤ n := hnlo
  have hkn' : (k : ℝ) < n := lt_of_lt_of_le hkn hnlo_le
  have hnpos : (0 : ℝ) < n := by linarith
  have hnk : (0 : ℝ) < (n : ℝ) - k := by linarith
  -- the connectivity loss
  have hFreal : ((2 : ℝ) ^ (k - 1) - 1) * ((q : ℝ) / ((n : ℝ) - k + 1)) ^ (k - 1) ≤ F := by
    refine le_trans ?_ hF
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (k - 1) - 1 := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (k - 1) := one_le_pow₀ (by norm_num)
      linarith
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) h2
    have hj : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
    have hmono := div_sub_le_div_sub hj (by linarith : (k : ℝ) - 1 < nlo) hnlo_le
    calc (q : ℝ) / ((n : ℝ) - k + 1) ≤ π * n / ((n : ℝ) - k + 1) :=
          div_le_div_of_nonneg_right hq (by linarith)
      _ = π * (n / ((n : ℝ) - (k - 1))) := by ring_nf
      _ ≤ π * (nlo / (nlo - (k - 1))) := mul_le_mul_of_nonneg_left hmono hπ
      _ = π * nlo / (nlo - k + 1) := by ring_nf
  -- the pair loss
  set N : ℕ := n / k
  set A : ℝ := ((k : ℝ) + 1) / (k * P) with hA_def
  have hApos : 0 < A := by positivity
  set y : ℝ := A * (n * ((q : ℝ) / n) ^ k) / ((n : ℝ) - k)
  have hy0 : 0 ≤ y := by positivity
  have hy : y ≤ A * π ^ k * (nlo / (nlo - k)) := by
    have hqn : (q : ℝ) / n ≤ π := by rw [div_le_iff₀ hnpos]; linarith
    have hmono := div_sub_le_div_sub (by linarith : (0 : ℝ) ≤ k) hkn hnlo_le
    calc y = A * ((q : ℝ) / n) ^ k * (n / ((n : ℝ) - k)) := by
          simp only [y]; ring
      _ ≤ A * π ^ k * (nlo / (nlo - k)) := by
          gcongr
  have hNk : (N : ℝ) * k ≤ n := by
    have := Nat.div_mul_le_self n k
    exact_mod_cast this
  have hNlow : (n : ℝ) / k - 1 < N := by
    have h := Nat.lt_div_mul_add (a := n) (b := k) (by omega)
    have h' : (n : ℝ) < N * k + k := by exact_mod_cast h
    rw [div_sub_one (by positivity), div_lt_iff₀ (by positivity)]
    linarith
  have hNnhi : (N : ℝ) - 1 ≤ (67 / 25 * U * sU * b) / k := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hpair : ((N : ℝ) - 1) / 2 * y ^ k ≤ P / (k + 1) := by
    have hyk : y ^ k ≤ (A * π ^ k * (nlo / (nlo - k))) ^ k := pow_le_pow_left₀ hy0 hy k
    rcases le_or_gt (N : ℝ) 1 with hN1 | hN1
    · have : ((N : ℝ) - 1) / 2 * y ^ k ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      exact this.trans (by positivity)
    have hnhi0 : (0 : ℝ) ≤ 67 / 25 * U * sU * b := (Nat.cast_nonneg n).trans hnhi
    calc ((N : ℝ) - 1) / 2 * y ^ k
        ≤ ((67 / 25 * U * sU * b) / k) / 2 * (A * π ^ k * (nlo / (nlo - k))) ^ k := by
          gcongr
      _ = ((((k : ℝ) + 1) / k) ^ (k + 1) * ((67 / 25 * U * sU * b) / 2) *
            (nlo / (nlo - k)) ^ k * π ^ (k * k)) / ((k + 1) * P ^ k) := by
          rw [hA_def]
          have hk0 : (k : ℝ) ≠ 0 := by positivity
          have hP0 : P ≠ 0 := hP.ne'
          have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
          have hnk0 : nlo - k ≠ 0 := by linarith
          rw [mul_pow, mul_pow, ← pow_mul]
          simp only [div_pow, mul_pow]
          field_simp
          ring
      _ ≤ P ^ (k + 1) / ((k + 1) * P ^ k) := by gcongr
      _ = P / (k + 1) := by
          rw [pow_succ]; field_simp
  -- assemble
  have h1A : 1 / A = k * P / (k + 1) := by rw [hA_def]; field_simp
  have hFP' : 0 < 1 - F - P := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hB : (N : ℝ) * (1 - F - P) ≤ (N : ℝ) * (1 - ((2 : ℝ) ^ (k - 1) - 1) *
        ((q : ℝ) / ((n : ℝ) - k + 1)) ^ (k - 1) - 1 / A) - (N : ℝ) * ((N : ℝ) - 1) / 2 * y ^ k := by
    have : (N : ℝ) * ((N : ℝ) - 1) / 2 * y ^ k = N * (((N : ℝ) - 1) / 2 * y ^ k) := by ring
    rw [this, h1A]
    have h3 := mul_le_mul_of_nonneg_left hpair hN0
    have h4 := mul_le_mul_of_nonneg_left hFreal hN0
    have h5 : (N : ℝ) * (k * P / (k + 1)) + N * (P / (k + 1)) = N * P := by
      field_simp
    generalize ((2 : ℝ) ^ (k - 1) - 1) * ((q : ℝ) / ((n : ℝ) - k + 1)) ^ (k - 1) = X at h4 ⊢
    generalize ((N : ℝ) - 1) / 2 * y ^ k = Y at h3 ⊢
    calc (N : ℝ) * (1 - F - P) = N - N * F - (N * (k * P / (k + 1)) + N * (P / (k + 1))) := by
          rw [h5]; ring
      _ ≤ N - N * X - (N * (k * P / (k + 1)) + N * Y) := by linarith only [h3, h4]
      _ = N * (1 - X - k * P / (k + 1)) - N * Y := by ring
  have hlow : (p : ℝ) * (1 - 3 / U) < N * (1 - F - P) := by
    have hG : (p : ℝ) * (67 / 25 * sL * a / k - 1 / L) ≤ (n : ℝ) / k - 1 := by
      have h1 : (p : ℝ) * (67 / 25 * sL * a / k) ≤ n / k := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]; linarith
      have h2 : (1 : ℝ) ≤ p * (1 / L) := by
        rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
      have e : (p : ℝ) * (67 / 25 * sL * a / k - 1 / L) =
          p * (67 / 25 * sL * a / k) - p * (1 / L) := by ring
      linarith only [h1, h2, e]
    calc (p : ℝ) * (1 - 3 / U) < p * ((67 / 25 * sL * a / k - 1 / L) * (1 - F - P)) :=
          mul_lt_mul_of_pos_left htest hpos_p
      _ = (p * (67 / 25 * sL * a / k - 1 / L)) * (1 - F - P) := by ring
      _ ≤ ((n : ℝ) / k - 1) * (1 - F - P) := mul_le_mul_of_nonneg_right hG hFP'.le
      _ ≤ N * (1 - F - P) := mul_le_mul_of_nonneg_right hNlow.le hFP'.le
  have hU3 : (p : ℝ) - 3 ≤ p * (1 - 3 / U) := by
    have hUpos : (0 : ℝ) < U := by linarith
    have : (p : ℝ) * (3 / U) ≤ 3 := by
      rw [mul_div_assoc', div_le_iff₀ hUpos]; linarith
    have e : (p : ℝ) * (1 - 3 / U) = p - p * (3 / U) := by ring
    linarith only [this, e]
  linarith

end GraphMinor.Thomason.Uniform
