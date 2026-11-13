module
public import GraphMinor.Thomason.UniformIntervals
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# The random block lemma for `p > 10 ^ 44`

This replaces Section 6 of the note `docs/thomason/uniform_minor_bound.tex`. We keep
the density `D = (67/25) p s` of XIII (5.5) with `s = (log₂ p) ^ (1/2)`, so
`p = 2 ^ (s ^ 2)` and `s ≥ 12`. Let `c = ⌊D⌋` and `R = ⌊25c/67⌋ - 1`; then
`R ≥ p s - 158/67`. A reduced graph has order `n ≤ D` and at most `q`
non-neighbours at each vertex, where `2q ≤ n - R`.

The note picks the block size from `ln (n / q)`. To avoid logarithms of
`q / n`, we cut the range of `π = q / n` into the three pieces
`π ≤ 1/25`, `1/25 < π ≤ 13/100` and `13/100 < π ≤ 63/200`. On a piece with
`π ≤ φ ≤ 2 ^ (-μ)` we take blocks of size `k = ⌈t s⌉ + 1` with
`t ^ 2 μ ≥ 1`, and `A = 4`. Then

* the connectivity loss `F` is at most `(2 φ · 1001/1000) ^ (k - 1) ≤ 1/50`;
* the missing-pair loss per block is at most
  `(67/25)/t · 2 ^ (s ^ 2 + 2k - μ k ^ 2) ≤ 1/50`, since `p = 2 ^ (s ^ 2)` and
  `μ k ^ 2 - 2k ≥ s ^ 2 + 24 t (μ - 1) + μ - 2`;
* there are at least `n / k - 1` blocks, and `n / k ≥ 1.41 p` because
  `n (1 - 2π) ≥ R` and `k ≤ t s + 2`.

So at least `0.71 (1.41 p - 1) > p - 3` blocks survive.
-/

public section
namespace GraphMinor.Thomason.Uniform
open Finset SimpleGraph

/-- The connectivity loss on a piece: if `q ≤ φ n` and the block size `k`
is small compared with `n`, then `F ≤ (2 φ · 1001/1000) ^ j` for every
`j ≤ k - 1`. -/
theorem tail_F_le {n q φ : ℝ} {k j : ℕ} (hk : 1 ≤ k) (hjk : j ≤ k - 1)
    (hkn : 1001 * (k : ℝ) ≤ n) (hq0 : 0 ≤ q) (hφ0 : 0 ≤ φ) (hq : q ≤ φ * n)
    (hy1 : 2 * φ * (1001 / 1000) ≤ 1) (hF : (2 * φ * (1001 / 1000)) ^ j ≤ 1 / 50) :
    ((2 : ℝ) ^ (k - 1) - 1) * (q / (n - k + 1)) ^ (k - 1) ≤ 1 / 50 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnk : 0 < n - k + 1 := by linarith
  have hb0 : 0 ≤ q / (n - k + 1) := div_nonneg hq0 hnk.le
  have hb : 2 * (q / (n - k + 1)) ≤ 2 * φ * (1001 / 1000) := by
    rw [mul_assoc, mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2), div_le_iff₀ hnk]
    have : φ * n ≤ φ * (1001 / 1000) * (n - k + 1) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith) hφ0
    linarith
  calc ((2 : ℝ) ^ (k - 1) - 1) * (q / (n - k + 1)) ^ (k - 1)
      ≤ (2 : ℝ) ^ (k - 1) * (q / (n - k + 1)) ^ (k - 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hb0 _)
    _ = (2 * (q / (n - k + 1))) ^ (k - 1) := (mul_pow _ _ _).symm
    _ ≤ (2 * φ * (1001 / 1000)) ^ (k - 1) := pow_le_pow_left₀ (by positivity) hb _
    _ ≤ (2 * φ * (1001 / 1000)) ^ j := pow_le_pow_of_le_one (by positivity) hy1 hjk
    _ ≤ 1 / 50 := hF

/-- The exponent of the missing-pair loss: for `k ≥ t s + 1`,
`s ^ 2 + 2k - μ k ^ 2 ≤ -e₀`. -/
theorem tail_exponent_le {s t μ k e₀ : ℝ} (hs : 12 ≤ s) (ht : 0 < t) (hμ : 1 ≤ μ)
    (htμ : 1 ≤ t ^ 2 * μ) (hk : t * s + 1 ≤ k) (hE : e₀ ≤ 24 * t * (μ - 1) + μ - 2) :
    s ^ 2 + 2 * k - μ * k ^ 2 ≤ -e₀ := by
  obtain ⟨a, ha⟩ : ∃ a, a = t * s + 1 := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by rw [ha]; nlinarith
  have h1 : μ * a ^ 2 - 2 * a ≤ μ * k ^ 2 - 2 * k := by
    have : 0 ≤ (k - a) * (μ * (k + a) - 2) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  have h2 : s ^ 2 ≤ t ^ 2 * μ * s ^ 2 := by nlinarith
  have h3 : 24 * t * (μ - 1) ≤ 2 * t * s * (μ - 1) := by
    have : 0 ≤ t * (μ - 1) := mul_nonneg ht.le (by linarith)
    nlinarith
  have h4 : μ * a ^ 2 - 2 * a = t ^ 2 * μ * s ^ 2 + 2 * t * s * (μ - 1) + μ - 2 := by
    rw [ha]; ring
  linarith

/-- The missing-pair loss per block on a piece is at most `1/50`. -/
theorem tail_pairs_le {p s n q t μ φ : ℝ} {k e₀ : ℕ} (hs : 12 ≤ s) (hp2 : (2 : ℝ) ^ (s ^ 2) = p)
    (hn : n ≤ 67 / 25 * p * s) (h2k : 2 * (k : ℝ) ^ 2 ≤ n) (hq0 : 0 ≤ q) (hq : q ≤ φ * n)
    (hφ : φ ≤ (2 : ℝ) ^ (-μ)) (ht : 0 < t) (hμ : 1 ≤ μ) (htμ : 1 ≤ t ^ 2 * μ)
    (hk : t * s + 1 ≤ k) (hE : (e₀ : ℝ) ≤ 24 * t * (μ - 1) + μ - 2)
    (he₀ : 134 ≤ t * 2 ^ e₀) :
    n / (2 * k) * (4 * (n * (q / n) ^ k) / (n - k)) ^ k ≤ 1 / 50 := by
  have hs0 : 0 < s := by linarith
  have hk1 : (1 : ℝ) ≤ k := by nlinarith [mul_pos ht hs0]
  have hk0 : (0 : ℝ) < k := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) h2k
  have hp0 : 0 < p := by rw [← hp2]; positivity
  have hkn : (k : ℝ) < n := by nlinarith
  -- the factor `(n / (n - k)) ^ k ≤ 2`, by Bernoulli's inequality
  have hratio : (n / (n - k)) ^ k ≤ 2 := by
    have hb := one_add_mul_le_pow (a := -((k : ℝ) / n)) (by
      have : (k : ℝ) / n ≤ 1 := by rw [div_le_one hn0]; exact hkn.le
      linarith) k
    have hkk : (k : ℝ) * (k / n) ≤ 1 / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ hn0]; nlinarith
    have hr : (n - k) / n = 1 + -((k : ℝ) / n) := by field_simp; ring
    have hneg : (k : ℝ) * -((k : ℝ) / n) = -((k : ℝ) * (k / n)) := by ring
    have hrk : 2⁻¹ ≤ ((n - k) / n) ^ k := by rw [hr]; linarith
    have hr0 : 0 < (n - k) / n := div_pos (by linarith) hn0
    calc (n / (n - k)) ^ k = (((n - k) / n) ^ k)⁻¹ := by rw [← inv_pow, inv_div]
      _ ≤ 2 := by rw [inv_le_comm₀ (by positivity) (by norm_num)]; exact hrk
  -- the factor `(q / n) ^ (k k) ≤ 2 ^ (-μ k k)`
  have hπ0 : 0 ≤ q / n := div_nonneg hq0 hn0.le
  have hπ : q / n ≤ (2 : ℝ) ^ (-μ) := by
    rw [div_le_iff₀ hn0]
    have : φ * n ≤ (2 : ℝ) ^ (-μ) * n := mul_le_mul_of_nonneg_right hφ hn0.le
    linarith
  have hpow : (q / n) ^ (k * k) ≤ (2 : ℝ) ^ (-μ * ((k * k : ℕ) : ℝ)) := by
    calc (q / n) ^ (k * k) ≤ ((2 : ℝ) ^ (-μ)) ^ (k * k) := pow_le_pow_left₀ hπ0 hπ _
      _ = (2 : ℝ) ^ (-μ * ((k * k : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have h4 : (4 : ℝ) ^ k = (2 : ℝ) ^ (((2 * k : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast, pow_mul]; norm_num
  -- the exponent
  have hexp : (2 : ℝ) ^ (s ^ 2) * (2 : ℝ) ^ (((2 * k : ℕ) : ℝ)) *
      (2 : ℝ) ^ (-μ * ((k * k : ℕ) : ℝ)) ≤ ((2 : ℝ) ^ e₀)⁻¹ := by
    rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
    have h := tail_exponent_le (k := (k : ℝ)) (e₀ := (e₀ : ℝ)) hs ht hμ htμ hk hE
    calc _ ≤ (2 : ℝ) ^ (-(e₀ : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          push_cast
          linarith [show (k : ℝ) ^ 2 = k * k by ring]
      _ = ((2 : ℝ) ^ e₀)⁻¹ := by rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  -- the number of pairs
  have hnk2 : n / (2 * k) ≤ 67 / 50 * p / t := by
    rw [div_le_div_iff₀ (by positivity) ht]
    have h1 : n * t ≤ 67 / 25 * p * s * t := mul_le_mul_of_nonneg_right hn ht.le
    have h2 : 67 / 25 * p * (t * s) ≤ 67 / 25 * p * k :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have eX : 4 * (n * (q / n) ^ k) / (n - k) = 4 * (q / n) ^ k * (n / (n - k)) := by ring
  have h2e : (0 : ℝ) < 2 ^ e₀ := by positivity
  calc n / (2 * k) * (4 * (n * (q / n) ^ k) / (n - k)) ^ k
      = n / (2 * k) * ((4 : ℝ) ^ k * (q / n) ^ (k * k) * (n / (n - k)) ^ k) := by
        rw [eX, mul_pow, mul_pow, ← pow_mul]
    _ ≤ 67 / 50 * p / t * ((4 : ℝ) ^ k * (2 : ℝ) ^ (-μ * ((k * k : ℕ) : ℝ)) * 2) := by
        gcongr
    _ = 67 / 25 / t * ((2 : ℝ) ^ (s ^ 2) * (2 : ℝ) ^ (((2 * k : ℕ) : ℝ)) *
        (2 : ℝ) ^ (-μ * ((k * k : ℕ) : ℝ))) := by rw [← hp2, h4]; ring
    _ ≤ 67 / 25 / t * ((2 : ℝ) ^ e₀)⁻¹ := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ 1 / 50 := by
        have e : (67 / 25 : ℝ) / t * ((2 : ℝ) ^ e₀)⁻¹ = 67 / 25 / (t * 2 ^ e₀) := by
          field_simp
        rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith

/-- The number of blocks on a piece: `n ≥ 1.41 p k`. Here `φ` is a lower
bound for `q / n`, so `n (1 - 2φ) ≥ n - 2q ≥ R`. -/
theorem tail_blocks {p s n q R t φ k : ℝ} (hs : 12 ≤ s) (hp : 10000 ≤ p)
    (hR : p * s - 158 / 67 ≤ R) (hRq : R ≤ n - 2 * q) (hlo : φ * n ≤ q)
    (hu : 0 < 1 - 2 * φ) (hg : 0 ≤ 1 - 141 / 100 * (1 - 2 * φ) * t)
    (hg2 : 1 / 1000 ≤ 12 * (1 - 141 / 100 * (1 - 2 * φ) * t) - 282 / 100 * (1 - 2 * φ))
    (hk2 : k ≤ t * s + 2) :
    141 / 100 * p * k ≤ n := by
  obtain ⟨u, hu_def⟩ : ∃ u, u = 1 - 2 * φ := ⟨_, rfl⟩
  rw [← hu_def] at hu hg hg2
  obtain ⟨g, hg_def⟩ : ∃ g, g = 1 - 141 / 100 * u * t := ⟨_, rfl⟩
  rw [← hg_def] at hg hg2
  have hnu : R ≤ n * u := by rw [hu_def]; linarith
  have h1 : 141 / 100 * p * u * k ≤ 141 / 100 * p * u * (t * s + 2) :=
    mul_le_mul_of_nonneg_left hk2 (by positivity)
  have h2 : 141 / 100 * p * u * (t * s + 2) = p * s - p * (s * g - 282 / 100 * u) := by
    rw [hg_def]; ring
  have h3 : 12 * g ≤ s * g := mul_le_mul_of_nonneg_right hs hg
  have h4 : p / 1000 ≤ p * (s * g - 282 / 100 * u) := by
    have : 1 / 1000 ≤ s * g - 282 / 100 * u := by linarith
    nlinarith
  have h5 : 141 / 100 * p * k * u ≤ n * u := by nlinarith
  exact le_of_mul_le_mul_right h5 hu

/-- The hypothesis of the random block lemma on one piece of the range of
`q / n`, with `N` blocks of size `k` and `A = 4`. -/
theorem tail_bound {p s n q R t μ φlo φhi N : ℝ} {k j e₀ : ℕ} (hs : 12 ≤ s)
    (hp2 : (2 : ℝ) ^ (s ^ 2) = p) (hp : 10000 ≤ p) (h16 : 16 * s ≤ p)
    (hR : p * s - 158 / 67 ≤ R) (hRq : R ≤ n - 2 * q) (hn : n ≤ 67 / 25 * p * s)
    (hq0 : 0 ≤ q) (hlo : φlo * n ≤ q) (hhi : q ≤ φhi * n) (hφ0 : 0 ≤ φhi)
    (hφ : φhi ≤ (2 : ℝ) ^ (-μ)) (ht : 0 < t) (ht1 : t ≤ 1) (hμ : 1 ≤ μ)
    (htμ : 1 ≤ t ^ 2 * μ) (hj : (j : ℝ) ≤ 12 * t) (hy1 : 2 * φhi * (1001 / 1000) ≤ 1)
    (hF : (2 * φhi * (1001 / 1000)) ^ j ≤ 1 / 50)
    (hE : (e₀ : ℝ) ≤ 24 * t * (μ - 1) + μ - 2) (he₀ : 134 ≤ t * 2 ^ e₀)
    (hu : 0 < 1 - 2 * φlo) (hg : 0 ≤ 1 - 141 / 100 * (1 - 2 * φlo) * t)
    (hg2 : 1 / 1000 ≤ 12 * (1 - 141 / 100 * (1 - 2 * φlo) * t) - 282 / 100 * (1 - 2 * φlo))
    (hk1 : t * s + 1 ≤ k) (hk2 : k ≤ t * s + 2) (hN0 : 0 ≤ N) (hN1 : N ≤ n / k)
    (hN2 : n / k - 1 < N) :
    (p - 2) - 1 < N * (1 - ((2 : ℝ) ^ (k - 1) - 1) * (q / (n - k + 1)) ^ (k - 1) - 1 / 4) -
      N * (N - 1) / 2 * (4 * (n * (q / n) ^ k) / (n - k)) ^ k := by
  have hs0 : 0 < s := by linarith
  have hk1' : (1 : ℝ) ≤ k := by linarith only [mul_pos ht hs0, hk1]
  have hk : 1 ≤ k := by exact_mod_cast hk1'
  have hkn0 : (0 : ℝ) < k := by linarith
  have hts : t * s ≤ 1 * s := mul_le_mul_of_nonneg_right ht1 hs0.le
  have hk2s : (k : ℝ) ≤ 2 * s := by linarith only [hts, hk2, hs]
  have hnR : p * s - 158 / 67 ≤ n := by linarith only [hR, hRq, hq0]
  have hps : 10000 * s ≤ p * s := mul_le_mul_of_nonneg_right hp hs0.le
  have hkn : 1001 * (k : ℝ) ≤ n := by linarith only [hnR, hps, hk2s, hs]
  have h2k : 2 * (k : ℝ) ^ 2 ≤ n := by
    have h1 : (k : ℝ) ^ 2 ≤ (2 * s) ^ 2 := pow_le_pow_left₀ hkn0.le hk2s 2
    have h2 : 16 * s * s ≤ p * s := mul_le_mul_of_nonneg_right h16 hs0.le
    have h3 : 12 * s ≤ s * s := mul_le_mul_of_nonneg_right hs hs0.le
    nlinarith only [h1, h2, h3, hnR, hs]
  have hn0 : 0 < n := by linarith only [hkn, hkn0]
  have hjk : j ≤ k - 1 := by
    have : (j : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
      have h12 : t * 12 ≤ t * s := mul_le_mul_of_nonneg_left hs ht.le
      rw [Nat.cast_sub hk]; push_cast; linarith
    exact_mod_cast this
  have hFle := tail_F_le hk hjk hkn hq0 hφ0 hhi hy1 hF
  have hP := tail_pairs_le hs hp2 hn h2k hq0 hhi hφ ht hμ htμ hk1 hE he₀
  have hB := tail_blocks hs hp hR hRq hlo hu hg hg2 hk2
  -- the missing-pair loss is at most `N / 50`
  have hX0 : 0 ≤ (4 * (n * (q / n) ^ k) / (n - k)) ^ k := by
    have : (0 : ℝ) < n - k := by linarith
    positivity
  have hM : N * (N - 1) / 2 * (4 * (n * (q / n) ^ k) / (n - k)) ^ k ≤ N / 50 := by
    have h1 : N * (N - 1) / 2 ≤ N * (n / (2 * k)) := by
      have h0 : N * (N - 1) ≤ N * (n / k) := mul_le_mul_of_nonneg_left (by linarith) hN0
      have : n / (2 * k) = n / k / 2 := by rw [div_div, mul_comm]
      rw [this]
      linarith
    calc N * (N - 1) / 2 * (4 * (n * (q / n) ^ k) / (n - k)) ^ k
        ≤ N * (n / (2 * k)) * (4 * (n * (q / n) ^ k) / (n - k)) ^ k :=
          mul_le_mul_of_nonneg_right h1 hX0
      _ = N * (n / (2 * k) * (4 * (n * (q / n) ^ k) / (n - k)) ^ k) := by ring
      _ ≤ N * (1 / 50) := mul_le_mul_of_nonneg_left hP hN0
      _ = N / 50 := by ring
  -- the connectivity and domination losses
  have hL : N * (1 - 1 / 50 - 1 / 4) ≤
      N * (1 - ((2 : ℝ) ^ (k - 1) - 1) * (q / (n - k + 1)) ^ (k - 1) - 1 / 4) :=
    mul_le_mul_of_nonneg_left (by linarith) hN0
  -- there are enough blocks
  have hnk : 141 / 100 * p ≤ n / k := by rw [le_div_iff₀ hkn0]; linarith only [hB]
  linarith only [hL, hM, hN2, hnk, hp]

/-- `φ ≤ 2 ^ (-a/b)` from the integer test `φ ^ b 2 ^ a ≤ 1`. -/
theorem le_two_rpow_neg {φ : ℝ} {a b : ℕ} (hb : 0 < b) (hφ : 0 ≤ φ) (h : φ ^ b * 2 ^ a ≤ 1) :
    φ ≤ (2 : ℝ) ^ (-((a : ℝ) / b)) := by
  have hb' : (b : ℝ) ≠ 0 := by positivity
  have e : ((2 : ℝ) ^ (-((a : ℝ) / b))) ^ b = ((2 : ℝ) ^ a)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), neg_mul, div_mul_cancel₀ _ hb',
      Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [← pow_le_pow_iff_left₀ hφ (by positivity) hb.ne', e]
  have h2 : (0 : ℝ) < 2 ^ a := by positivity
  calc φ ^ b = φ ^ b * 2 ^ a * ((2 : ℝ) ^ a)⁻¹ := by field_simp
    _ ≤ 1 * ((2 : ℝ) ^ a)⁻¹ := by gcongr
    _ = ((2 : ℝ) ^ a)⁻¹ := one_mul _

/-- For `p > 10 ^ 44` and `s = (log₂ p) ^ (1/2)`: `s ≥ 12`, `p = 2 ^ (s ^ 2)`
and `16 s ≤ p`. -/
theorem tail_s_facts {p : ℕ} (hp : 10 ^ 44 < p) :
    12 ≤ Real.sqrt (Real.logb 2 p) ∧ (2 : ℝ) ^ (Real.sqrt (Real.logb 2 p) ^ 2) = p ∧
      16 * Real.sqrt (Real.logb 2 p) ≤ p := by
  have hpR : (10 : ℝ) ^ 44 < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := lt_trans (by norm_num) hpR
  have h146 : (146 : ℝ) ≤ Real.logb 2 p := by
    have h := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num) (by positivity)
      (show (2 : ℝ) ^ 146 ≤ p by linarith [show (2 : ℝ) ^ 146 ≤ 10 ^ 44 by norm_num])
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h
    push_cast at h
    linarith
  have hsq : Real.sqrt (Real.logb 2 p) ^ 2 = Real.logb 2 p := Real.sq_sqrt (by linarith)
  refine ⟨Real.le_sqrt_of_sq_le (by linarith), ?_, ?_⟩
  · rw [hsq, Real.rpow_logb (by norm_num) (by norm_num) hp0]
  · have hlog2 := Real.log_two_gt_d9
    have hlogp := Real.log_le_sub_one_of_pos hp0
    have hlb : Real.logb 2 p ≤ 100 / 69 * p := by
      rw [← Real.log_div_log, div_le_iff₀ (by linarith)]
      nlinarith
    have h1 : (16 * Real.sqrt (Real.logb 2 p)) ^ 2 ≤ (p : ℝ) ^ 2 := by
      rw [mul_pow, hsq]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hp0.le (by norm_num)).mp h1

end GraphMinor.Thomason.Uniform
