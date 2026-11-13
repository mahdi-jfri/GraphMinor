module
public import GraphMinor.Thomason.UniformTail
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Thomason's bound for `p > 10 ^ 44`

We apply the random block lemma to the reduced graphs, cutting the range of
`q / n` into three pieces as explained in `UniformTail.lean`.
-/

public section
namespace GraphMinor.Thomason.Uniform
open Finset SimpleGraph
universe u

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- One piece of the range of `q / n`: blocks of size `⌈t s⌉ + 1` give a
`K_{p-2}` minor. -/
theorem clique_of_tail_piece (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ)
    (hq : ∀ v, (nonNbr H v).card ≤ q) {p : ℕ} {s R t μ φlo φhi : ℝ} {j e₀ : ℕ}
    (hs : 12 ≤ s) (hp2 : (2 : ℝ) ^ (s ^ 2) = p) (hp : 10000 ≤ (p : ℝ))
    (h16 : 16 * s ≤ p) (hR : p * s - 158 / 67 ≤ R)
    (hRq : R ≤ Fintype.card W - 2 * (q : ℝ))
    (hn : (Fintype.card W : ℝ) ≤ 67 / 25 * p * s)
    (hlo : φlo * Fintype.card W ≤ q) (hhi : (q : ℝ) ≤ φhi * Fintype.card W) (hφ0 : 0 ≤ φhi)
    (hφ : φhi ≤ (2 : ℝ) ^ (-μ)) (ht : 0 < t) (ht1 : t ≤ 1) (hμ : 1 ≤ μ)
    (htμ : 1 ≤ t ^ 2 * μ) (hj : (j : ℝ) ≤ 12 * t) (hy1 : 2 * φhi * (1001 / 1000) ≤ 1)
    (hF : (2 * φhi * (1001 / 1000)) ^ j ≤ 1 / 50)
    (hE : (e₀ : ℝ) ≤ 24 * t * (μ - 1) + μ - 2) (he₀ : 134 ≤ t * 2 ^ e₀)
    (hu : 0 < 1 - 2 * φlo) (hg : 0 ≤ 1 - 141 / 100 * (1 - 2 * φlo) * t)
    (hg2 : 1 / 1000 ≤ 12 * (1 - 141 / 100 * (1 - 2 * φlo) * t) - 282 / 100 * (1 - 2 * φlo)) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (p - 2)))) (Graph.ofSimpleGraph H) := by
  have hs0 : 0 ≤ t * s := by positivity
  obtain ⟨k, hk_def⟩ : ∃ k, k = ⌈t * s⌉₊ + 1 := ⟨_, rfl⟩
  have hk1 : t * s + 1 ≤ k := by
    rw [hk_def]; push_cast; linarith [Nat.le_ceil (t * s)]
  have hk2 : (k : ℝ) ≤ t * s + 2 := by
    rw [hk_def]; push_cast; linarith [Nat.ceil_lt_add_one hs0]
  have hk : 1 ≤ k := by omega
  have hk0 : 0 < k := hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  set n := Fintype.card W
  have hN1 : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / k := Nat.cast_div_le
  have hN2 : (n : ℝ) / k - 1 < ((n / k : ℕ) : ℝ) := by
    have h := Nat.lt_div_mul_add (a := n) hk0
    have h' : (n : ℝ) < ((n / k : ℕ) : ℝ) * k + k := by exact_mod_cast h
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hkR]
    linarith
  have hB := tail_bound (N := ((n / k : ℕ) : ℝ)) (q := (q : ℝ)) hs hp2 hp h16 hR hRq hn
    (Nat.cast_nonneg q) hlo hhi hφ0 hφ ht ht1 hμ htμ hj hy1 hF hE he₀ hu hg hg2 hk1 hk2
    (Nat.cast_nonneg _) hN1 hN2
  have hp2' : 2 ≤ p := by
    have : (2 : ℝ) ≤ p := by linarith
    exact_mod_cast this
  refine clique_isIsoMinor_of_two_sizes H q hq k 1 (n / k) 0 hk le_rfl
    (by simpa using Nat.div_mul_le_self n k) 4 1 (by norm_num) one_pos (p - 2) ?_
  rw [Nat.cast_sub hp2']
  simp only [Nat.cast_zero, zero_mul, mul_zero, sub_zero, add_zero, Nat.cast_ofNat]
  linarith

/-- For `p > 10 ^ 44`, the reduced graphs have a `K_{p-2}` minor. -/
theorem reduced_clique_of_large {p : ℕ} (hp : 10 ^ 44 < p) [Nonempty W] (J : SimpleGraph W)
    [DecidableRel J.Adj]
    (hW : Fintype.card W ≤ ⌊(67 / 25 : ℝ) * p * Real.sqrt (Real.logb 2 p)⌋₊)
    (hdeg : ∀ v, 2 * (nonNbr J v).card +
      (25 * ⌊(67 / 25 : ℝ) * p * Real.sqrt (Real.logb 2 p)⌋₊ / 67 - 1) ≤ Fintype.card W) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (p - 2)))) (Graph.ofSimpleGraph J) := by
  obtain ⟨hs12, hp2, h16⟩ := tail_s_facts hp
  generalize Real.sqrt (Real.logb 2 p) = s at hW hdeg hs12 hp2 h16
  have hpR : (10000 : ℝ) ≤ p := by
    have : (10000 : ℝ) ≤ 10 ^ 44 := by norm_num
    have h : ((10 ^ 44 : ℕ) : ℝ) < p := by exact_mod_cast hp
    push_cast at h
    linarith
  have hps : (10000 : ℝ) * 12 ≤ p * s := mul_le_mul hpR hs12 (by norm_num) (by linarith)
  -- the density `c = ⌊D⌋` and `R`
  generalize hD : 67 / 25 * (p : ℝ) * s = D at hW hdeg
  have hD0 : 0 ≤ D := by rw [← hD]; positivity
  have hcD : (⌊D⌋₊ : ℝ) ≤ D := Nat.floor_le hD0
  have hDc : D < ⌊D⌋₊ + 1 := Nat.lt_floor_add_one D
  generalize hc : ⌊D⌋₊ = c at hW hdeg hcD hDc
  have hc3 : 3 ≤ c := by
    have : (3 : ℝ) < c := by rw [← hD] at hDc; linarith
    exact_mod_cast this.le
  have hR := cast_R_ge c hc3
  generalize hRdef : 25 * c / 67 - 1 = R at hdeg hR
  have hRreal : (p : ℝ) * s - 158 / 67 ≤ R := by rw [← hD] at hDc; linarith
  -- the order `n` and the non-neighbour bound `q`
  generalize hn : Fintype.card W = n at hW hdeg
  obtain ⟨v₀⟩ := ‹Nonempty W›
  have hRn : R ≤ n := by have := hdeg v₀; omega
  have hq (v : W) : (nonNbr J v).card ≤ (n - R) / 2 := by have := hdeg v; omega
  have hRq : (R : ℝ) ≤ n - 2 * (((n - R) / 2 : ℕ) : ℝ) := by
    have h : 2 * ((n - R) / 2) ≤ n - R := by omega
    have h' : ((2 * ((n - R) / 2) : ℕ) : ℝ) ≤ ((n - R : ℕ) : ℝ) := by exact_mod_cast h
    push_cast [Nat.cast_sub hRn] at h'
    linarith
  have hnD : (n : ℝ) ≤ 67 / 25 * p * s := by
    have : (n : ℝ) ≤ c := by exact_mod_cast hW
    linarith
  subst hn
  generalize hqdef : (Fintype.card W - R) / 2 = q at hq hRq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  -- the three pieces of the range of `q / n`
  by_cases hC : (q : ℝ) ≤ 1 / 25 * Fintype.card W
  · exact clique_of_tail_piece J q hq (φlo := 0) (t := 1 / 2) (μ := ((4 : ℕ) : ℝ) / (1 : ℕ))
      (j := 5) (e₀ := 9) hs12 hp2 hpR h16 hRreal hRq hnD (by simp) hC
      (by norm_num) (le_two_rpow_neg (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  by_cases hB : (q : ℝ) ≤ 13 / 100 * Fintype.card W
  · exact clique_of_tail_piece J q hq (φlo := 1 / 25) (t := 3 / 5)
      (μ := ((29 : ℕ) : ℝ) / (10 : ℕ)) (j := 7) (e₀ := 8) hs12 hp2 hpR h16 hRreal hRq hnD
      (by linarith) hB (by norm_num) (le_two_rpow_neg (by norm_num) (by norm_num) (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have hA : (q : ℝ) ≤ 63 / 200 * Fintype.card W := by linarith
    exact clique_of_tail_piece J q hq (φlo := 13 / 100) (t := 39 / 50)
      (μ := ((83 : ℕ) : ℝ) / (50 : ℕ)) (j := 9) (e₀ := 8) hs12 hp2 hpR h16 hRreal hRq hnD
      (by linarith) hA (by norm_num) (le_two_rpow_neg (by norm_num) (by norm_num) (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- For `p > 10 ^ 44`, density `2.68 p (log₂ p) ^ (1/2)` forces a `K_p`
minor. -/
theorem clique_isIsoMinor_of_large {p : ℕ} (hp : 10 ^ 44 < p) {V : Type u} [Fintype V]
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : ⌊(67 / 25 : ℝ) * p * Real.sqrt (Real.logb 2 p)⌋₊ * Fintype.card V ≤
      G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin p))) (Graph.ofSimpleGraph G) := by
  have hc3 : 3 ≤ ⌊(67 / 25 : ℝ) * p * Real.sqrt (Real.logb 2 p)⌋₊ := by
    obtain ⟨hs12, -, -⟩ := tail_s_facts hp
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
    have h : (3 : ℝ) ≤ 67 / 25 * p * Real.sqrt (Real.logb 2 p) := by nlinarith
    exact Nat.le_floor (by exact_mod_cast h)
  have h := clique_isIsoMinor_of_reduced G _ (p - 2) hc3 hden
    fun J _ hW hdeg => reduced_clique_of_large hp J hW hdeg
  rwa [show p - 2 + 2 = p by omega] at h

end GraphMinor.Thomason.Uniform
