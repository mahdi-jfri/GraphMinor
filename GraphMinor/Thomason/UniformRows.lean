module
public import GraphMinor.Thomason.UniformCheck
public import GraphMinor.Thomason.UniformReduction
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Certificate rows for one value of `p`

Section 4 of the note `docs/thomason/uniform_minor_bound.tex` checks, for each
`51 ≤ p ≤ 109`, an integer density `c` and one choice of blocks for every
order `n = R + 2, …, c` of a reduced graph, where `R = ⌊25c/67⌋ - 1`. The
reduced graph has at most `q = ⌊(n - R)/2⌋` non-neighbours at each vertex.
A row is accepted by `rowOK` when

* `c ≤ 2.68 p (log₂ p) ^ (1/2)`, shown by integers `a, b` with
  `2 ^ a ≤ p ^ b` and `10000 b c² ≤ 71824 a p²`;
* `R ≥ p - 2`, so that the orders `n = R, R + 1`, where the reduced graph
  is complete, have at least `p - 2` vertices;
* each entry passes the integer test `twoSizeOK` with `m = p - 2`.

We prove that an accepted row gives a `K_p` minor in every graph of density
at least `2.68 p (log₂ p) ^ (1/2)`, by the density reduction of
`UniformReduction.lean`.
-/

public section
namespace GraphMinor.Thomason.Uniform
open Finset SimpleGraph
universe u

/-- One choice of blocks: `u k aN aD` is `⌊n/k⌋` blocks of size `k` with
`A = aN / aD`; `m N2 N3 a2n a2d a3n a3d` is `N2` pairs and `N3` triples with
`A₂ = a2n / a2d` and `A₃ = a3n / a3d`. -/
inductive Entry where
  | u (k aN aD : ℕ)
  | m (N2 N3 a2n a2d a3n a3d : ℕ)

/-- The integer test for one entry at order `n`, with the worst
non-neighbour count `⌊(n - R)/2⌋`. -/
@[expose] def entryOK (m R n : ℕ) : Entry → Bool
  | .u k aN aD => twoSizeOK n ((n - R) / 2) m k 1 (n / k) 0 aN aD 1 1
  | .m N2 N3 a2n a2d a3n a3d => twoSizeOK n ((n - R) / 2) m 2 3 N2 N3 a2n a2d a3n a3d

/-- Consecutive entries for the orders `n, n + 1, …`. -/
@[expose] def entriesOK (m R : ℕ) : ℕ → List Entry → Bool
  | _, [] => true
  | n, e :: es => entryOK m R n e && entriesOK m R (n + 1) es

/-- The test of one certificate row. -/
@[expose] def rowOK (p c a b : ℕ) (es : List Entry) : Bool :=
  decide (4 ≤ p) && decide (3 ≤ c) && decide (0 < b) && decide (2 ^ a ≤ p ^ b) &&
  decide (10000 * b * c ^ 2 ≤ 71824 * a * p ^ 2) &&
  decide (p - 2 ≤ 25 * c / 67 - 1) && decide (25 * c / 67 - 1 + 1 + es.length = c) &&
  entriesOK (p - 2) (25 * c / 67 - 1) (25 * c / 67 - 1 + 2) es

theorem entriesOK_get {m R : ℕ} :
    ∀ (es : List Entry) (n₀ : ℕ), entriesOK m R n₀ es = true →
      ∀ n, n₀ ≤ n → n < n₀ + es.length → ∃ e, entryOK m R n e = true
  | [], _, _, n, h1, h2 => by simp at h2; omega
  | e :: es, n₀, h, n, h1, h2 => by
    simp only [entriesOK, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with h3 | h3
    · exact ⟨e, h3 ▸ h.1⟩
    · exact entriesOK_get es (n₀ + 1) h.2 n h3 (by simp at h2; omega)

/-- `c ≤ 2.68 p (log₂ p) ^ (1/2)` from `2 ^ a ≤ p ^ b` and
`10000 b c² ≤ 71824 a p²`. -/
theorem le_coeff_of_check {p c a b : ℕ} (hp : 1 ≤ p) (hb : 0 < b) (hpow : 2 ^ a ≤ p ^ b)
    (hsq : 10000 * b * c ^ 2 ≤ 71824 * a * p ^ 2) :
    (c : ℝ) ≤ (2.68 : ℝ) * p * Real.sqrt (Real.logb 2 p) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hlog : (a : ℝ) / b ≤ Real.logb 2 p := by
    have hpowR : (2 : ℝ) ^ a ≤ (p : ℝ) ^ b := by exact_mod_cast hpow
    have h := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
      (by positivity : (0 : ℝ) < 2 ^ a) hpowR
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h
    rw [div_le_iff₀ hbR]
    linarith
  have hsqR : (c : ℝ) ^ 2 ≤ (2.68 * p) ^ 2 * ((a : ℝ) / b) := by
    have h : (10000 * b * c ^ 2 : ℝ) ≤ 71824 * a * p ^ 2 := by exact_mod_cast hsq
    rw [mul_div_assoc', le_div_iff₀ hbR]
    nlinarith
  have hlog0 : 0 ≤ Real.logb 2 p := Real.logb_nonneg (by norm_num) hpR
  have hroot : (c : ℝ) ≤ Real.sqrt ((2.68 * p) ^ 2 * Real.logb 2 p) :=
    Real.le_sqrt_of_sq_le (hsqR.trans (mul_le_mul_of_nonneg_left hlog (by positivity)))
  rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)] at hroot

variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- A graph in which no vertex has a non-neighbour other than itself has a
`K_m` minor when it has at least `m` vertices: take `m` single vertices as
blocks in the random block lemma. -/
theorem clique_isIsoMinor_of_complete {m : ℕ} (hq : ∀ v, (nonNbr H v).card ≤ 0)
    (hmn : m ≤ Fintype.card W) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin m))) (Graph.ofSimpleGraph H) := by
  refine clique_isIsoMinor_of_two_sizes H 0 hq 1 1 m 0 le_rfl le_rfl (by simpa using hmn)
    (2 * m + 2) 1 (by positivity) one_pos m ?_
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : (m : ℝ) * (2 * (m : ℝ) + 2)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one (by positivity)]; linarith
  norm_num
  nlinarith [h1]

/-- An accepted row gives a `K_{p-2}` minor in every reduced graph. -/
theorem reduced_clique_of_rowOK {p c a b : ℕ} {es : List Entry}
    (hrow : rowOK p c a b es = true) [Nonempty W] (hW : Fintype.card W ≤ c)
    (hdeg : ∀ v, 2 * (nonNbr H v).card + (25 * c / 67 - 1) ≤ Fintype.card W) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (p - 2)))) (Graph.ofSimpleGraph H) := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hrow
  obtain ⟨⟨⟨⟨⟨⟨⟨hp, hc⟩, hb⟩, hpow⟩, hsq⟩, hR⟩, hlen⟩, hents⟩ := hrow
  set R := 25 * c / 67 - 1
  set n := Fintype.card W
  obtain ⟨v₀⟩ := ‹Nonempty W›
  have hRn : R ≤ n := by have := hdeg v₀; omega
  have hq (v : W) : (nonNbr H v).card ≤ (n - R) / 2 := by
    have := hdeg v; omega
  by_cases hsmall : n ≤ R + 1
  · refine clique_isIsoMinor_of_complete H (fun v => ?_) (by omega)
    have := hq v; omega
  · obtain ⟨e, he⟩ := entriesOK_get es (R + 2) hents n (by omega) (by omega)
    cases e with
    | u k aN aD => exact clique_isIsoMinor_of_twoSizeOK H _ hq rfl he
    | m N2 N3 a2n a2d a3n a3d => exact clique_isIsoMinor_of_twoSizeOK H _ hq rfl he

/-- An accepted row gives a `K_p` minor in every graph of density at least
`c`, by the density reduction. -/
theorem clique_isIsoMinor_of_rowOK {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p c a b : ℕ} {es : List Entry}
    (hrow : rowOK p c a b es = true) (hden : c * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin p))) (Graph.ofSimpleGraph G) := by
  have hrow' := hrow
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hrow'
  obtain ⟨⟨⟨⟨⟨⟨⟨hp, hc⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hrow'
  have h := clique_isIsoMinor_of_reduced G c (p - 2) hc hden
    fun J _ hW hdeg => reduced_clique_of_rowOK J hrow hW hdeg
  rwa [show p - 2 + 2 = p by omega] at h

/-- The density of an accepted row is at most the coefficient of XIII (5.5). -/
theorem le_coeff_of_rowOK {p c a b : ℕ} {es : List Entry} (hrow : rowOK p c a b es = true) :
    (c : ℝ) ≤ (2.68 : ℝ) * p * Real.sqrt (Real.logb 2 p) := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hrow
  obtain ⟨⟨⟨⟨⟨⟨⟨hp, hc⟩, hb⟩, hpow⟩, hsq⟩, hR⟩, hlen⟩, hents⟩ := hrow
  exact le_coeff_of_check (by omega) hb hpow hsq

end GraphMinor.Thomason.Uniform
