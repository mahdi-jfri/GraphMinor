module
public import GraphMinor.Thomason.UniformBlockCounts
public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import GraphMinor.Thomason.DensityReduction
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The density reduction with the rational constant `67/25`

Thomason's Lemma 1 (Math. Proc. Cambridge Philos. Soc. 95 (1984), p. 262)
is proved in `DensityReduction.lean` for any `a > 1` with
`1 + ln (2a) ≤ a`. Section 2 of the note `docs/thomason/uniform_minor_bound.tex`
uses it with the rational value `a = 67/25`: since `e ^ (42/25) > 134/25`,
we get `1 + ln (134/25) ≤ 67/25`.

With integer density `c ≥ 3` and `R = ⌊25c/67⌋ - 1`, this reduces a `K_p`
minor in a graph of density at least `c` to a `K_{p-2}` minor in every
non-null graph with at most `c` vertices in which every vertex has at most
`(n - R)/2` non-neighbours other than itself, where `n` is its number of
vertices.
-/

public section
namespace GraphMinor.Thomason.Uniform
open Finset SimpleGraph
universe u

/-- A vertex, its neighbours and its non-neighbours make up the vertex set. -/
theorem card_nonNbr_add_degree {W : Type*} [Fintype W] [DecidableEq W] (J : SimpleGraph W)
    [DecidableRel J.Adj] (v : W) :
    (nonNbr J v).card + J.degree v + 1 = Fintype.card W := by
  have h1 : nonNbr J v = (univ.erase v).filter (fun w => ¬ J.Adj v w) := by
    ext w; rw [mem_nonNbr]; simp
  have h2 : J.neighborFinset v = (univ.erase v).filter (fun w => J.Adj v w) := by
    ext w
    simp only [mem_neighborFinset, mem_filter, mem_erase, mem_univ, and_true]
    exact ⟨fun h => ⟨(J.ne_of_adj h).symm, h⟩, fun h => h.2⟩
  rw [← card_neighborFinset_eq_degree, h1, h2, add_comm ((univ.erase v).filter _).card,
    card_filter_add_card_filter_not, card_erase_of_mem (mem_univ v), card_univ]
  have : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

/-- The rational value `67/25` satisfies Thomason's condition
`1 + ln (2a) ≤ a`, because `e ^ (42/25)` exceeds `134/25`: the first eight
terms of its series already do. -/
theorem one_add_log_le_rational : 1 + Real.log (2 * (67 / 25 : ℝ)) ≤ 67 / 25 := by
  have hexp := Real.sum_le_exp_of_nonneg (x := (42 / 25 : ℝ)) (by norm_num) 8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hexp
  norm_num at hexp
  have hlt : (2 * (67 / 25 : ℝ)) ≤ Real.exp (42 / 25) := by norm_num; linarith
  have hlog := Real.log_le_log (by norm_num) hlt
  rw [Real.log_exp] at hlog
  linarith

/-- The density reduction of Section 2 of the note: a `K_{q+2}` minor in a
graph of integer density at least `c ≥ 3` follows from a `K_q` minor in
every non-null graph with `n ≤ c` vertices, each with at most
`(n - R) / 2` non-neighbours, where `R = ⌊25c/67⌋ - 1`. -/
theorem clique_isIsoMinor_of_reduced {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c q : ℕ) (hc : 3 ≤ c)
    (hden : c * Fintype.card V ≤ G.edgeFinset.card)
    (hclass : ∀ {W : Type u} [Fintype W] [DecidableEq W] [Nonempty W]
      (J : SimpleGraph W) [DecidableRel J.Adj], Fintype.card W ≤ c →
      (∀ v, 2 * (nonNbr J v).card + (25 * c / 67 - 1) ≤ Fintype.card W) →
      IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q))) (Graph.ofSimpleGraph J)) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (q + 2)))) (Graph.ofSimpleGraph G) := by
  have hcR : (3 : ℝ) ≤ c := by exact_mod_cast hc
  refine clique_isIsoMinor_of_dense_class G (67 / 25) (25 * c / 67) c q
    (by linarith) (by norm_num) one_add_log_le_rational (by ring) hden ?_
  intro W _ _ J _ hW hdeg
  classical
  refine hclass J hW fun v => ?_
  have hsum := card_nonNbr_add_degree J v
  have hR : ((25 * c / 67 : ℕ) : ℝ) ≤ 25 * c / 67 := by
    rw [le_div_iff₀ (by norm_num)]
    have := Nat.div_mul_le_self (25 * c) 67
    exact_mod_cast this
  have hd := hdeg v
  have hR1 : 1 ≤ 25 * c / 67 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  -- `2 deg - n > ⌊25c/67⌋ - 4`, and both sides are integers
  have hint : (25 * c / 67 : ℤ) - 4 < 2 * (J.degree v : ℤ) - Fintype.card W := by
    have : ((25 * c / 67 : ℕ) : ℝ) - 4 < 2 * (J.degree v : ℝ) - Fintype.card W := by linarith
    exact_mod_cast this
  omega

end GraphMinor.Thomason.Uniform
