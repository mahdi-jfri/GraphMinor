module
public import GraphMinor.GM13.Cited
import GraphMinor.Thomason.FiftyCase
import GraphMinor.Thomason.SimpleRepresentation
import GraphMinor.Thomason.UniformFiniteRange
import GraphMinor.Thomason.UniformMediumRange
import GraphMinor.Thomason.UniformLarge
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Thomason's bound, Graph Minors XIII (5.5)

We prove `GM13.Thomason84Statement`: a non-null simple graph `G` with
`|E(G)| ≥ 2.68 p (log₂ p) ^ (1/2) |V(G)|` has a `K_p` minor. The proof joins
four ranges of `p`:

* `p ≤ 50`: `hasGraphModel_of_density_of_le_fifty` in `FiftyCase.lean`;
* `51 ≤ p ≤ 109`: the certificate rows of `UniformFiniteRange.lean`;
* `110 ≤ p ≤ 10 ^ 44`: the interval certificate of `UniformMediumRange.lean`;
* `p > 10 ^ 44`: the analytic argument of `UniformLarge.lean`.

The last three ranges follow the computer-assisted note
`docs/thomason/uniform_minor_bound.tex`, which uses Thomason's density reduction
(Thomason 1984, Lemma 1, p. 262) and a random partition into blocks.
-/

public section
namespace GraphMinor.Thomason
open Graph Set GraphMinor.GM09 GraphMinor.GM16 GraphMinor.Thomason.Uniform
universe u v

/-- A simple graph whose density is at least `c` for some natural number
`c ≤ 2.68 p (log₂ p) ^ (1/2)` with `c ≥ 1` has a `K_p` minor, if every
finite simple graph of density at least `c` has one. -/
theorem hasGraphModel_of_density_bound {α : Type u} {β : Type v} (G : Graph α β) (p c : ℕ)
    (hV : V(G).Finite) (hE : E(G).Finite) (hne : V(G).Nonempty) (hs : IsSimpleGraph G)
    (hd : (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 p) * (V(G).ncard : ℝ) ≤
      (E(G).ncard : ℝ))
    (hc : (c : ℝ) ≤ 2.68 * p * Real.sqrt (Real.logb 2 p)) (hc1 : 1 ≤ c)
    (hcl : ∀ {V : Type u} [Fintype V] [Nonempty V] (H : SimpleGraph V) [DecidableRel H.Adj],
      c * Fintype.card V ≤ H.edgeFinset.card →
      IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin p))) (Graph.ofSimpleGraph H)) :
    GM13.HasGraphModel (completeGraph p) G := by
  classical
  have hden : c * V(G).ncard ≤ E(G).ncard := by
    have hh := (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (V(G).ncard))).trans hd
    exact_mod_cast hh
  let := hV.fintype
  have : Nonempty V(G) := hne.to_subtype
  have hden' : c * Fintype.card V(G) ≤ G.toSimpleGraph.edgeFinset.card := by
    rwa [Set.fintypeCard_eq_ncard, toSimpleGraph_edgeFinset_card G hs]
  have hm := hcl G.toSimpleGraph hden'
  have hVpos : 0 < V(G).ncard := (Set.ncard_pos hV).mpr hne
  have hEpos : 0 < E(G).ncard := (Nat.mul_pos hc1 hVpos).trans_le hden
  obtain ⟨e, _⟩ := (Set.ncard_pos hE).mp hEpos
  let : Nonempty β := ⟨e⟩
  exact hasGraphModel_of_simpleGraph_minor G p hV hE hs hm

/-- The density `⌊(67/25) p (log₂ p) ^ (1/2)⌋` is at most the coefficient
of XIII (5.5). -/
theorem floor_le_coeff (p : ℕ) :
    ((⌊(67 / 25 : ℝ) * p * Real.sqrt (Real.logb 2 p)⌋₊ : ℕ) : ℝ) ≤
      2.68 * p * Real.sqrt (Real.logb 2 p) := by
  have h : (0 : ℝ) ≤ 67 / 25 * p * Real.sqrt (Real.logb 2 p) := by positivity
  have := Nat.floor_le h
  norm_num at this ⊢
  linarith

/-- **Thomason's bound**, Graph Minors XIII (5.5), for every `p ≥ 1`. -/
theorem thomason84 : GM13.Thomason84Statement.{u, v} := by
  intro α β G p hp hV hE hne hs hd
  by_cases h50 : p ≤ 50
  · exact hasGraphModel_of_density_of_le_fifty G p hp h50 hV hE hne hs hd
  by_cases h109 : p ≤ 109
  · obtain ⟨c, a, b, es, hrow⟩ := exists_rowOK_of_finite p (by omega) h109
    have hc3 : 3 ≤ c := by
      simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hrow
      exact hrow.1.1.1.1.1.1.2
    refine hasGraphModel_of_density_bound G p c hV hE hne hs hd ?_ (by omega)
      fun H _ hden => clique_isIsoMinor_of_rowOK H hrow hden
    simpa using le_coeff_of_rowOK hrow
  have hc1 : 1 ≤ ⌊(67 / 25 : ℝ) * p * Real.sqrt (Real.logb 2 p)⌋₊ := by
    have hlog : (1 : ℝ) ≤ Real.logb 2 p := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
      have : (2 : ℝ) ≤ p := by exact_mod_cast (show 2 ≤ p by omega)
      simpa using this
    have hs1 : (1 : ℝ) ≤ Real.sqrt (Real.logb 2 p) := Real.le_sqrt_of_sq_le (by linarith)
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
    exact Nat.le_floor (by push_cast; nlinarith)
  by_cases h44 : p ≤ 10 ^ 44
  · obtain ⟨I, hI, hpL, hpU⟩ := exists_interval_of_medium p (by omega) h44
    exact hasGraphModel_of_density_bound G p _ hV hE hne hs hd (floor_le_coeff p) hc1
      fun H _ hden => clique_isIsoMinor_of_intervalOK hI hpL hpU H hden
  · exact hasGraphModel_of_density_bound G p _ hV hE hne hs hd (floor_le_coeff p) hc1
      fun H _ hden => clique_isIsoMinor_of_large (by omega) H hden

end GraphMinor.Thomason
