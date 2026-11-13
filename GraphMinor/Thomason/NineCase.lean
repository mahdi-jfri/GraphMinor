module

public import GraphMinor.GM13.Defs
public import GraphMinor.GM16.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import GraphMinor.Thomason.NineDensity
import GraphMinor.Thomason.MinorGraphModel
import GraphMinor.Thomason.GeneralGraphCriterion
import GraphMinor.Thomason.ElementaryDensity
import GraphMinor.GM01.ForestGraphs
import GraphMinor.Minor.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The exact nine-vertex case of Thomason's bound

A power comparison proves that the coefficient for nine vertices is
larger than forty-two. The proved forty-two-density theorem gives the
clique minor. The simple-graph isomorphism preserves actual vertex and
edge counts, and minor-model extraction returns the model required by XIII.
-/

public section
namespace GraphMinor.Thomason
open Graph Set GraphMinor.GM09 GraphMinor.GM16
universe u v

/-- The coefficient in XIII (5.5) at `p=9` exceeds forty-two. -/
theorem forty_two_le_thomason_coefficient_nine :
    (42 : ℝ) ≤ (2.68 : ℝ) * 9 * Real.sqrt (Real.logb 2 9) := by
  have hpow : (2 : ℝ) ^ 25 ≤ 9 ^ 8 := by norm_num
  have hh := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
    (by norm_num : (0 : ℝ) < 2 ^ 25) hpow
  rw [Real.logb_pow, Real.logb_pow] at hh
  norm_num at hh
  have hlog : (25 / 8 : ℝ) ≤ Real.logb 2 9 := by linarith only [hh]
  have hroot : (7 / 4 : ℝ) ≤ Real.sqrt (Real.logb 2 9) :=
    (Real.le_sqrt (by norm_num) (by linarith only [hlog])).mpr (by linarith only [hlog])
  linarith only [hroot]

/-- Thomason's exact density implication at nine vertices, with arbitrary
ambient vertex and edge types as in XIII (5.5). -/
theorem hasGraphModel_of_density_nine {α : Type u} {β : Type v}
    (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (hne : V(G).Nonempty) (hs : IsSimpleGraph G)
    (hd : (2.68 : ℝ) * 9 * Real.sqrt (Real.logb 2 9) *
      (V(G).ncard : ℝ) ≤ (E(G).ncard : ℝ)) :
    GM13.HasGraphModel (completeGraph 9) G := by
  classical
  have hden : 42 * V(G).ncard ≤ E(G).ncard := by
    have hh := (mul_le_mul_of_nonneg_right forty_two_le_thomason_coefficient_nine
      (Nat.cast_nonneg (V(G).ncard))).trans hd
    exact_mod_cast hh
  let := hV.fintype
  have : Nonempty V(G) := hne.to_subtype
  let : G.Simple := {
    not_isLoopAt := fun e x h => hs.1 e h.edge_mem x h
    eq_of_isLink := fun {e f x y} h₁ h₂ => hs.2 _ h₁.edge_mem _ h₂.edge_mem _ _ h₁ h₂ }
  let φ := GM01.simpleGraphIso G
  have hverts : Fintype.card V(G) = V(G).ncard := Set.fintypeCard_eq_ncard _
  have hedges : G.toSimpleGraph.edgeFinset.card = E(G).ncard := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
    exact (Nat.card_congr φ.edgeEquiv).trans (Nat.card_coe_set_eq _)
  have hden' : 42 * Fintype.card V(G) ≤ G.toSimpleGraph.edgeFinset.card := by
    rwa [hverts, hedges]
  have hm := clique_nine_of_density_forty_two G.toSimpleGraph hden'
  have hm' : IsIsoMinor (completeGraph 9) G := by
    rw [completeGraph_eq_ofSimpleGraph_top]
    exact hm.trans (φ.isIsoMinor_left (.refl G))
  have hVpos : 0 < V(G).ncard := (Set.ncard_pos hV).mpr hne
  have hEpos : 0 < E(G).ncard := (Nat.mul_pos (by decide : 0 < 42) hVpos).trans_le hden
  obtain ⟨e, _⟩ := (Set.ncard_pos hE).mp hEpos
  let : Nonempty β := ⟨e⟩
  exact hasGraphModel_of_isIsoMinor hV hE hm'

/-- Thomason's exact density implication holds for `1≤p≤9`. -/
theorem hasGraphModel_of_density_of_le_nine {α : Type u} {β : Type v}
    (G : Graph α β) (p : ℕ) (hp : 1 ≤ p) (hp9 : p ≤ 9)
    (hV : V(G).Finite) (hE : E(G).Finite) (hne : V(G).Nonempty)
    (hs : IsSimpleGraph G)
    (hd : (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 p) *
      (V(G).ncard : ℝ) ≤ (E(G).ncard : ℝ)) :
    GM13.HasGraphModel (completeGraph p) G := by
  by_cases hp8 : p ≤ 8
  · exact hasGraphModel_of_density_of_le_eight G p hp hp8 hV hE hne hs hd
  · have heq : p = 9 := by omega
    subst p
    exact hasGraphModel_of_density_nine G hV hE hne hs hd

end GraphMinor.Thomason
