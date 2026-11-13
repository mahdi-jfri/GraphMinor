module

public import GraphMinor.GM13.Defs
public import GraphMinor.GM16.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import GraphMinor.Thomason.ElevenDensity
import GraphMinor.Thomason.MinorGraphModel
import GraphMinor.Thomason.GeneralGraphCriterion
import GraphMinor.Thomason.TenCase
import GraphMinor.GM01.ForestGraphs
import GraphMinor.Minor.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The exact eleven-vertex case of Thomason's bound

A power comparison proves that the coefficient for eleven vertices is
larger than fifty-four. The proved fifty-four-density theorem gives the
clique minor. The simple-graph isomorphism preserves actual vertex and
edge counts, and minor-model extraction returns the model required by XIII.
-/

public section
namespace GraphMinor.Thomason
open Graph Set GraphMinor.GM09 GraphMinor.GM16
universe u v

/-- The coefficient in XIII (5.5) at `p=11` exceeds fifty-four. -/
theorem fifty_four_le_thomason_coefficient_eleven :
    (54 : ℝ) ≤ (2.68 : ℝ) * 11 * Real.sqrt (Real.logb 2 11) := by
  have hpow : (2 : ℝ) ^ 17 ≤ 11 ^ 5 := by norm_num
  have hh := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
    (by norm_num : (0 : ℝ) < 2 ^ 17) hpow
  rw [Real.logb_pow, Real.logb_pow] at hh
  norm_num at hh
  have hlog : (17 / 5 : ℝ) ≤ Real.logb 2 11 := by linarith only [hh]
  have hroot : (11 / 6 : ℝ) ≤ Real.sqrt (Real.logb 2 11) :=
    (Real.le_sqrt (by norm_num) (by linarith only [hlog])).mpr (by linarith only [hlog])
  linarith only [hroot]

/-- Thomason's exact density implication at eleven vertices, with arbitrary
ambient vertex and edge types as in XIII (5.5). -/
theorem hasGraphModel_of_density_eleven {α : Type u} {β : Type v}
    (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (hne : V(G).Nonempty) (hs : IsSimpleGraph G)
    (hd : (2.68 : ℝ) * 11 * Real.sqrt (Real.logb 2 11) *
      (V(G).ncard : ℝ) ≤ (E(G).ncard : ℝ)) :
    GM13.HasGraphModel (completeGraph 11) G := by
  classical
  have hden : 54 * V(G).ncard ≤ E(G).ncard := by
    have hh := (mul_le_mul_of_nonneg_right fifty_four_le_thomason_coefficient_eleven
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
  have hden' : 54 * Fintype.card V(G) ≤ G.toSimpleGraph.edgeFinset.card := by
    rwa [hverts, hedges]
  have hm := clique_eleven_of_density_fifty_four G.toSimpleGraph hden'
  have hm' : IsIsoMinor (completeGraph 11) G := by
    rw [completeGraph_eq_ofSimpleGraph_top]
    exact hm.trans (φ.isIsoMinor_left (.refl G))
  have hVpos : 0 < V(G).ncard := (Set.ncard_pos hV).mpr hne
  have hEpos : 0 < E(G).ncard := (Nat.mul_pos (by decide : 0 < 54) hVpos).trans_le hden
  obtain ⟨e, _⟩ := (Set.ncard_pos hE).mp hEpos
  let : Nonempty β := ⟨e⟩
  exact hasGraphModel_of_isIsoMinor hV hE hm'

/-- Thomason's exact density implication holds for `1≤p≤11`. -/
theorem hasGraphModel_of_density_of_le_eleven {α : Type u} {β : Type v}
    (G : Graph α β) (p : ℕ) (hp : 1 ≤ p) (hp11 : p ≤ 11)
    (hV : V(G).Finite) (hE : E(G).Finite) (hne : V(G).Nonempty)
    (hs : IsSimpleGraph G)
    (hd : (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 p) *
      (V(G).ncard : ℝ) ≤ (E(G).ncard : ℝ)) :
    GM13.HasGraphModel (completeGraph p) G := by
  by_cases hp10 : p ≤ 10
  · exact hasGraphModel_of_density_of_le_ten G p hp hp10 hV hE hne hs hd
  · have heq : p = 11 := by omega
    subst p
    exact hasGraphModel_of_density_eleven G hV hE hne hs hd

end GraphMinor.Thomason
