module

public import GraphMinor.GM13.Defs
public import GraphMinor.GM16.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import GraphMinor.Thomason.ThirtyFourDensity
import GraphMinor.Thomason.ThirtyCase
import GraphMinor.Thomason.CliqueOrderMonotone
import GraphMinor.Thomason.SimpleRepresentation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The exact density implication through 34 vertices

Density 184 forces a 34-vertex clique minor. This density is already
below the exact Thomason coefficient at 31. Restrict the clique branches
to cover every target order from 31 through 34, and use the earlier
proof for smaller orders.
-/

public section
namespace GraphMinor.Thomason
open Graph Set GraphMinor.GM09 GraphMinor.GM16
universe u v

/-- The 34-vertex density bound is below the exact coefficient at 31. -/
theorem thirtyFour_density_le_coefficient_at_31 :
    (184 : ℝ) ≤ (2.68 : ℝ) * 31 * Real.sqrt (Real.logb 2 31) := by
  have hpow : (2 : ℝ) ^ 54 ≤ 31 ^ 11 := by norm_num
  have hh := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
    (by norm_num : (0 : ℝ) < 2 ^ 54) hpow
  rw [Real.logb_pow, Real.logb_pow] at hh
  norm_num at hh
  have hlog : (54 / 11 : ℝ) ≤ Real.logb 2 31 := by linarith only [hh]
  have hroot : (144 / 65 : ℝ) ≤ Real.sqrt (Real.logb 2 31) :=
    (Real.le_sqrt (by norm_num) (by linarith only [hlog])).mpr (by linarith only [hlog])
  linarith only [hroot]

/-- Thomason's exact density implication holds for `1≤p≤34`. -/
theorem hasGraphModel_of_density_of_le_thirtyFour {α : Type u} {β : Type v}
    (G : Graph α β) (p : ℕ) (hp : 1 ≤ p) (hpmax : p ≤ 34)
    (hV : V(G).Finite) (hE : E(G).Finite) (hne : V(G).Nonempty)
    (hs : IsSimpleGraph G)
    (hd : (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 p) *
      (V(G).ncard : ℝ) ≤ (E(G).ncard : ℝ)) :
    GM13.HasGraphModel (completeGraph p) G := by
  classical
  by_cases hp' : p ≤ 30
  · exact hasGraphModel_of_density_of_le_thirty G p hp hp' hV hE hne hs hd
  have hpa : 31 ≤ p := by omega
  have hc : (184 : ℝ) ≤ (2.68 : ℝ) * p * Real.sqrt (Real.logb 2 p) :=
    thirtyFour_density_le_coefficient_at_31 |>.trans (thomason_coefficient_mono (by decide) hpa)
  have hden : 184 * V(G).ncard ≤ E(G).ncard := by
    have hh := (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (V(G).ncard))).trans hd
    exact_mod_cast hh
  let := hV.fintype
  have : Nonempty V(G) := hne.to_subtype
  have hden' : 184 * Fintype.card V(G) ≤ G.toSimpleGraph.edgeFinset.card := by
    rwa [Set.fintypeCard_eq_ncard, toSimpleGraph_edgeFinset_card G hs]
  have hm := clique_isIsoMinor_mono G.toSimpleGraph hpmax
    (clique_thirtyFour_of_density G.toSimpleGraph hden')
  have hVpos : 0 < V(G).ncard := (Set.ncard_pos hV).mpr hne
  have hEpos : 0 < E(G).ncard := (Nat.mul_pos (by decide : 0 < 184) hVpos).trans_le hden
  obtain ⟨e, _⟩ := (Set.ncard_pos hE).mp hEpos
  let : Nonempty β := ⟨e⟩
  exact hasGraphModel_of_simpleGraph_minor G p hV hE hs hm

end GraphMinor.Thomason
