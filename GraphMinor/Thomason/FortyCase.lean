module

public import GraphMinor.GM13.Defs
public import GraphMinor.GM16.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import GraphMinor.Thomason.FortyDensity
import GraphMinor.Thomason.ThirtySixCase
import GraphMinor.Thomason.CliqueOrderMonotone
import GraphMinor.Thomason.SimpleRepresentation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The exact density implication through 40 vertices

Density 222 forces a 40-vertex clique minor. This density is already
below the exact Thomason coefficient at 37. Restrict the clique branches
to cover every target order from 37 through 40, and use the earlier
proof for smaller orders.
-/

public section
namespace GraphMinor.Thomason
open Graph Set GraphMinor.GM09 GraphMinor.GM16
universe u v

/-- The 40-vertex density bound is below the exact coefficient at 37. -/
theorem forty_density_le_coefficient_at_37 :
    (222 : ℝ) ≤ (2.68 : ℝ) * 37 * Real.sqrt (Real.logb 2 37) := by
  have hpow : (2 : ℝ) ^ 26 ≤ 37 ^ 5 := by norm_num
  have hh := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
    (by norm_num : (0 : ℝ) < 2 ^ 26) hpow
  rw [Real.logb_pow, Real.logb_pow] at hh
  norm_num at hh
  have hlog : (26 / 5 : ℝ) ≤ Real.logb 2 37 := by linarith only [hh]
  have hroot : (9 / 4 : ℝ) ≤ Real.sqrt (Real.logb 2 37) :=
    (Real.le_sqrt (by norm_num) (by linarith only [hlog])).mpr (by linarith only [hlog])
  linarith only [hroot]

/-- Thomason's exact density implication holds for `1≤p≤40`. -/
theorem hasGraphModel_of_density_of_le_forty {α : Type u} {β : Type v}
    (G : Graph α β) (p : ℕ) (hp : 1 ≤ p) (hpmax : p ≤ 40)
    (hV : V(G).Finite) (hE : E(G).Finite) (hne : V(G).Nonempty)
    (hs : IsSimpleGraph G)
    (hd : (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 p) *
      (V(G).ncard : ℝ) ≤ (E(G).ncard : ℝ)) :
    GM13.HasGraphModel (completeGraph p) G := by
  classical
  by_cases hp' : p ≤ 36
  · exact hasGraphModel_of_density_of_le_thirtySix G p hp hp' hV hE hne hs hd
  have hpa : 37 ≤ p := by omega
  have hc : (222 : ℝ) ≤ (2.68 : ℝ) * p * Real.sqrt (Real.logb 2 p) :=
    forty_density_le_coefficient_at_37 |>.trans (thomason_coefficient_mono (by decide) hpa)
  have hden : 222 * V(G).ncard ≤ E(G).ncard := by
    have hh := (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (V(G).ncard))).trans hd
    exact_mod_cast hh
  let := hV.fintype
  have : Nonempty V(G) := hne.to_subtype
  have hden' : 222 * Fintype.card V(G) ≤ G.toSimpleGraph.edgeFinset.card := by
    rwa [Set.fintypeCard_eq_ncard, toSimpleGraph_edgeFinset_card G hs]
  have hm := clique_isIsoMinor_mono G.toSimpleGraph hpmax
    (clique_forty_of_density G.toSimpleGraph hden')
  have hVpos : 0 < V(G).ncard := (Set.ncard_pos hV).mpr hne
  have hEpos : 0 < E(G).ncard := (Nat.mul_pos (by decide : 0 < 222) hVpos).trans_le hden
  obtain ⟨e, _⟩ := (Set.ncard_pos hE).mp hEpos
  let : Nonempty β := ⟨e⟩
  exact hasGraphModel_of_simpleGraph_minor G p hV hE hs hm

end GraphMinor.Thomason
