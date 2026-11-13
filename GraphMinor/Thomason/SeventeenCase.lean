module

public import GraphMinor.GM13.Defs
public import GraphMinor.GM16.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import GraphMinor.Thomason.SeventeenDensity
import GraphMinor.Thomason.SixteenCase
import GraphMinor.Thomason.SimpleRepresentation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The exact 17-vertex case of Thomason's bound

An integer power comparison bounds the binary logarithm below. This
shows that the exact coefficient in XIII (5.5) exceeds density 92.
The proved density theorem transfers to arbitrary edge names.
-/

public section
namespace GraphMinor.Thomason
open Graph Set GraphMinor.GM09 GraphMinor.GM16
universe u v

/-- The exact Thomason coefficient at 17 is at least 92. -/
theorem density_le_thomason_coefficient_seventeen :
    (92 : ℝ) ≤ (2.68 : ℝ) * 17 * Real.sqrt (Real.logb 2 17) := by
  have hpow : (2 : ℝ) ^ 49 ≤ 17 ^ 12 := by norm_num
  have hh := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
    (by norm_num : (0 : ℝ) < 2 ^ 49) hpow
  rw [Real.logb_pow, Real.logb_pow] at hh
  norm_num at hh
  have hlog : (49 / 12 : ℝ) ≤ Real.logb 2 17 := by linarith only [hh]
  have hroot : (99 / 49 : ℝ) ≤ Real.sqrt (Real.logb 2 17) :=
    (Real.le_sqrt (by norm_num) (by linarith only [hlog])).mpr (by linarith only [hlog])
  linarith only [hroot]

/-- The exact density implication at 17, with arbitrary ambient types. -/
theorem hasGraphModel_of_density_seventeen {α : Type u} {β : Type v}
    (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (hne : V(G).Nonempty) (hs : IsSimpleGraph G)
    (hd : (2.68 : ℝ) * 17 * Real.sqrt (Real.logb 2 17) *
      (V(G).ncard : ℝ) ≤ (E(G).ncard : ℝ)) :
    GM13.HasGraphModel (completeGraph 17) G := by
  classical
  have hden : 92 * V(G).ncard ≤ E(G).ncard := by
    have hh := (mul_le_mul_of_nonneg_right density_le_thomason_coefficient_seventeen
      (Nat.cast_nonneg (V(G).ncard))).trans hd
    exact_mod_cast hh
  let := hV.fintype
  have : Nonempty V(G) := hne.to_subtype
  have hden' : 92 * Fintype.card V(G) ≤ G.toSimpleGraph.edgeFinset.card := by
    rwa [Set.fintypeCard_eq_ncard, toSimpleGraph_edgeFinset_card G hs]
  have hm := clique_seventeen_of_density G.toSimpleGraph hden'
  have hVpos : 0 < V(G).ncard := (Set.ncard_pos hV).mpr hne
  have hEpos : 0 < E(G).ncard := (Nat.mul_pos (by decide : 0 < 92) hVpos).trans_le hden
  obtain ⟨e, _⟩ := (Set.ncard_pos hE).mp hEpos
  let : Nonempty β := ⟨e⟩
  exact hasGraphModel_of_simpleGraph_minor G 17 hV hE hs hm

/-- Thomason's exact density implication holds for `1≤p≤17`. -/
theorem hasGraphModel_of_density_of_le_seventeen {α : Type u} {β : Type v}
    (G : Graph α β) (p : ℕ) (hp : 1 ≤ p) (hpmax : p ≤ 17)
    (hV : V(G).Finite) (hE : E(G).Finite) (hne : V(G).Nonempty)
    (hs : IsSimpleGraph G)
    (hd : (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 p) *
      (V(G).ncard : ℝ) ≤ (E(G).ncard : ℝ)) :
    GM13.HasGraphModel (completeGraph p) G := by
  by_cases hp' : p ≤ 16
  · exact hasGraphModel_of_density_of_le_sixteen G p hp hp' hV hE hne hs hd
  · have heq : p = 17 := by omega
    subst p
    exact hasGraphModel_of_density_seventeen G hV hE hne hs hd

end GraphMinor.Thomason
