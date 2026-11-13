module
public import GraphMinor.GM13.Defs
public import GraphMinor.GM16.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import GraphMinor.Thomason.DensitySmallCases
import GraphMinor.Thomason.SmallCases
import GraphMinor.GM13.Section6
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Further small parameters in Thomason's bound

The elementary exponential density bound from XIII (6.4) suffices
through `p=8`. Orienting edges preserves both counts. The real coefficient
in XIII (5.5) exceeds the elementary coefficient in this finite range.
-/

public section
namespace GraphMinor.Thomason
open Graph Set GraphMinor.GM09 GraphMinor.GM13 GraphMinor.GM16
universe u v

/-- The elementary density bound of XIII (6.4), stated directly for an
undirected graph with arbitrary edge names. -/
theorem hasGraphModel_of_exponential_density {α : Type u} {β : Type v}
    (G : Graph α β) (p : ℕ) (hp : 1 ≤ p)
    (hV : V(G).Finite) (hE : E(G).Finite) (hne : V(G).Nonempty)
    (hs : IsSimpleGraph G)
    (hd : 2 ^ (p - 3) * V(G).ncard ≤ E(G).ncard) :
    HasGraphModel (completeGraph p) G := by
  by_cases hp1 : p = 1
  · subst p
    exact hasGraphModel_completeGraph_one G hne
  have hVpos := (Set.ncard_pos hV).mpr hne
  have hEpos : 0 < E(G).ncard :=
    (Nat.mul_pos (pow_pos (by decide) _) hVpos).trans_le hd
  obtain ⟨e, _⟩ := (Set.ncard_pos hE).mp hEpos
  let : Nonempty β := ⟨e⟩
  obtain ⟨D, hDV, hDE, hDG⟩ := exists_orientation G hne
  have hmodel := algorithm_6_4_correct (G := D) hp ⟨hDV ▸ hV, hDE ▸ hE⟩
    (hDV ▸ hne) (hDG ▸ hs)
    (show 2 ^ (p - 3) * D.vertexSet.ncard ≤ D.edgeSet.ncard by rwa [hDV, hDE])
  rwa [hDG] at hmodel

/-- The coefficient in Thomason's bound dominates the elementary
exponential coefficient for `2≤p≤8`. -/
theorem exponential_coefficient_le_thomason {p : ℕ} (hp : 2 ≤ p) (hp8 : p ≤ 8) :
    ((2 ^ (p - 3) : ℕ) : ℝ) ≤
      (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 p) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 1 ≤ Real.logb 2 (p : ℝ) := by
    have h := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
      (by norm_num : (0 : ℝ) < 2) hpR
    simpa using h
  have hsqrt : 1 ≤ Real.sqrt (Real.logb 2 (p : ℝ)) := by
    simpa using Real.sqrt_le_sqrt hlog
  by_cases hp7 : p ≤ 7
  · calc
      ((2 ^ (p - 3) : ℕ) : ℝ) ≤ (2.68 : ℝ) * p := by interval_cases p <;> norm_num
      _ ≤ (2.68 : ℝ) * p * Real.sqrt (Real.logb 2 p) := by nlinarith only [hsqrt, hpR]
  · have hpEq : p = 8 := by omega
    subst p
    have hlog8 : Real.logb 2 (8 : ℝ) = 3 := by
      have h := Real.logb_pow (2 : ℝ) (2 : ℝ) 3
      norm_num at h
      exact h
    norm_num only [Nat.cast_ofNat]
    rw [hlog8]
    have hsq : (3 / 2 : ℝ) ≤ Real.sqrt 3 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    nlinarith

/-- Thomason's exact density implication holds throughout `1≤p≤8`.
The proof compares its coefficient with the proved elementary bound. -/
theorem hasGraphModel_of_density_of_le_eight {α : Type u} {β : Type v}
    (G : Graph α β) (p : ℕ) (hp : 1 ≤ p) (hp8 : p ≤ 8)
    (hV : V(G).Finite) (hE : E(G).Finite) (hne : V(G).Nonempty)
    (hs : IsSimpleGraph G)
    (hd : (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 p) *
      (V(G).ncard : ℝ) ≤ (E(G).ncard : ℝ)) :
    HasGraphModel (completeGraph p) G := by
  by_cases hp1 : p = 1
  · subst p
    exact hasGraphModel_completeGraph_one G hne
  have hc := exponential_coefficient_le_thomason (by omega : 2 ≤ p) hp8
  have hdR : ((2 ^ (p - 3) : ℕ) : ℝ) * (V(G).ncard : ℝ) ≤ E(G).ncard :=
    (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)).trans hd
  exact hasGraphModel_of_exponential_density G p hp hV hE hne hs (by exact_mod_cast hdR)

end GraphMinor.Thomason
