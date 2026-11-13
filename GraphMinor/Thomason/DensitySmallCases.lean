module

public import GraphMinor.GM13.Defs
public import GraphMinor.GM16.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import GraphMinor.GM13.Section6
import GraphMinor.Thomason.SmallCases

/-!
# Small parameters in Thomason's density bound

For parameters two and three the density bound implies at least as many
edges as vertices. Orienting each edge allows us to apply the elementary
clique-model construction of XIII (6.4). The one-vertex case needs no edge.
-/

public section

namespace GraphMinor.Thomason

open Graph Set GraphMinor.GM09 GraphMinor.GM13 GraphMinor.GM16

universe u v

/-- Every non-null graph can be given directions without changing its
underlying graph, as in XIII, Section 2, page 68. -/
theorem exists_orientation {α : Type u} {β : Type v} (G : Graph α β)
    (hne : V(G).Nonempty) :
    ∃ D : Digraph α β, D.vertexSet = V(G) ∧ D.edgeSet = E(G) ∧ D.toGraph = G := by
  classical
  obtain ⟨a, ha⟩ := hne
  let headD (e : β) : α :=
    if he : e ∈ E(G) then Classical.choose (exists_isLink_of_mem_edgeSet he) else a
  let tailD (e : β) : α :=
    if he : e ∈ E(G) then
      Classical.choose (Classical.choose_spec (exists_isLink_of_mem_edgeSet he)) else a
  have hl (e : β) (he : e ∈ E(G)) : G.IsLink e (headD e) (tailD e) := by
    dsimp [headD, tailD]
    simp only [he, ↓reduceDIte]
    exact Classical.choose_spec (Classical.choose_spec (exists_isLink_of_mem_edgeSet he))
  let D : Digraph α β := {
    vertexSet := V(G)
    edgeSet := E(G)
    head := headD
    tail := tailD
    head_mem := fun e he => (hl e he).left_mem
    tail_mem := fun e he => (hl e he).right_mem
  }
  refine ⟨D, rfl, rfl, Graph.ext rfl (fun e x y => ?_)⟩
  simp only [Digraph.toGraph, D]
  constructor
  · rintro ⟨he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hl e he
    · exact (hl e he).symm
  · intro h
    refine ⟨h.edge_mem, ?_⟩
    exact (hl e h.edge_mem).eq_and_eq_or_eq_and_eq h

/-- Thomason's conclusion holds for `1 ≤ p ≤ 3`, with the exact density
hypothesis of XIII (5.5), page 83. The proof uses XIII (6.4). -/
theorem hasGraphModel_of_density_of_le_three {α : Type u} {β : Type v}
    (G : Graph α β) (p : ℕ) (hp : 1 ≤ p) (hp3 : p ≤ 3)
    (hV : V(G).Finite) (hE : E(G).Finite) (hne : V(G).Nonempty)
    (hs : IsSimpleGraph G)
    (hd : (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 p) *
      (V(G).ncard : ℝ) ≤ (E(G).ncard : ℝ)) :
    HasGraphModel (completeGraph p) G := by
  by_cases hp1 : p = 1
  · subst p
    exact hasGraphModel_completeGraph_one G hne
  have hp2 : 2 ≤ p := by omega
  have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hlog : 1 ≤ Real.logb 2 (p : ℝ) := by
    have h := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
      (by norm_num : (0 : ℝ) < 2) hp2'
    simpa using h
  have hsqrt : 1 ≤ Real.sqrt (Real.logb 2 (p : ℝ)) := by
    simpa using Real.sqrt_le_sqrt hlog
  have hc : 1 ≤ (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 (p : ℝ)) := by
    nlinarith
  have hVE : V(G).ncard ≤ E(G).ncard := by
    have hnonneg : (0 : ℝ) ≤ V(G).ncard := Nat.cast_nonneg _
    have hv : (V(G).ncard : ℝ) ≤ E(G).ncard :=
      le_trans (by nlinarith) hd
    exact_mod_cast hv
  have hepos : 0 < E(G).ncard := lt_of_lt_of_le ((Set.ncard_pos hV).mpr hne) hVE
  obtain ⟨e, he⟩ := (Set.ncard_pos hE).mp hepos
  have : Nonempty β := ⟨e⟩
  obtain ⟨D, hDV, hDE, hDG⟩ := exists_orientation G hne
  have hfin : D.IsFinite := ⟨hDV ▸ hV, hDE ▸ hE⟩
  have hmodel := algorithm_6_4_correct (G := D) hp hfin (hDV ▸ hne)
    (hDG ▸ hs) (show 2 ^ (p - 3) * D.vertexSet.ncard ≤ D.edgeSet.ncard by
      rw [Nat.sub_eq_zero_of_le hp3, pow_zero, one_mul, hDV, hDE]
      exact hVE)
  rwa [hDG] at hmodel

end GraphMinor.Thomason
