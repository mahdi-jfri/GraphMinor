module
public import GraphMinor.GM13.Defs
public import GraphMinor.GM16.Defs
public import Mathlib.Data.Nat.Log
import GraphMinor.Thomason.IntegralDensityCriterion
import GraphMinor.Thomason.MinorGraphModel
import GraphMinor.GM01.ForestGraphs
import GraphMinor.Minor.Basic
import Lean.Elab.Tactic.Omega

/-!
# The density criterion for graphs with arbitrary edge names

A simple graph in the sense of XIII is isomorphic to the simple graph
on its actual vertex set. This preserves both counts. Apply the integer
density criterion there and transfer the resulting minor back to the
original edge names, then extract the edge-indexed model of XIII.
-/

public section
namespace GraphMinor.Thomason
open Graph Set GraphMinor.GM09 GraphMinor.GM16
universe u v

/-- The complete graph used in XIII agrees with the graph associated to
the complete simple graph. -/
theorem completeGraph_eq_ofSimpleGraph_top (q : ℕ) :
    completeGraph q = Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q)) := by
  ext e x y
  · rfl
  · change (x ≠ y ∧ e = s(x, y)) ↔
      (e = s(x, y) ∧ e ∈ (⊤ : SimpleGraph (Fin q)).edgeSet)
    constructor
    · rintro ⟨hxy, rfl⟩
      exact ⟨rfl, (SimpleGraph.mem_edgeSet _).mpr hxy⟩
    · rintro ⟨rfl, he⟩
      exact ⟨(SimpleGraph.mem_edgeSet _).mp he, rfl⟩

/-- The integer density criterion in the exact graph-model language of
XIII. The graph may have arbitrary ambient vertex and edge types. -/
theorem hasGraphModel_of_integral_density {α : Type u} {β : Type v}
    (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (hne : V(G).Nonempty) (hs : IsSimpleGraph G) (d b k q : ℕ)
    (hscale : 2679 * (b + 4) ≤ 1000 * d)
    (hden : d * V(G).ncard ≤ E(G).ncard) (hk : 0 < k)
    (hroom : (q - 1) * (k + 2 * Nat.log 2 k + 1) + (Nat.log 2 k + 3) ≤ b)
    (hpower : (q - 1) * d ^ k <
      (2 ^ k * (b - (q - 1) * (k + 2 * Nat.log 2 k + 1) + 1 - k)) ^ k) :
    GM13.HasGraphModel (completeGraph q) G := by
  classical
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
  have hden' : d * Fintype.card V(G) ≤ G.toSimpleGraph.edgeFinset.card := by
    rwa [hverts, hedges]
  have hm := clique_isIsoMinor_of_integral_density G.toSimpleGraph d b k q
    hscale hden' hk hroom hpower
  have hm' : IsIsoMinor (completeGraph q) G := by
    rw [completeGraph_eq_ofSimpleGraph_top]
    exact hm.trans (φ.isIsoMinor_left (.refl G))
  have hdpos : 0 < d := by omega
  have hVpos : 0 < V(G).ncard := (Set.ncard_pos hV).mpr hne
  have hEpos : 0 < E(G).ncard := (Nat.mul_pos hdpos hVpos).trans_le hden
  obtain ⟨e, _⟩ := (Set.ncard_pos hE).mp hEpos
  let : Nonempty β := ⟨e⟩
  exact hasGraphModel_of_isIsoMinor hV hE hm'

end GraphMinor.Thomason
