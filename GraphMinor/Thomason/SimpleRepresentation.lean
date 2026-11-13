module

public import GraphMinor.GM13.Defs
public import GraphMinor.GM16.Defs
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.GM01.ForestGraphs
import GraphMinor.Thomason.MinorGraphModel
import GraphMinor.Thomason.GeneralGraphCriterion
import GraphMinor.Minor.Basic

/-!
# Transferring the finite density cases to arbitrary edge names

The simple graph on the actual vertex set has exactly the same edges
as a simple graph of XIII, through an explicit graph isomorphism. Its
clique minors therefore give the edge-indexed models required by XIII.
These lemmas share the representation argument across numeric cases.
-/

public section
namespace GraphMinor.Thomason
open Graph Set GraphMinor.GM09 GraphMinor.GM16
universe u v

/-- Simplicity in the interface implies Mathlib's simple-graph class. -/
theorem simple_of_isSimpleGraph {α : Type u} {β : Type v} {G : Graph α β}
    (hs : IsSimpleGraph G) : G.Simple where
  not_isLoopAt e x h := hs.1 e h.edge_mem x h
  eq_of_isLink {e f x y} h₁ h₂ := hs.2 e h₁.edge_mem f h₂.edge_mem x y h₁ h₂

/-- Passing to the simple graph on the actual vertices preserves the
number of edges, including their distinct original names. -/
theorem toSimpleGraph_edgeFinset_card {α : Type u} {β : Type v} (G : Graph α β)
    [Fintype V(G)] [DecidableRel G.toSimpleGraph.Adj] (hs : IsSimpleGraph G) :
    G.toSimpleGraph.edgeFinset.card = E(G).ncard := by
  classical
  let := simple_of_isSimpleGraph hs
  let φ := GM01.simpleGraphIso G
  rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr φ.edgeEquiv).trans (Nat.card_coe_set_eq _)

/-- A clique minor of the simple representation transfers to the exact
model notion of XIII. Nonemptiness of the ambient edge type permits
minor-model extraction; density supplies it in the applications. -/
theorem hasGraphModel_of_simpleGraph_minor {α : Type u} {β : Type v} [Nonempty β]
    (G : Graph α β) (p : ℕ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hs : IsSimpleGraph G)
    (hm : IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin p)))
      (Graph.ofSimpleGraph G.toSimpleGraph)) :
    GM13.HasGraphModel (completeGraph p) G := by
  let := simple_of_isSimpleGraph hs
  let φ := GM01.simpleGraphIso G
  have hm' : IsIsoMinor (completeGraph p) G := by
    rw [completeGraph_eq_ofSimpleGraph_top]
    exact hm.trans (φ.isIsoMinor_left (.refl G))
  exact hasGraphModel_of_isIsoMinor hV hE hm'

end GraphMinor.Thomason
