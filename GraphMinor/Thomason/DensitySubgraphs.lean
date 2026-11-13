module

public import GraphMinor.Statement
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card
import GraphMinor.GM01.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Subgraphs used in the dense-minor reduction

Deleting vertices or edges gives minors. We also trim a spanning simple
subgraph to any prescribed number of edges. This lets the dense-minor
argument use a graph with exactly `d` edges per vertex before applying
the degree-sum formula.
-/

public section

namespace GraphMinor.Thomason

open SimpleGraph Graph Set

universe u
variable {V : Type u} [Fintype V]

omit [Fintype V] in
/-- A spanning simple subgraph is a minor, by deleting its omitted edges. -/
theorem isIsoMinor_ofSimpleGraph_of_le {H G : SimpleGraph V} (hle : H ≤ G) :
    IsIsoMinor (Graph.ofSimpleGraph H) (Graph.ofSimpleGraph G) := by
  rw [GM01.ofSimpleGraph_eq_toGraph H, GM01.ofSimpleGraph_eq_toGraph G]
  apply GM01.isIsoMinor_toGraph_of_le
  exact ⟨fun _ _ => trivial, fun _ _ h => hle h⟩

/-- An induced simple subgraph is a minor, using singleton branches. -/
theorem isIsoMinor_ofSimpleGraph_induce (G : SimpleGraph V) (S : Set V) :
    IsIsoMinor (Graph.ofSimpleGraph (G.induce S)) (Graph.ofSimpleGraph G) := by
  classical
  let Γ := SimpleGraph.toSubgraph G le_top
  let K : S → (⊤ : SimpleGraph V).Subgraph :=
    fun x => (⊤ : SimpleGraph V).singletonSubgraph x.val
  rw [GM01.ofSimpleGraph_eq_toGraph G]
  apply GM01.isIsoMinor_ofSimpleGraph_of_connected_subgraphs (G.induce S)
    (Set.toFinite Γ.verts) K
  · intro x
    exact ⟨fun _ _ => trivial, fun _ _ h => h.elim⟩
  · intro x
    exact SimpleGraph.Subgraph.singletonSubgraph_connected
  · intro x y hxy
    exact Set.disjoint_singleton.mpr (fun h => hxy (Subtype.ext h))
  · intro x y hxy
    exact ⟨x.val, rfl, y.val, rfl, hxy⟩

/-- Retaining a subset of the edge set with the prescribed cardinality
gives a spanning subgraph. -/
theorem exists_spanning_subgraph_card (G : SimpleGraph V) (k : ℕ)
    (hk : k ≤ G.edgeSet.ncard) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.edgeSet.ncard = k := by
  classical
  have hk' : k ≤ G.edgeFinset.card := by
    simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hk
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hk'
  let H := SimpleGraph.fromEdgeSet (S : Set (Sym2 V))
  have hle : H ≤ G := by
    apply (SimpleGraph.fromEdgeSet_le (G := G)).mpr
    intro e he
    exact SimpleGraph.mem_edgeFinset.mp (hS he.1)
  have hE : H.edgeSet = (S : Set (Sym2 V)) := by
    ext e
    simp only [H, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Finset.mem_coe,
      Sym2.mem_diagSet]
    exact ⟨And.left, fun he => ⟨he, G.not_isDiag_of_mem_edgeFinset (hS he)⟩⟩
  exact ⟨H, hle, by rw [hE, Set.ncard_coe_finset, hcard]⟩

end GraphMinor.Thomason
