module

public import GraphMinor.Thomason.ContractionCount
public import GraphMinor.Statement
public import Mathlib.Combinatorics.Graph.Simple
import GraphMinor.GM01.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# An edge contraction is a minor

The retained endpoint has the two endpoints as its branch. Every other
vertex has a singleton branch. These branches prove that the contraction
used in Thomason's dense-minor reduction is a minor of the original graph.
-/

public section

namespace GraphMinor.Thomason

open SimpleGraph Graph Set

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Each edge after contraction comes from an old edge, possibly with its
removed endpoint replaced by the retained endpoint. -/
theorem edgeContraction_adj_cases {u v : V} {x y : ({v}ᶜ : Set V)}
    (h : (edgeContraction G u v).Adj x y) :
    G.Adj x.val y.val ∨ (x.val = u ∧ G.Adj v y.val) ∨
      (y.val = u ∧ G.Adj x.val v) := by
  have he : s(x.val, y.val) ∈ contractionEdges G u v := h.1
  rcases Finset.mem_union.mp he with he | he
  · exact Or.inl (G.deleteIncidenceSet_le v (SimpleGraph.mem_edgeFinset.mp he))
  · obtain ⟨w, hw, he⟩ := Finset.mem_image.mp he
    have hwv : G.Adj v w := (G.mem_neighborFinset v w).mp (Finset.mem_sdiff.mp hw).1
    rcases Sym2.eq_iff.mp he with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · exact Or.inr (Or.inl ⟨hx.symm, hy ▸ hwv⟩)
    · exact Or.inr (Or.inr ⟨hy.symm, hx ▸ hwv.symm⟩)

/-- The edge contraction has a model with a two-vertex branch at the
retained endpoint and singleton branches elsewhere. Thus it is a minor. -/
theorem edgeContraction_isIsoMinor {u v : V} (huv : G.Adj u v) :
    IsIsoMinor (Graph.ofSimpleGraph (edgeContraction G u v)) (Graph.ofSimpleGraph G) := by
  classical
  let Γ := SimpleGraph.toSubgraph G le_top
  let K : ({v}ᶜ : Set V) → (⊤ : SimpleGraph V).Subgraph := fun x =>
    if x.val = u then (⊤ : SimpleGraph V).subgraphOfAdj huv.ne
    else (⊤ : SimpleGraph V).singletonSubgraph x.val
  have hverts (x : ({v}ᶜ : Set V)) :
      (K x).verts = if x.val = u then {u, v} else {x.val} := by
    dsimp [K]
    split_ifs <;> rfl
  have hself (x : ({v}ᶜ : Set V)) : x.val ∈ (K x).verts := by
    rw [hverts]
    split_ifs with hx
    · exact Or.inl hx
    · exact rfl
  have hremoved (x : ({v}ᶜ : Set V)) (hx : x.val = u) : v ∈ (K x).verts := by
    rw [hverts, ite_eq_left hx]
    exact Or.inr rfl
  rw [GM01.ofSimpleGraph_eq_toGraph G]
  apply GM01.isIsoMinor_ofSimpleGraph_of_connected_subgraphs (edgeContraction G u v)
    (Set.toFinite Γ.verts) K
  · intro x
    dsimp [K]
    split_ifs with hx
    · refine ⟨fun _ _ => trivial, fun a b hab => ?_⟩
      change s(u, v) = s(a, b) at hab
      change G.Adj a b
      rw [← G.mem_edgeSet, ← hab]
      exact huv
    · exact ⟨fun _ _ => trivial, fun _ _ h => h.elim⟩
  · intro x
    dsimp [K]
    split_ifs
    · exact SimpleGraph.Subgraph.subgraphOfAdj_connected huv.ne
    · exact SimpleGraph.Subgraph.singletonSubgraph_connected
  · intro x y hxy
    rw [hverts, hverts]
    split_ifs with hx hy hy
    · exact (hxy (Subtype.ext (hx.trans hy.symm))).elim
    · apply Set.disjoint_left.mpr
      intro a ha hb
      have hay : a = y.val := hb
      subst a
      rcases ha with h | h
      · exact hy h
      · exact y.property h
    · apply Set.disjoint_left.mpr
      intro a ha hb
      have hax : a = x.val := ha
      subst a
      rcases hb with h | h
      · exact hx h
      · exact x.property h
    · exact Set.disjoint_singleton.mpr (fun h => hxy (Subtype.ext h))
  · intro x y hxy
    rcases edgeContraction_adj_cases G hxy with h | ⟨hx, h⟩ | ⟨hy, h⟩
    · exact ⟨x.val, hself x, y.val, hself y, h⟩
    · exact ⟨v, hremoved x hx, y.val, hself y, h⟩
    · exact ⟨x.val, hself x, v, hremoved y hy, h⟩

end GraphMinor.Thomason
