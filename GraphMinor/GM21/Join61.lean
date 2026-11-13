module

public import GraphMinor.GM21.Cited
public import GraphMinor.GM21.Defs
public import GraphMinor.GM10.TreeWidth
public import GraphMinor.GM13.Defs
import GraphMinor.GM04.Decomposition.Basic
import GraphMinor.GM21.LinkageLemmas
import GraphMinor.GM10.TangleLemmas
import GraphMinor.GM13.Section2
import GraphMinor.GM13.Section6a

/-!
# Join of Graph Minors XIII (6.1) and Graph Minors XXI

This file bridges the digraph, separation, connected-subgraph, model, and `δ`-folio definitions of
Graph Minors XIII (`GraphMinor.GM13`) and Graph Minors XXI (`GraphMinor.GM21`), and proves XXI's
cited hypothesis `GM21.GM13Theorem61Statement` unconditionally from `GM13.theorem_6_1_proof`.

## Main results

- `GM21.gm13Theorem61`: proves `GM21.GM13Theorem61Statement.{u, v}` unconditionally from
  `GM13.theorem_6_1_proof`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Function Classical
open Hypergraph GraphMinor.Surface GraphMinor.GM10

universe u v

variable {α : Type u} {β : Type v}

/-! ## Section 1: Digraph and Subgraph Bridges between `GM21` and `GM13` -/

namespace Digraph

/-- Convert a `GM21.Digraph α β` to the corresponding `GM13.Digraph α β`. -/
abbrev toGM13 (G : Digraph α β) : GM13.Digraph α β where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet
  head := G.head
  tail := G.tail
  head_mem _ he := G.head_mem _ he
  tail_mem _ he := G.tail_mem _ he

@[simp]
theorem vertexSet_toGM13 (G : Digraph α β) : G.toGM13.vertexSet = G.vertexSet := rfl

@[simp]
theorem edgeSet_toGM13 (G : Digraph α β) : G.toGM13.edgeSet = G.edgeSet := rfl

@[simp]
theorem head_toGM13 (G : Digraph α β) : G.toGM13.head = G.head := rfl

@[simp]
theorem tail_toGM13 (G : Digraph α β) : G.toGM13.tail = G.tail := rfl

/-- Every `GM21.Digraph` converts to a finite `GM13.Digraph`. -/
theorem isFinite_toGM13 (G : Digraph α β) : G.toGM13.IsFinite :=
  ⟨G.vertexSet_finite, G.edgeSet_finite⟩

/-- Convert a finite `GM13.Digraph α β` to `GM21.Digraph α β`. -/
def _root_.GraphMinor.GM13.Digraph.toGM21 (G : GM13.Digraph α β) (hfin : G.IsFinite) :
    Digraph α β where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet
  vertexSet_finite := hfin.finite_V
  edgeSet_finite := hfin.finite_E
  tail := G.tail
  head := G.head
  tail_mem _ he := G.tail_mem he
  head_mem _ he := G.head_mem he

/-- Extensionality for `GM13.Digraph`. -/
theorem _root_.GraphMinor.GM13.Digraph.ext {D₁ D₂ : GM13.Digraph α β}
    (hV : D₁.vertexSet = D₂.vertexSet) (hE : D₁.edgeSet = D₂.edgeSet)
    (hhead : D₁.head = D₂.head) (htail : D₁.tail = D₂.tail) : D₁ = D₂ := by
  cases D₁; cases D₂; congr

/-- Vertex deletion commutes with `toGM13`. -/
theorem deleteVertex_toGM13 (G : Digraph α β) (v : α) :
    (G.deleteVertex v).toGM13 = G.toGM13.deleteVertex v := by
  refine GM13.Digraph.ext ?_ ?_ rfl rfl
  · ext x
    simp only [deleteVertex, GM13.Digraph.deleteVertex, GM13.Digraph.deleteVertices,
      GM13.Digraph.induce, mem_inter_iff, mem_sdiff, mem_singleton_iff]
    exact ⟨fun ⟨hx, hne⟩ => ⟨hx, hx, hne⟩, fun ⟨_, hx, hne⟩ => ⟨hx, hne⟩⟩
  · ext x
    simp only [deleteVertex, GM13.Digraph.deleteVertex, GM13.Digraph.deleteVertices,
      GM13.Digraph.induce, mem_sep_iff, mem_sdiff, mem_singleton_iff]
    exact ⟨fun ⟨he, ht, hh⟩ => ⟨he, ⟨G.head_mem _ he, hh⟩, ⟨G.tail_mem _ he, ht⟩⟩,
      fun ⟨he, ⟨_, hh⟩, ⟨_, ht⟩⟩ => ⟨he, ht, hh⟩⟩

/-- For `e ∈ G.edgeSet`, the ends of `e` in `G.toHypergraph` are `{G.tail e, G.head e}`. -/
theorem ends_toHypergraph (G : Digraph α β) {e : β} (he : e ∈ G.edgeSet) :
    G.toHypergraph.ends e = {G.tail e, G.head e} := by
  ext x
  simp only [Hypergraph.ends, toHypergraph, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩

/-- If `H ≤ G.toHypergraph` and `e ∈ H.edgeSet`, then `G.tail e ∈ H.vertexSet` and
`G.head e ∈ H.vertexSet`. -/
theorem tail_mem_and_head_mem_of_le_toHypergraph {G : Digraph α β} {H : Hypergraph α β}
    (hH : H ≤ G.toHypergraph) {e : β} (he : e ∈ H.edgeSet) :
    G.tail e ∈ H.vertexSet ∧ G.head e ∈ H.vertexSet := by
  have heG : e ∈ G.edgeSet := hH.edgeSet_subset he
  have hends : H.ends e = {G.tail e, G.head e} :=
    (hH.ends_eq e he).symm.trans (G.ends_toHypergraph heG)
  have ht : G.tail e ∈ H.ends e := by rw [hends]; exact Or.inl rfl
  have hh : G.head e ∈ H.ends e := by rw [hends]; exact Or.inr rfl
  exact ⟨H.vertex_mem_of_inc ht, H.vertex_mem_of_inc hh⟩

/-- Two subhypergraphs of `G.toHypergraph` with the same vertex and edge sets are equal. -/
theorem eq_of_le_toHypergraph {G : Digraph α β} {H₁ H₂ : Hypergraph α β}
    (h₁ : H₁ ≤ G.toHypergraph) (h₂ : H₂ ≤ G.toHypergraph)
    (hV : H₁.vertexSet = H₂.vertexSet) (hE : H₁.edgeSet = H₂.edgeSet) :
    H₁ = H₂ :=
  GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq h₁ h₂ hV hE

/-- Convert a hypergraph `H : Hypergraph α β` into a subdigraph of `G.toGM13`. -/
def subdigraphOfHypergraph (G : Digraph α β) (H : Hypergraph α β) : GM13.Digraph α β :=
  G.toGM13.subdigraphOf H.vertexSet H.edgeSet

theorem isSubdigraph_subdigraphOfHypergraph (G : Digraph α β) (H : Hypergraph α β) :
    (G.subdigraphOfHypergraph H).IsSubdigraph G.toGM13 :=
  G.toGM13.subdigraphOf_isSubdigraph H.vertexSet H.edgeSet

@[simp]
theorem vertexSet_subdigraphOfHypergraph {G : Digraph α β} {H : Hypergraph α β}
    (hH : H ≤ G.toHypergraph) :
    (G.subdigraphOfHypergraph H).vertexSet = H.vertexSet :=
  inter_eq_self_of_subset_right hH.vertexSet_subset

@[simp]
theorem edgeSet_subdigraphOfHypergraph {G : Digraph α β} {H : Hypergraph α β}
    (hH : H ≤ G.toHypergraph) :
    (G.subdigraphOfHypergraph H).edgeSet = H.edgeSet := by
  ext e
  simp only [subdigraphOfHypergraph, GM13.Digraph.subdigraphOf, mem_inter_iff,
    mem_ofPred_eq]
  refine ⟨fun h => h.1.2, fun he => ?_⟩
  have hth := tail_mem_and_head_mem_of_le_toHypergraph hH he
  exact ⟨⟨hH.edgeSet_subset he, he⟩, hth.2, hth.1⟩

/-- Convert a subdigraph `D` of `G.toGM13` into a subhypergraph of `G.toHypergraph`. -/
def hypergraphOfSubdigraph (G : Digraph α β) (D : GM13.Digraph α β)
    (hD : D.IsSubdigraph G.toGM13) : Hypergraph α β where
  vertexSet := D.vertexSet
  edgeSet := D.edgeSet
  Inc e v := e ∈ D.edgeSet ∧ (v = G.tail e ∨ v = G.head e)
  vertex_mem_of_inc := by
    rintro e v ⟨he, rfl | rfl⟩
    · rw [← tail_toGM13, ← hD.tail_eq he]
      exact D.tail_mem he
    · rw [← head_toGM13, ← hD.head_eq he]
      exact D.head_mem he
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := G.vertexSet_finite.subset hD.vertexSet_subset
  edgeSet_finite := G.edgeSet_finite.subset hD.edgeSet_subset

@[simp]
theorem vertexSet_hypergraphOfSubdigraph (G : Digraph α β) (D : GM13.Digraph α β)
    (hD : D.IsSubdigraph G.toGM13) :
    (G.hypergraphOfSubdigraph D hD).vertexSet = D.vertexSet := rfl

@[simp]
theorem edgeSet_hypergraphOfSubdigraph (G : Digraph α β) (D : GM13.Digraph α β)
    (hD : D.IsSubdigraph G.toGM13) :
    (G.hypergraphOfSubdigraph D hD).edgeSet = D.edgeSet := rfl

theorem hypergraphOfSubdigraph_le {G : Digraph α β} {D : GM13.Digraph α β}
    (hD : D.IsSubdigraph G.toGM13) :
    G.hypergraphOfSubdigraph D hD ≤ G.toHypergraph := by
  refine ⟨hD.vertexSet_subset, hD.edgeSet_subset, fun e he => ?_⟩
  ext v
  simp only [Hypergraph.ends, hypergraphOfSubdigraph, toHypergraph, mem_ofPred_eq]
  exact ⟨fun h => ⟨he, h.2⟩, fun h => ⟨hD.edgeSet_subset he, h.2⟩⟩

@[simp]
theorem hypergraphOfSubdigraph_subdigraphOfHypergraph {G : Digraph α β} {H : Hypergraph α β}
    (hH : H ≤ G.toHypergraph) :
    G.hypergraphOfSubdigraph (G.subdigraphOfHypergraph H)
      (G.isSubdigraph_subdigraphOfHypergraph H) = H :=
  eq_of_le_toHypergraph
    (hypergraphOfSubdigraph_le (G.isSubdigraph_subdigraphOfHypergraph H)) hH
    (vertexSet_subdigraphOfHypergraph hH)
    (edgeSet_subdigraphOfHypergraph hH)

/-! ## Section 2: Connectedness and `HasEdgeBetween` Bridges -/

/-- For `H ≤ G.toHypergraph`, adjacency in `H.skeleton` is equivalent to the existence of a link
between distinct vertices in `(G.subdigraphOfHypergraph H).toGraph`. -/
theorem skeleton_adj_iff_exists_isLink {G : Digraph α β} {H : Hypergraph α β}
    (hH : H ≤ G.toHypergraph) {u v : α} :
    H.skeleton.Adj u v ↔ u ≠ v ∧ ∃ e, (G.subdigraphOfHypergraph H).toGraph.IsLink e u v := by
  constructor
  · rintro ⟨hne, e, hu_inc, hv_inc⟩
    have heH : e ∈ H.edgeSet := H.edge_mem_of_inc hu_inc
    have heG : e ∈ G.edgeSet := hH.edgeSet_subset heH
    have hends : H.ends e = {G.tail e, G.head e} :=
      (hH.ends_eq e heH).symm.trans (G.ends_toHypergraph heG)
    have hu_ends : u ∈ ({G.tail e, G.head e} : Set α) := hends ▸ hu_inc
    have hv_ends : v ∈ ({G.tail e, G.head e} : Set α) := hends ▸ hv_inc
    refine ⟨hne, e, (edgeSet_subdigraphOfHypergraph hH).symm ▸ heH, ?_⟩
    change (G.head e = u ∧ G.tail e = v) ∨ (G.head e = v ∧ G.tail e = u)
    rcases hu_ends with rfl | rfl <;> rcases hv_ends with rfl | rfl
    · exact (hne rfl).elim
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact (hne rfl).elim
  · rintro ⟨hne, e, he_sub, hlink⟩
    have heH : e ∈ H.edgeSet := (edgeSet_subdigraphOfHypergraph hH) ▸ he_sub
    have heG : e ∈ G.edgeSet := hH.edgeSet_subset heH
    have hends : H.ends e = {G.tail e, G.head e} :=
      (hH.ends_eq e heH).symm.trans (G.ends_toHypergraph heG)
    refine ⟨hne, e, ?_, ?_⟩
    · change u ∈ H.ends e
      rw [hends]
      rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl rfl
    · change v ∈ H.ends e
      rw [hends]
      rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- Lift a walk in `H.skeleton` to a `GraphWalk` in `(G.subdigraphOfHypergraph H).toGraph`. -/
private theorem nonempty_graphWalk_of_skeleton_walk {G : Digraph α β} {H : Hypergraph α β}
    (hH : H ≤ G.toHypergraph) {x y : α} (w : H.skeleton.Walk x y)
    (hx : x ∈ H.vertexSet) :
    Nonempty (GraphWalk (G.subdigraphOfHypergraph H).toGraph x y) := by
  induction w with
  | @nil u =>
    have hu_sub : u ∈ (G.subdigraphOfHypergraph H).vertexSet :=
      (vertexSet_subdigraphOfHypergraph hH).symm ▸ hx
    exact ⟨.nil hu_sub⟩
  | @cons u z v hadj rest ih =>
    rcases (skeleton_adj_iff_exists_isLink hH).mp hadj with ⟨_, e, hlink⟩
    have hz_sub : z ∈ (G.subdigraphOfHypergraph H).vertexSet :=
      (G.subdigraphOfHypergraph H).toGraph.left_mem_of_isLink hlink.symm
    have hzH : z ∈ H.vertexSet := (vertexSet_subdigraphOfHypergraph hH) ▸ hz_sub
    rcases ih hzH with ⟨W'⟩
    exact ⟨.cons hlink W'⟩

/-- Project a `GraphWalk` in `(G.subdigraphOfHypergraph H).toGraph` to `H.skeleton.Reachable`. -/
private theorem skeleton_reachable_of_graphWalk {G : Digraph α β} {H : Hypergraph α β}
    (hH : H ≤ G.toHypergraph) {x y : α}
    (W : GraphWalk (G.subdigraphOfHypergraph H).toGraph x y) :
    H.skeleton.Reachable x y := by
  induction W with
  | nil _ => exact SimpleGraph.Reachable.refl _
  | @cons u z v e hlink _ ih =>
    by_cases huz : u = z
    · exact huz ▸ ih
    · have hadj : H.skeleton.Adj u z :=
        (skeleton_adj_iff_exists_isLink hH).mpr ⟨huz, e, hlink⟩
      exact hadj.reachable.trans ih

/-- Equivalence between `H.skeleton.Reachable x y` and
`Nonempty (GraphWalk (G.subdigraphOfHypergraph H).toGraph x y)` for `x, y ∈ H.vertexSet`. -/
theorem skeleton_reachable_iff_nonempty_graphWalk {G : Digraph α β} {H : Hypergraph α β}
    (hH : H ≤ G.toHypergraph) {x y : α} (hx : x ∈ H.vertexSet) :
    H.skeleton.Reachable x y ↔
      Nonempty (GraphWalk (G.subdigraphOfHypergraph H).toGraph x y) :=
  ⟨fun ⟨w⟩ => nonempty_graphWalk_of_skeleton_walk hH w hx,
   fun ⟨W⟩ => skeleton_reachable_of_graphWalk hH W⟩

/-- For `H ≤ G.toHypergraph`, `(G.subdigraphOfHypergraph H).IsConnected` is equivalent to
`G.IsConnectedSubgraph H`. -/
theorem isConnected_subdigraphOfHypergraph_iff {G : Digraph α β} {H : Hypergraph α β}
    (hH : H ≤ G.toHypergraph) :
    (G.subdigraphOfHypergraph H).IsConnected ↔ G.IsConnectedSubgraph H := by
  constructor
  · rintro ⟨hne, hconn⟩
    rw [vertexSet_subdigraphOfHypergraph hH] at hne
    refine ⟨hH, hne, fun x hx y hy => ?_⟩
    rw [skeleton_reachable_iff_nonempty_graphWalk hH hx]
    exact hconn x ((vertexSet_subdigraphOfHypergraph hH).symm ▸ hx)
      y ((vertexSet_subdigraphOfHypergraph hH).symm ▸ hy)
  · rintro ⟨_, hne, hconn⟩
    refine ⟨(vertexSet_subdigraphOfHypergraph hH).symm ▸ hne, fun x hx y hy => ?_⟩
    have hxH : x ∈ H.vertexSet := (vertexSet_subdigraphOfHypergraph hH) ▸ hx
    have hyH : y ∈ H.vertexSet := (vertexSet_subdigraphOfHypergraph hH) ▸ hy
    exact (skeleton_reachable_iff_nonempty_graphWalk hH hxH).mp (hconn x hxH y hyH)

/-- For `D.IsSubdigraph G.toGM13`, `G.IsConnectedSubgraph (G.hypergraphOfSubdigraph D hD)` is
equivalent to `D.IsConnected`. -/
theorem isConnectedSubgraph_hypergraphOfSubdigraph_iff {G : Digraph α β} {D : GM13.Digraph α β}
    (hD : D.IsSubdigraph G.toGM13) :
    G.IsConnectedSubgraph (G.hypergraphOfSubdigraph D hD) ↔ D.IsConnected := by
  have hle := G.hypergraphOfSubdigraph_le hD
  rw [← isConnected_subdigraphOfHypergraph_iff hle]
  have hsub_eq : G.subdigraphOfHypergraph (G.hypergraphOfSubdigraph D hD) =
      G.toGM13.subdigraphOf D.vertexSet D.edgeSet := rfl
  have htoGraph_eq : (G.subdigraphOfHypergraph (G.hypergraphOfSubdigraph D hD)).toGraph =
      D.toGraph := by
    refine Graph.ext (vertexSet_subdigraphOfHypergraph hle) (fun e x y => ?_)
    simp only [GM13.Digraph.toGraph, edgeSet_subdigraphOfHypergraph hle]
    refine and_congr_right fun he => ?_
    change (G.head e = x ∧ G.tail e = y ∨ G.head e = y ∧ G.tail e = x) ↔
      (D.head e = x ∧ D.tail e = y ∨ D.head e = y ∧ D.tail e = x)
    rw [← head_toGM13, ← tail_toGM13, hD.head_eq he, hD.tail_eq he]
  unfold GM13.Digraph.IsConnected
  rw [vertexSet_subdigraphOfHypergraph hle, vertexSet_hypergraphOfSubdigraph, htoGraph_eq]

/-- Bridge between `GM13.Digraph.HasEdgeBetween` and XXI's edge-between condition. -/
theorem hasEdgeBetween_toGM13_iff (G : Digraph α β) (X Y : Set α) :
    G.toGM13.HasEdgeBetween X Y ↔
      ∃ e ∈ G.edgeSet, (G.tail e ∈ X ∧ G.head e ∈ Y) ∨ (G.tail e ∈ Y ∧ G.head e ∈ X) := by
  unfold GM13.Digraph.HasEdgeBetween
  simp only [and_comm, or_comm]

/-! ## Section 3: Separations, `separationOrder`, and `interSub … IsNull` Bridges -/

/-- If `G.toHypergraph.IsSeparation A B`, then `A ≤ G.toHypergraph` and `B ≤ G.toHypergraph`. -/
theorem le_of_isSeparation_toHypergraph {G : Digraph α β} {A B : Hypergraph α β}
    (hsep : G.toHypergraph.IsSeparation A B) :
    A ≤ G.toHypergraph ∧ B ≤ G.toHypergraph :=
  ⟨hsep.left_le, hsep.right_le⟩

/-- Convert a hypergraph separation `G.toHypergraph.IsSeparation A B` into a `GM13.Digraph`
separation of `G.toGM13`. -/
theorem isSeparation_subdigraphOfHypergraph {G : Digraph α β} {A B : Hypergraph α β}
    (hsep : G.toHypergraph.IsSeparation A B) :
    G.toGM13.IsSeparation (G.subdigraphOfHypergraph A) (G.subdigraphOfHypergraph B) := by
  obtain ⟨hA, hB⟩ := le_of_isSeparation_toHypergraph hsep
  refine ⟨G.isSubdigraph_subdigraphOfHypergraph A,
    G.isSubdigraph_subdigraphOfHypergraph B, ?_, ?_, ?_⟩
  · rw [vertexSet_subdigraphOfHypergraph hA, vertexSet_subdigraphOfHypergraph hB]
    exact congrArg Hypergraph.vertexSet hsep.union_eq
  · rw [edgeSet_subdigraphOfHypergraph hA, edgeSet_subdigraphOfHypergraph hB]
    exact congrArg Hypergraph.edgeSet hsep.union_eq
  · rw [edgeSet_subdigraphOfHypergraph hA, edgeSet_subdigraphOfHypergraph hB]
    exact hsep.disjoint_edgeSet

/-- Convert a `GM13.Digraph` separation `G.toGM13.IsSeparation DA DB` into a hypergraph separation
`G.toHypergraph.IsSeparation`. -/
theorem isSeparation_hypergraphOfSubdigraph {G : Digraph α β} {DA DB : GM13.Digraph α β}
    (hsep : G.toGM13.IsSeparation DA DB) :
    G.toHypergraph.IsSeparation
      (G.hypergraphOfSubdigraph DA hsep.sub_left)
      (G.hypergraphOfSubdigraph DB hsep.sub_right) := by
  have hA := G.hypergraphOfSubdigraph_le hsep.sub_left
  have hB := G.hypergraphOfSubdigraph_le hsep.sub_right
  refine ⟨hA, hB, ?_, Set.disjoint_iff_inter_eq_empty.mp hsep.edgeSet_disjoint⟩
  exact eq_of_le_toHypergraph (Hypergraph.union_le hA hB) le_rfl
    hsep.vertexSet_union hsep.edgeSet_union

/-- Equivalence between `G.toHypergraph.IsSeparation A B` and `G.toGM13.IsSeparation` on
`subdigraphOfHypergraph`. -/
theorem isSeparation_toHypergraph_iff {G : Digraph α β} {A B : Hypergraph α β} :
    G.toHypergraph.IsSeparation A B ↔
      A ≤ G.toHypergraph ∧ B ≤ G.toHypergraph ∧
        G.toGM13.IsSeparation (G.subdigraphOfHypergraph A) (G.subdigraphOfHypergraph B) := by
  refine ⟨fun hsep => ⟨hsep.left_le, hsep.right_le, isSeparation_subdigraphOfHypergraph hsep⟩, ?_⟩
  rintro ⟨hA, hB, hsep⟩
  have h := isSeparation_hypergraphOfSubdigraph hsep
  rwa [hypergraphOfSubdigraph_subdigraphOfHypergraph hA,
    hypergraphOfSubdigraph_subdigraphOfHypergraph hB] at h

/-- Separation order is preserved by `subdigraphOfHypergraph`. -/
theorem separationOrder_subdigraphOfHypergraph {G : Digraph α β} {A B : Hypergraph α β}
    (hA : A ≤ G.toHypergraph) (hB : B ≤ G.toHypergraph) :
    GM13.Digraph.separationOrder (G.subdigraphOfHypergraph A) (G.subdigraphOfHypergraph B) =
      Hypergraph.separationOrder A B := by
  change ((G.subdigraphOfHypergraph A).vertexSet ∩ (G.subdigraphOfHypergraph B).vertexSet).ncard =
    (A.vertexSet ∩ B.vertexSet).ncard
  rw [vertexSet_subdigraphOfHypergraph hA, vertexSet_subdigraphOfHypergraph hB]

/-- Separation order is preserved by `hypergraphOfSubdigraph`. -/
theorem separationOrder_hypergraphOfSubdigraph {G : Digraph α β} {DA DB : GM13.Digraph α β}
    (hA : DA.IsSubdigraph G.toGM13) (hB : DB.IsSubdigraph G.toGM13) :
    Hypergraph.separationOrder
        (G.hypergraphOfSubdigraph DA hA) (G.hypergraphOfSubdigraph DB hB) =
      GM13.Digraph.separationOrder DA DB := rfl

/-- For `DA.vertexSet ⊆ G.vertexSet`, `(G.toGM13.interSub DA DB).IsNull` is equivalent to
`Disjoint DA.vertexSet DB.vertexSet`. -/
theorem interSub_isNull_iff_disjoint {G : Digraph α β} {DA DB : GM13.Digraph α β}
    (hA : DA.vertexSet ⊆ G.vertexSet) :
    (G.toGM13.interSub DA DB).IsNull ↔ Disjoint DA.vertexSet DB.vertexSet := by
  unfold GM13.Digraph.IsNull GM13.Digraph.interSub GM13.Digraph.subdigraphOf
  rw [Set.disjoint_iff_inter_eq_empty]
  have hV : G.toGM13.vertexSet ∩ (DA.vertexSet ∩ DB.vertexSet) = DA.vertexSet ∩ DB.vertexSet :=
    inter_eq_self_of_subset_right (inter_subset_left.trans hA)
  dsimp only
  rw [hV]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rw [h]
  ext e
  simp

end Digraph

/-! ## Section 4: Digraph Models and Rooted Digraph Minors Bridges -/

/-- Convert a `GM21.RootedDigraph α β k` to `GM13.RootedDigraph α β k`. -/
abbrev RootedDigraph.toGM13 {k : ℕ} (R : RootedDigraph α β k) : GM13.RootedDigraph α β k where
  digraph := R.G.toGM13
  roots := R.roots
  roots_mem := R.roots_mem

/-- Equivalence between `GM21.HasDetailLe R δ` and `R.toGM13.detail ≤ δ`. -/
theorem hasDetailLe_iff_detail_le {k : ℕ} (R : RootedDigraph α β k) (δ : ℕ) :
    HasDetailLe R δ ↔ R.toGM13.detail ≤ δ := by
  unfold GM13.RootedDigraph.detail RootedDigraph.toGM13
  dsimp only [Digraph.vertexSet_toGM13, Digraph.edgeSet_toGM13]
  exact ⟨fun ⟨h1, h2⟩ => Nat.max_le.mpr ⟨h1, h2⟩,
    fun h => ⟨(Nat.max_le.mp h).1, (Nat.max_le.mp h).2⟩⟩

/-- Bridge between `GM21.IsDigraphModel` and `GM13.IsDigraphModel`. -/
theorem isDigraphModel_iff_gm13 (G H : Digraph α β)
    (φV : α → Hypergraph α β) (φE : β → β) :
    IsDigraphModel G H φV φE ↔
      (∀ v ∈ H.vertexSet, φV v ≤ G.toHypergraph) ∧
        GM13.IsDigraphModel H.toGM13 G.toGM13 (fun v => G.subdigraphOfHypergraph (φV v)) φE := by
  constructor
  · intro hM
    have hle : ∀ v ∈ H.vertexSet, φV v ≤ G.toHypergraph :=
      fun v hv => (hM.vert_conn v hv).le_toHypergraph
    refine ⟨hle, {
      sub_of_mem := fun v _ => G.isSubdigraph_subdigraphOfHypergraph (φV v)
      connected_of_mem := fun v hv =>
        (Digraph.isConnected_subdigraphOfHypergraph_iff (hle v hv)).mpr (hM.vert_conn v hv)
      disjoint_of_ne := fun u v hu hv hne => by
        rw [Digraph.vertexSet_subdigraphOfHypergraph (hle u hu),
          Digraph.vertexSet_subdigraphOfHypergraph (hle v hv)]
        exact hM.vert_disjoint u hu v hv hne
      edge_mem := fun e he => hM.edge_mem e he
      head_tail_mem := fun e he => by
        rw [Digraph.vertexSet_subdigraphOfHypergraph (hle (H.head e) (H.head_mem e he)),
          Digraph.vertexSet_subdigraphOfHypergraph (hle (H.tail e) (H.tail_mem e he))]
        exact ⟨hM.head_mem e he, hM.tail_mem e he⟩
      loop_not_mem := fun e he _ => by
        rw [Digraph.edgeSet_subdigraphOfHypergraph (hle (H.head e) (H.head_mem e he))]
        exact hM.edge_not_in_vert e he (H.head e) (H.head_mem e he)
      eMap_injOn := fun e₁ he₁ e₂ he₂ heq => hM.edge_inj e₁ he₁ e₂ he₂ heq
    }⟩
  · rintro ⟨hle, hM⟩
    refine {
      vert_conn := fun v hv =>
        (Digraph.isConnected_subdigraphOfHypergraph_iff (hle v hv)).mp (hM.connected_of_mem hv)
      vert_disjoint := fun u hu v hv hne => by
        rw [← Digraph.vertexSet_subdigraphOfHypergraph (hle u hu),
          ← Digraph.vertexSet_subdigraphOfHypergraph (hle v hv)]
        exact hM.disjoint_of_ne hu hv hne
      edge_mem := fun e he => hM.edge_mem he
      edge_inj := fun e₁ he₁ e₂ he₂ heq => hM.eMap_injOn he₁ he₂ heq
      edge_not_in_vert := fun e he v hv => by
        rw [← Digraph.edgeSet_subdigraphOfHypergraph (hle v hv)]
        exact hM.edge_not_mem_vMap he hv
      tail_mem := fun e he => by
        rw [← Digraph.vertexSet_subdigraphOfHypergraph (hle (H.tail e) (H.tail_mem e he))]
        exact (hM.head_tail_mem he).2
      head_mem := fun e he => by
        rw [← Digraph.vertexSet_subdigraphOfHypergraph (hle (H.head e) (H.head_mem e he))]
        exact (hM.head_tail_mem he).1
    }

/-- Bridge between `GM21.IsRootedDigraphMinor RG RH` and
`GM13.IsRootedDigraphMinor RH.toGM13 RG.toGM13`. -/
theorem isRootedDigraphMinor_iff_gm13 {k : ℕ} (RG RH : RootedDigraph α β k) :
    IsRootedDigraphMinor RG RH ↔ GM13.IsRootedDigraphMinor RH.toGM13 RG.toGM13 := by
  constructor
  · rintro ⟨φV, φE, hM, hroots⟩
    obtain ⟨hle, hM'⟩ := (isDigraphModel_iff_gm13 RG.G RH.G φV φE).mp hM
    refine ⟨fun v => RG.G.subdigraphOfHypergraph (φV v), φE, ⟨hM', fun i => ?_⟩⟩
    rw [Digraph.vertexSet_subdigraphOfHypergraph (hle (RH.roots i) (RH.roots_mem i))]
    exact hroots i
  · rintro ⟨vMap, eMap, hM⟩
    let φV (v : α) : Hypergraph α β :=
      if hv : v ∈ RH.G.vertexSet then
        RG.G.hypergraphOfSubdigraph (vMap v) (hM.sub_of_mem hv)
      else RG.G.toHypergraph
    have hle : ∀ v ∈ RH.G.vertexSet, φV v ≤ RG.G.toHypergraph := by
      intro v hv
      dsimp only [φV]
      rw [dite_eq_left hv]
      exact RG.G.hypergraphOfSubdigraph_le (hM.sub_of_mem hv)
    have hV_eq : ∀ v ∈ RH.G.vertexSet, (φV v).vertexSet = (vMap v).vertexSet := by
      intro v hv
      dsimp only [φV]
      rw [dite_eq_left hv]
      rfl
    have hE_eq : ∀ v ∈ RH.G.vertexSet, (φV v).edgeSet = (vMap v).edgeSet := by
      intro v hv
      dsimp only [φV]
      rw [dite_eq_left hv]
      rfl
    refine ⟨φV, eMap, (isDigraphModel_iff_gm13 RG.G RH.G φV eMap).mpr ⟨hle, ?_⟩, fun i => ?_⟩
    · refine {
        sub_of_mem := fun v _ => RG.G.isSubdigraph_subdigraphOfHypergraph (φV v)
        connected_of_mem := fun v hv => by
          rw [Digraph.isConnected_subdigraphOfHypergraph_iff (hle v hv)]
          dsimp only [φV]
          rw [dite_eq_left hv]
          exact (Digraph.isConnectedSubgraph_hypergraphOfSubdigraph_iff
            (hM.sub_of_mem hv)).mpr (hM.connected_of_mem hv)
        disjoint_of_ne := fun u v hu hv hne => by
          rw [Digraph.vertexSet_subdigraphOfHypergraph (hle u hu), hV_eq u hu,
            Digraph.vertexSet_subdigraphOfHypergraph (hle v hv), hV_eq v hv]
          exact hM.disjoint_of_ne hu hv hne
        edge_mem := fun e he => hM.edge_mem he
        head_tail_mem := fun e he => by
          have hh := RH.G.head_mem e he
          have ht := RH.G.tail_mem e he
          rw [Digraph.vertexSet_subdigraphOfHypergraph (hle (RH.G.head e) hh),
            hV_eq (RH.G.head e) hh,
            Digraph.vertexSet_subdigraphOfHypergraph (hle (RH.G.tail e) ht),
            hV_eq (RH.G.tail e) ht]
          exact hM.head_tail_mem he
        loop_not_mem := fun e he hloop => by
          have hh := RH.G.head_mem e he
          change eMap e ∉ (RG.G.subdigraphOfHypergraph (φV (RH.G.head e))).edgeSet
          rw [Digraph.edgeSet_subdigraphOfHypergraph (hle (RH.G.head e) hh),
            hE_eq (RH.G.head e) hh]
          exact hM.loop_not_mem he hloop
        eMap_injOn := hM.eMap_injOn
      }
    · rw [hV_eq (RH.roots i) (RH.roots_mem i)]
      exact hM.root_mem i

/-! ## Section 5: Finite Reindexing of `GM13.RootedDigraph` to `ℕ` and `δ`-Folio Bridges -/

/-- Precompose a `GM13.IsRootedDigraphModel` on the left with a rooted digraph isomorphism. -/
theorem isRootedDigraphModel_of_iso_left {α₁ β₁ α₂ β₂ : Type*} {k : ℕ}
    {H₁ : GM13.RootedDigraph α₁ β₁ k} {H₂ : GM13.RootedDigraph α₂ β₂ k}
    {G : GM13.RootedDigraph α β k}
    {vMap : α₂ → GM13.Digraph α β} {eMap : β₂ → β}
    (iso : GM13.RootedDigraph.Iso H₁ H₂)
    (hM : GM13.IsRootedDigraphModel H₂ G vMap eMap) :
    GM13.IsRootedDigraphModel H₁ G (vMap ∘ iso.vMap) (eMap ∘ iso.eMap) where
  sub_of_mem _ hu := hM.sub_of_mem (iso.bijOn_v.mapsTo hu)
  connected_of_mem _ hu := hM.connected_of_mem (iso.bijOn_v.mapsTo hu)
  disjoint_of_ne _ _ hu hv hne :=
    hM.disjoint_of_ne (iso.bijOn_v.mapsTo hu) (iso.bijOn_v.mapsTo hv)
      (fun h => hne (iso.bijOn_v.injOn hu hv h))
  edge_mem _ he := hM.edge_mem (iso.bijOn_e.mapsTo he)
  head_tail_mem e he := by
    dsimp only [Function.comp_def]
    rw [← iso.head_eq he, ← iso.tail_eq he]
    exact hM.head_tail_mem (iso.bijOn_e.mapsTo he)
  loop_not_mem e he hloop := by
    dsimp only [Function.comp_def]
    rw [← iso.head_eq he]
    refine hM.loop_not_mem (iso.bijOn_e.mapsTo he) ?_
    rw [iso.head_eq he, iso.tail_eq he, hloop]
  eMap_injOn := hM.eMap_injOn.comp iso.bijOn_e.injOn iso.bijOn_e.mapsTo
  root_mem i := by
    dsimp only [Function.comp_def]
    rw [iso.map_roots i]
    exact hM.root_mem i

/-- Transport `GM13.IsRootedDigraphMinor` along a rooted digraph isomorphism on the left. -/
theorem isRootedDigraphMinor_of_iso_left {α₁ β₁ α₂ β₂ : Type*} {k : ℕ}
    {H₁ : GM13.RootedDigraph α₁ β₁ k} {H₂ : GM13.RootedDigraph α₂ β₂ k}
    {G : GM13.RootedDigraph α β k}
    (iso : GM13.RootedDigraph.Iso H₁ H₂)
    (h : GM13.IsRootedDigraphMinor H₂ G) :
    GM13.IsRootedDigraphMinor H₁ G := by
  rcases h with ⟨vMap, eMap, hM⟩
  exact ⟨vMap ∘ iso.vMap, eMap ∘ iso.eMap, isRootedDigraphModel_of_iso_left iso hM⟩

/-- Isomorphic rooted digraphs have the same detail. -/
theorem detail_eq_of_iso {α₁ β₁ α₂ β₂ : Type*} {k : ℕ}
    {R₁ : GM13.RootedDigraph α₁ β₁ k} {R₂ : GM13.RootedDigraph α₂ β₂ k}
    (iso : GM13.RootedDigraph.Iso R₁ R₂) :
    R₂.detail = R₁.detail := by
  unfold GM13.RootedDigraph.detail
  have hE : R₂.digraph.edgeSet.ncard = R₁.digraph.edgeSet.ncard := by
    rw [← iso.bijOn_e.image_eq, iso.bijOn_e.injOn.ncard_image]
  have hbij_sdiff :
      Set.BijOn iso.vMap
        (R₁.digraph.vertexSet \ Set.range R₁.roots)
        (R₂.digraph.vertexSet \ Set.range R₂.roots) := by
    refine ⟨fun u ⟨hu, hnot⟩ => ⟨iso.bijOn_v.mapsTo hu, ?_⟩,
      iso.bijOn_v.injOn.mono sdiff_subset,
      fun v ⟨hv, hnot⟩ => ?_⟩
    · rintro ⟨i, hi⟩
      rw [← iso.map_roots i] at hi
      exact hnot ⟨i, iso.bijOn_v.injOn (R₁.roots_mem i) hu hi⟩
    · rcases iso.bijOn_v.surjOn hv with ⟨u, hu, rfl⟩
      refine ⟨u, ⟨hu, fun ⟨i, hi⟩ => hnot ⟨i, ?_⟩⟩, rfl⟩
      rw [← iso.map_roots i, hi]
  have hV : (R₂.digraph.vertexSet \ Set.range R₂.roots).ncard =
      (R₁.digraph.vertexSet \ Set.range R₁.roots).ncard := by
    rw [← hbij_sdiff.image_eq, hbij_sdiff.injOn.ncard_image]
  rw [hE, hV]

/-- Reindex any finite `GM13.RootedDigraph α β k` to an isomorphic `GM13.RootedDigraph ℕ ℕ k`. -/
noncomputable def _root_.GraphMinor.GM13.RootedDigraph.toNatRootedDigraph {k : ℕ}
    (R : GM13.RootedDigraph α β k) (hfin : R.digraph.IsFinite) :
    GM13.RootedDigraph ℕ ℕ k :=
  let eV : R.digraph.vertexSet ≃ Fin R.digraph.vertexSet.ncard :=
    @Finite.equivFin R.digraph.vertexSet hfin.finite_V.to_subtype
  let eE : R.digraph.edgeSet ≃ Fin R.digraph.edgeSet.ncard :=
    @Finite.equivFin R.digraph.edgeSet hfin.finite_E.to_subtype
  { digraph :=
      { vertexSet := {i : ℕ | i < R.digraph.vertexSet.ncard}
        edgeSet := {j : ℕ | j < R.digraph.edgeSet.ncard}
        head := fun j =>
          if hj : j < R.digraph.edgeSet.ncard then
            (eV ⟨R.digraph.head (eE.symm ⟨j, hj⟩).1,
              R.digraph.head_mem (eE.symm ⟨j, hj⟩).2⟩).1
          else 0
        tail := fun j =>
          if hj : j < R.digraph.edgeSet.ncard then
            (eV ⟨R.digraph.tail (eE.symm ⟨j, hj⟩).1,
              R.digraph.tail_mem (eE.symm ⟨j, hj⟩).2⟩).1
          else 0
        head_mem := fun j hj => by
          change j < R.digraph.edgeSet.ncard at hj
          dsimp only [mem_ofPred_eq]
          rw [dite_eq_left hj]
          exact (eV _).2
        tail_mem := fun j hj => by
          change j < R.digraph.edgeSet.ncard at hj
          dsimp only [mem_ofPred_eq]
          rw [dite_eq_left hj]
          exact (eV _).2 }
    roots := fun i => (eV ⟨R.roots i, R.roots_mem i⟩).1
    roots_mem := fun i => (eV ⟨R.roots i, R.roots_mem i⟩).2 }

theorem _root_.GraphMinor.GM13.RootedDigraph.isFinite_toNatRootedDigraph {k : ℕ}
    (R : GM13.RootedDigraph α β k) (hfin : R.digraph.IsFinite) :
    (R.toNatRootedDigraph hfin).digraph.IsFinite := by
  refine ⟨?_, ?_⟩
  · change {i : ℕ | i < R.digraph.vertexSet.ncard}.Finite
    exact ( Set.finite_lt_nat _ )
  · change {j : ℕ | j < R.digraph.edgeSet.ncard}.Finite
    exact ( Set.finite_lt_nat _ )

/-- Rooted digraph isomorphism from `R` to `R.toNatRootedDigraph hfin`. -/
noncomputable def _root_.GraphMinor.GM13.RootedDigraph.isoToNatRootedDigraph {k : ℕ}
    (R : GM13.RootedDigraph α β k) (hfin : R.digraph.IsFinite) :
    GM13.RootedDigraph.Iso R (R.toNatRootedDigraph hfin) :=
  let eV : R.digraph.vertexSet ≃ Fin R.digraph.vertexSet.ncard :=
    @Finite.equivFin R.digraph.vertexSet hfin.finite_V.to_subtype
  let eE : R.digraph.edgeSet ≃ Fin R.digraph.edgeSet.ncard :=
    @Finite.equivFin R.digraph.edgeSet hfin.finite_E.to_subtype
  { vMap := fun u => if hu : u ∈ R.digraph.vertexSet then (eV ⟨u, hu⟩).1 else 0
    eMap := fun e => if he : e ∈ R.digraph.edgeSet then (eE ⟨e, he⟩).1 else 0
    bijOn_v :=
      ⟨fun u hu => by
        dsimp only [GM13.RootedDigraph.toNatRootedDigraph, mem_ofPred_eq]
        rw [dite_eq_left hu]
        exact (eV ⟨u, hu⟩).2,
       fun u₁ hu₁ u₂ hu₂ heq => by
        dsimp only at heq
        rw [dite_eq_left hu₁, dite_eq_left hu₂] at heq
        exact congrArg Subtype.val (eV.injective (Fin.ext heq)),
       fun i hi => by
        change i < R.digraph.vertexSet.ncard at hi
        let u := eV.symm ⟨i, hi⟩
        refine ⟨u.1, u.2, ?_⟩
        dsimp only
        rw [dite_eq_left u.2]
        exact congrArg Fin.val (eV.apply_symm_apply ⟨i, hi⟩)⟩
    bijOn_e :=
      ⟨fun e he => by
        dsimp only [GM13.RootedDigraph.toNatRootedDigraph, mem_ofPred_eq]
        rw [dite_eq_left he]
        exact (eE ⟨e, he⟩).2,
       fun e₁ he₁ e₂ he₂ heq => by
        dsimp only at heq
        rw [dite_eq_left he₁, dite_eq_left he₂] at heq
        exact congrArg Subtype.val (eE.injective (Fin.ext heq)),
       fun j hj => by
        change j < R.digraph.edgeSet.ncard at hj
        let e := eE.symm ⟨j, hj⟩
        refine ⟨e.1, e.2, ?_⟩
        dsimp only
        rw [dite_eq_left e.2]
        exact congrArg Fin.val (eE.apply_symm_apply ⟨j, hj⟩)⟩
    head_eq := fun e he => by
      have hj : (eE ⟨e, he⟩).1 < R.digraph.edgeSet.ncard := (eE ⟨e, he⟩).2
      have hh : R.digraph.head e ∈ R.digraph.vertexSet := R.digraph.head_mem he
      dsimp only [GM13.RootedDigraph.toNatRootedDigraph]
      simp only [he, ↓reduceDIte, hj, hh]
      refine congrArg (fun v : R.digraph.vertexSet => (eV v).1) (Subtype.ext ?_)
      exact congrArg (fun z : R.digraph.edgeSet => R.digraph.head z.1)
        (eE.symm_apply_apply ⟨e, he⟩)
    tail_eq := fun e he => by
      have hj : (eE ⟨e, he⟩).1 < R.digraph.edgeSet.ncard := (eE ⟨e, he⟩).2
      have ht : R.digraph.tail e ∈ R.digraph.vertexSet := R.digraph.tail_mem he
      dsimp only [GM13.RootedDigraph.toNatRootedDigraph]
      simp only [he, ↓reduceDIte, hj, ht]
      refine congrArg (fun v : R.digraph.vertexSet => (eV v).1) (Subtype.ext ?_)
      exact congrArg (fun z : R.digraph.edgeSet => R.digraph.tail z.1)
        (eE.symm_apply_apply ⟨e, he⟩)
    map_roots := fun i => by
      dsimp only [GM13.RootedDigraph.toNatRootedDigraph]
      rw [dite_eq_left (R.roots_mem i)] }

/-- Rooted digraph isomorphism from `R.toNatRootedDigraph hfin` to `R`. -/
noncomputable def _root_.GraphMinor.GM13.RootedDigraph.isoFromNatRootedDigraph {k : ℕ}
    [Nonempty α] [Nonempty β]
    (R : GM13.RootedDigraph α β k) (hfin : R.digraph.IsFinite) :
    GM13.RootedDigraph.Iso (R.toNatRootedDigraph hfin) R :=
  let eV : R.digraph.vertexSet ≃ Fin R.digraph.vertexSet.ncard :=
    @Finite.equivFin R.digraph.vertexSet hfin.finite_V.to_subtype
  let eE : R.digraph.edgeSet ≃ Fin R.digraph.edgeSet.ncard :=
    @Finite.equivFin R.digraph.edgeSet hfin.finite_E.to_subtype
  let a₀ : α := Classical.arbitrary α
  let b₀ : β := Classical.arbitrary β
  { vMap := fun i => if hi : i < R.digraph.vertexSet.ncard then (eV.symm ⟨i, hi⟩).1 else a₀
    eMap := fun j => if hj : j < R.digraph.edgeSet.ncard then (eE.symm ⟨j, hj⟩).1 else b₀
    bijOn_v :=
      ⟨fun i hi => by
        change i < R.digraph.vertexSet.ncard at hi
        dsimp only
        rw [dite_eq_left hi]
        exact (eV.symm ⟨i, hi⟩).2,
       fun i₁ hi₁ i₂ hi₂ heq => by
        change i₁ < R.digraph.vertexSet.ncard at hi₁
        change i₂ < R.digraph.vertexSet.ncard at hi₂
        dsimp only at heq
        rw [dite_eq_left hi₁, dite_eq_left hi₂] at heq
        exact congrArg Fin.val (eV.symm.injective (Subtype.ext heq)),
       fun u hu => by
        refine ⟨(eV ⟨u, hu⟩).1, (eV ⟨u, hu⟩).2, ?_⟩
        dsimp only
        rw [dite_eq_left (eV ⟨u, hu⟩).2]
        exact congrArg Subtype.val (eV.symm_apply_apply ⟨u, hu⟩)⟩
    bijOn_e :=
      ⟨fun j hj => by
        change j < R.digraph.edgeSet.ncard at hj
        dsimp only
        rw [dite_eq_left hj]
        exact (eE.symm ⟨j, hj⟩).2,
       fun j₁ hj₁ j₂ hj₂ heq => by
        change j₁ < R.digraph.edgeSet.ncard at hj₁
        change j₂ < R.digraph.edgeSet.ncard at hj₂
        dsimp only at heq
        rw [dite_eq_left hj₁, dite_eq_left hj₂] at heq
        exact congrArg Fin.val (eE.symm.injective (Subtype.ext heq)),
       fun e he => by
        refine ⟨(eE ⟨e, he⟩).1, (eE ⟨e, he⟩).2, ?_⟩
        dsimp only
        rw [dite_eq_left (eE ⟨e, he⟩).2]
        exact congrArg Subtype.val (eE.symm_apply_apply ⟨e, he⟩)⟩
    head_eq := fun j hj => by
      change j < R.digraph.edgeSet.ncard at hj
      dsimp only [GM13.RootedDigraph.toNatRootedDigraph]
      simp only [hj, ↓reduceDIte, Fin.is_lt]
      have hsymm := eV.symm_apply_apply
        ⟨R.digraph.head (eE.symm ⟨j, hj⟩).1, R.digraph.head_mem (eE.symm ⟨j, hj⟩).2⟩
      exact (congrArg Subtype.val hsymm).symm
    tail_eq := fun j hj => by
      change j < R.digraph.edgeSet.ncard at hj
      dsimp only [GM13.RootedDigraph.toNatRootedDigraph]
      simp only [hj, ↓reduceDIte, Fin.is_lt]
      have hsymm := eV.symm_apply_apply
        ⟨R.digraph.tail (eE.symm ⟨j, hj⟩).1, R.digraph.tail_mem (eE.symm ⟨j, hj⟩).2⟩
      exact (congrArg Subtype.val hsymm).symm
    map_roots := fun i => by
      dsimp only [GM13.RootedDigraph.toNatRootedDigraph]
      simp only [Fin.is_lt, ↓reduceDIte]
      exact congrArg Subtype.val (eV.symm_apply_apply ⟨R.roots i, R.roots_mem i⟩) }

@[simp]
theorem _root_.GraphMinor.GM13.RootedDigraph.detail_toNatRootedDigraph {k : ℕ}
    (R : GM13.RootedDigraph α β k) (hfin : R.digraph.IsFinite) :
    (R.toNatRootedDigraph hfin).detail = R.detail :=
  detail_eq_of_iso (R.isoToNatRootedDigraph hfin)

/-- For a finite rooted digraph `R` of detail `≤ δ`, `R.toNatRootedDigraph hfin` belongs to
`G.deltaFolio δ` if and only if `GM13.IsRootedDigraphMinor R G`. -/
theorem _root_.GraphMinor.GM13.RootedDigraph.toNatRootedDigraph_mem_deltaFolio_iff
    {α₁ β₁ : Type*} {k δ : ℕ} [Nonempty α] [Nonempty β]
    (G : GM13.RootedDigraph α₁ β₁ k)
    (R : GM13.RootedDigraph α β k) (hfin : R.digraph.IsFinite) (hdet : R.detail ≤ δ) :
    R.toNatRootedDigraph hfin ∈ G.deltaFolio δ ↔ GM13.IsRootedDigraphMinor R G := by
  simp only [GM13.RootedDigraph.deltaFolio, mem_ofPred_eq, GM13.RootedDigraph.InDeltaFolio,
    GM13.RootedDigraph.InFolio, R.detail_toNatRootedDigraph hfin]
  refine ⟨fun ⟨⟨_, hmin⟩, _⟩ =>
      isRootedDigraphMinor_of_iso_left (R.isoToNatRootedDigraph hfin) hmin,
    fun hmin =>
      ⟨⟨R.isFinite_toNatRootedDigraph hfin,
        isRootedDigraphMinor_of_iso_left (R.isoFromNatRootedDigraph hfin) hmin⟩, hdet⟩⟩

/-! ## Section 6: Injectivity of Finite Enumerations and Irrelevance Bridge -/

/-- Any enumeration `roots : Fin k → α` of a set `Z` with `k = Z.ncard` and `Set.range roots = Z`
is injective. -/
theorem injective_of_range_eq_of_ncard_eq {Z : Set α} {k : ℕ} {roots : Fin k → α}
    (hk : k = Z.ncard) (hrange : Set.range roots = Z) :
    Function.Injective roots := by
  let f : Fin k → ↥Z := fun i => ⟨roots i, hrange ▸ Set.mem_range_self i⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    rw [← hrange] at hz
    rcases hz with ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  have hcard : Nat.card (Fin k) = Nat.card ↥Z := by
    rw [Nat.card_fin, hk, Nat.card_coe_set_eq]
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_surjective_and_card f).mpr ⟨hsurj, hcard⟩
  intro i j hij
  exact hbij.1 (Subtype.ext hij)

theorem rootedDigraph_mk_eq_of_digraph_eq {k : ℕ} {D₁ D₂ : GM13.Digraph α β}
    (hD : D₁ = D₂) (roots : Fin k → α)
    (hr₁ : ∀ i, roots i ∈ D₁.vertexSet) (hr₂ : ∀ i, roots i ∈ D₂.vertexSet) :
    GM13.RootedDigraph.mk D₁ roots hr₁ = GM13.RootedDigraph.mk D₂ roots hr₂ := by
  subst hD
  rfl

/-- Bridge from `GM13.IsIrrelevantVertex` to `GM21.IsIrrelevantToDigraphFolio`. -/
theorem isIrrelevantToDigraphFolio_of_gm13 [Nonempty β]
    {G : Digraph α β} {Z : Set α} {δ : ℕ} {v : α}
    (hirr : GM13.IsIrrelevantVertex G.toGM13 δ Z v) :
    IsIrrelevantToDigraphFolio G Z δ v := by
  have : Nonempty α := ⟨v⟩
  refine ⟨hirr.2.2.2.1, hirr.1, hirr.2.1, fun k roots hG_roots hGv_roots hk hrange RH hdet => ?_⟩
  have hinj : Function.Injective roots := injective_of_range_eq_of_ncard_eq hk hrange
  have hGv_roots' : ∀ i : Fin k, roots i ∈ (G.toGM13.deleteVertex v).vertexSet := by
    intro i
    rw [← G.deleteVertex_toGM13 v]
    exact hGv_roots i
  have hsame : GM13.HasSameDeltaFolio
      (GM13.RootedDigraph.mk (G.toGM13.deleteVertex v) roots hGv_roots')
      (GM13.RootedDigraph.mk G.toGM13 roots hG_roots) δ :=
    hirr.2.2.2.2 k roots hGv_roots' hG_roots hinj hrange.subset
  have hdet' : RH.toGM13.detail ≤ δ := (hasDetailLe_iff_detail_le RH δ).mp hdet
  have hfin_RH : RH.toGM13.digraph.IsFinite := RH.G.isFinite_toGM13
  rw [isRootedDigraphMinor_iff_gm13 ⟨G, roots, hG_roots⟩ RH,
    isRootedDigraphMinor_iff_gm13 ⟨G.deleteVertex v, roots, hGv_roots⟩ RH]
  have hRGv : (⟨G.deleteVertex v, roots, hGv_roots⟩ : RootedDigraph α β k).toGM13 =
      GM13.RootedDigraph.mk (G.toGM13.deleteVertex v) roots hGv_roots' :=
    rootedDigraph_mk_eq_of_digraph_eq (G.deleteVertex_toGM13 v) roots hGv_roots hGv_roots'
  rw [hRGv,
    ← GM13.RootedDigraph.toNatRootedDigraph_mem_deltaFolio_iff
      (GM13.RootedDigraph.mk G.toGM13 roots hG_roots) RH.toGM13 hfin_RH hdet',
    ← GM13.RootedDigraph.toNatRootedDigraph_mem_deltaFolio_iff
      (GM13.RootedDigraph.mk (G.toGM13.deleteVertex v) roots hGv_roots') RH.toGM13 hfin_RH hdet',
    hsame]

/-! ## Section 7: Proof of `GM21.gm13Theorem61` -/

/-- **Graph Minors XIII, (6.1)** in the types of Graph Minors XXI (`GM21.GM13Theorem61Statement`),
proved from `GM13.theorem_6_1_proof`. -/
theorem gm13Theorem61 : GM13Theorem61Statement.{u, v} := by
  intro α β _ G Z p δ _ hZ hZ_card k SubG hSubG_conn hSubG_disj hSubG_edges
    A B hsep hcond1 hcond2 hcond3 hcond4 v hv
  obtain ⟨hA_le, hB_le, hsep_gm13⟩ := Digraph.isSeparation_toHypergraph_iff.mp hsep
  let sub (i : Fin k) : GM13.Digraph α β :=
    G.subdigraphOfHypergraph (SubG i)
  have hsub_le : ∀ i, SubG i ≤ G.toHypergraph := fun i => (hSubG_conn i).le_toHypergraph
  have hsub_sub : ∀ i, (sub i).IsSubdigraph G.toGM13 := fun i =>
    G.isSubdigraph_subdigraphOfHypergraph (SubG i)
  have hsub_conn : ∀ i, (sub i).IsConnected := fun i =>
    (Digraph.isConnected_subdigraphOfHypergraph_iff (hsub_le i)).mpr (hSubG_conn i)
  have hsub_disj : Pairwise (fun i j => Disjoint (sub i).vertexSet (sub j).vertexSet) := by
    intro i j hne
    rw [Digraph.vertexSet_subdigraphOfHypergraph (hsub_le i),
      Digraph.vertexSet_subdigraphOfHypergraph (hsub_le j)]
    exact hSubG_disj i j hne
  have hsub_edges : ∀ i j, i < j →
      G.toGM13.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet := by
    intro i j hij
    rw [Digraph.vertexSet_subdigraphOfHypergraph (hsub_le i),
      Digraph.vertexSet_subdigraphOfHypergraph (hsub_le j),
      G.hasEdgeBetween_toGM13_iff]
    exact hSubG_edges i j hij
  have hcond1' : ∃ i, (G.toGM13.interSub (G.subdigraphOfHypergraph A) (sub i)).IsNull := by
    rcases hcond1 with ⟨i, hi⟩
    refine ⟨i, (Digraph.interSub_isNull_iff_disjoint
      (G.isSubdigraph_subdigraphOfHypergraph A).vertexSet_subset).mpr ?_⟩
    rwa [Digraph.vertexSet_subdigraphOfHypergraph hA_le,
      Digraph.vertexSet_subdigraphOfHypergraph (hsub_le i)]
  have hcond2' : Z ⊆ (G.subdigraphOfHypergraph A).vertexSet := by
    rwa [Digraph.vertexSet_subdigraphOfHypergraph hA_le]
  have hcond3' : ∀ A' B' : GM13.Digraph α β,
      G.toGM13.IsSeparation A' B' →
      (∃ i, (G.toGM13.interSub A' (sub i)).IsNull) →
      Z ⊆ A'.vertexSet →
      GM13.Digraph.separationOrder (G.subdigraphOfHypergraph A) (G.subdigraphOfHypergraph B) ≤
        GM13.Digraph.separationOrder A' B' := by
    intro A' B' hsep' ⟨i, hi'⟩ hZA'
    rw [Digraph.separationOrder_subdigraphOfHypergraph hA_le hB_le,
      ← Digraph.separationOrder_hypergraphOfSubdigraph hsep'.sub_left hsep'.sub_right]
    apply hcond3
      (G.hypergraphOfSubdigraph A' hsep'.sub_left)
      (G.hypergraphOfSubdigraph B' hsep'.sub_right)
      (Digraph.isSeparation_hypergraphOfSubdigraph hsep')
    · refine ⟨i, ?_⟩
      have hdisj :=
        (Digraph.interSub_isNull_iff_disjoint hsep'.sub_left.vertexSet_subset).mp hi'
      rwa [Digraph.vertexSet_subdigraphOfHypergraph (hsub_le i)] at hdisj
    · exact hZA'
  have hcond4' : ∀ A' B' : GM13.Digraph α β,
      G.toGM13.IsSeparation A' B' →
      (∃ i, (G.toGM13.interSub A' (sub i)).IsNull) →
      Z ⊆ A'.vertexSet →
      GM13.Digraph.separationOrder A' B' ≤
        GM13.Digraph.separationOrder (G.subdigraphOfHypergraph A) (G.subdigraphOfHypergraph B) →
      (G.subdigraphOfHypergraph A).IsSubdigraph A' →
      A'.vertexSet = (G.subdigraphOfHypergraph A).vertexSet ∧
        A'.edgeSet = (G.subdigraphOfHypergraph A).edgeSet := by
    intro A' B' hsep' ⟨i, hi'⟩ hZA' hord' hsub_AA'
    have hVA' : (G.subdigraphOfHypergraph A).vertexSet ⊆ A'.vertexSet := hsub_AA'.vertexSet_subset
    have hEA' : (G.subdigraphOfHypergraph A).edgeSet ⊆ A'.edgeSet := hsub_AA'.edgeSet_subset
    rw [Digraph.vertexSet_subdigraphOfHypergraph hA_le] at hVA' ⊢
    rw [Digraph.edgeSet_subdigraphOfHypergraph hA_le] at hEA' ⊢
    rw [Digraph.separationOrder_subdigraphOfHypergraph hA_le hB_le,
      ← Digraph.separationOrder_hypergraphOfSubdigraph hsep'.sub_left hsep'.sub_right] at hord'
    have hdisj : Disjoint A'.vertexSet (SubG i).vertexSet := by
      have h := (Digraph.interSub_isNull_iff_disjoint hsep'.sub_left.vertexSet_subset).mp hi'
      rwa [Digraph.vertexSet_subdigraphOfHypergraph (hsub_le i)] at h
    have hle_AA' : A ≤ G.hypergraphOfSubdigraph A' hsep'.sub_left := by
      refine ⟨hVA', hEA', fun e he => ?_⟩
      have heA' : e ∈ (G.hypergraphOfSubdigraph A' hsep'.sub_left).edgeSet := hEA' he
      exact ((G.hypergraphOfSubdigraph_le hsep'.sub_left).ends_eq e heA').symm.trans
        (hA_le.ends_eq e he)
    have h_eq : G.hypergraphOfSubdigraph A' hsep'.sub_left = A :=
      hcond4
        (G.hypergraphOfSubdigraph A' hsep'.sub_left)
        (G.hypergraphOfSubdigraph B' hsep'.sub_right)
        (Digraph.isSeparation_hypergraphOfSubdigraph hsep')
        ⟨i, hdisj⟩ hZA' hord' hle_AA'
    exact ⟨congrArg Hypergraph.vertexSet h_eq, congrArg Hypergraph.edgeSet h_eq⟩
  have hv' : v ∈ (G.subdigraphOfHypergraph B).vertexSet \
      (G.subdigraphOfHypergraph A).vertexSet := by
    rwa [Digraph.vertexSet_subdigraphOfHypergraph hB_le,
      Digraph.vertexSet_subdigraphOfHypergraph hA_le]
  have hirr_gm13 : GM13.IsIrrelevantVertex G.toGM13 δ Z v :=
    GM13.theorem_6_1_proof G.isFinite_toGM13 hZ hZ_card rfl hsub_sub hsub_conn hsub_disj hsub_edges
      hsep_gm13 hcond1' hcond2' hcond3' hcond4' hv'
  exact isIrrelevantToDigraphFolio_of_gm13 hirr_gm13

end GM21
end GraphMinor
