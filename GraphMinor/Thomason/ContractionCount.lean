module

public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Data.Set.Card

/-!
# Counting edges after one simple-graph contraction

Contracting an edge loses that edge and one edge for every common neighbour
of its ends. This is the counting step in Thomason's reduction to a dense
neighbourhood graph, described in *Extremal functions for graph minors*,
Lemma 2.1, page 363 (2006).
-/

@[expose] public section

namespace GraphMinor.Thomason

open SimpleGraph Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Neighbours of the removed vertex that need a new edge at the retained vertex. -/
def newContractionNeighbors (u v : V) : Finset V :=
  G.neighborFinset v \ insert u (G.neighborFinset u)

/-- Retain all edges not incident with `v`, then add the missing edges at `u`.
The vertex `v` is isolated in this graph. -/
def contractionEdges (u v : V) : Finset (Sym2 V) :=
  (G.deleteIncidenceSet v).edgeFinset ∪
    (newContractionNeighbors G u v).image (fun w => s(u, w))

/-- The simple graph after merging `v` into `u`, with `v` retained as an isolated vertex. -/
def contractGraph (u v : V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (contractionEdges G u v : Set (Sym2 V))

instance contractGraphDecidableAdj (u v : V) : DecidableRel (contractGraph G u v).Adj :=
  fun x y => inferInstanceAs
    (Decidable (s(x, y) ∈ (contractionEdges G u v : Set (Sym2 V)) ∧ x ≠ y))

private theorem newContractionNeighbors_ne {u v w : V}
    (hw : w ∈ newContractionNeighbors G u v) : w ≠ u := by
  exact fun h => (mem_sdiff.mp hw).2 (mem_insert.mpr (Or.inl h))

private theorem contractionEdges_not_isDiag {u v : V} {e : Sym2 V}
    (he : e ∈ contractionEdges G u v) : ¬ e.IsDiag := by
  rcases mem_union.mp he with he | he
  · exact (G.deleteIncidenceSet v).not_isDiag_of_mem_edgeFinset he
  · obtain ⟨w, hw, rfl⟩ := mem_image.mp he
    exact fun h => newContractionNeighbors_ne G hw (Sym2.mk_isDiag_iff.mp h).symm

/-- The stated edge set of the contraction contains no diagonal pairs. -/
theorem contractGraph_edgeFinset (u v : V) :
    (contractGraph G u v).edgeFinset = contractionEdges G u v := by
  ext e
  rw [SimpleGraph.mem_edgeFinset]
  change e ∈ (SimpleGraph.fromEdgeSet (contractionEdges G u v : Set (Sym2 V))).edgeSet ↔ _
  simp only [edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe, Sym2.mem_diagSet]
  exact ⟨And.left, fun he => ⟨he, contractionEdges_not_isDiag G he⟩⟩

private theorem contractionEdges_disjoint (u v : V) :
    Disjoint (G.deleteIncidenceSet v).edgeFinset
      ((newContractionNeighbors G u v).image (fun w => s(u, w))) := by
  apply Finset.disjoint_left.mpr
  intro e he hnew
  obtain ⟨w, hw, rfl⟩ := mem_image.mp hnew
  have hnot : w ∉ G.neighborFinset u := fun h =>
    (mem_sdiff.mp hw).2 (mem_insert_of_mem h)
  have hadj : G.Adj u w := G.deleteIncidenceSet_le v (mem_edgeFinset.mp he)
  exact hnot ((G.mem_neighborFinset u w).mpr hadj)

private theorem card_newContractionNeighbors_add (u v : V) (huv : G.Adj u v) :
    (newContractionNeighbors G u v).card +
      (G.neighborFinset v ∩ G.neighborFinset u).card + 1 = G.degree v := by
  have hu : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).mpr huv.symm
  have hn : u ∉ G.neighborFinset v ∩ G.neighborFinset u := by simp
  have hinter : G.neighborFinset v ∩ insert u (G.neighborFinset u) =
      insert u (G.neighborFinset v ∩ G.neighborFinset u) := by
    ext w
    by_cases hwu : w = u
    · subst w
      simp [hu]
    · simp [hwu]
  have hcount := card_sdiff_add_card_inter (G.neighborFinset v)
    (insert u (G.neighborFinset u))
  rw [hinter, card_insert_of_notMem hn] at hcount
  simpa only [newContractionNeighbors, G.card_neighborFinset_eq_degree, Nat.add_assoc] using hcount

/-- Merging adjacent vertices loses exactly one edge plus one for each common
neighbour, the edge count used in Thomason's Lemma 2.1, page 363. -/
theorem contractGraph_card_edges {u v : V} (huv : G.Adj u v) :
    (contractGraph G u v).edgeFinset.card +
      (G.neighborFinset v ∩ G.neighborFinset u).card + 1 = G.edgeFinset.card := by
  rw [contractGraph_edgeFinset, contractionEdges,
    card_union_of_disjoint (contractionEdges_disjoint G u v)]
  have hinj : Function.Injective (fun w : V => s(u, w)) := by
    intro a b h
    rcases Sym2.eq_iff.mp h with h | h
    · exact h.2
    · exact h.2.trans h.1
  rw [card_image_of_injective _ hinj, G.card_edgeFinset_deleteIncidenceSet]
  have hd := G.degree_le_card_edgeFinset (v := v)
  have hc := card_newContractionNeighbors_add G u v huv
  omega

/-- The contracted graph with the removed vertex omitted from its vertex type. -/
def edgeContraction (u v : V) : SimpleGraph ({v}ᶜ : Set V) :=
  (contractGraph G u v).induce {v}ᶜ

instance edgeContractionDecidableAdj (u v : V) : DecidableRel (edgeContraction G u v).Adj :=
  fun x y => inferInstanceAs (Decidable ((contractGraph G u v).Adj x.val y.val))

/-- The removed vertex is isolated in the graph before restricting its vertex type. -/
theorem contractGraph_not_adj_removed {u v : V} (huv : u ≠ v) (x : V) :
    ¬ (contractGraph G u v).Adj v x := by
  intro h
  have he : s(v, x) ∈ contractionEdges G u v := h.1
  rcases mem_union.mp he with he | he
  · have ha : (G.deleteIncidenceSet v).Adj v x := mem_edgeFinset.mp he
    exact (deleteIncidenceSet_adj.mp ha).2.1 rfl
  · obtain ⟨w, hw, he⟩ := mem_image.mp he
    have hwv : w ≠ v := by
      have ha := (G.mem_neighborFinset v w).mp (mem_sdiff.mp hw).1
      exact ha.ne.symm
    rcases Sym2.eq_iff.mp he with h | h
    · exact huv h.1
    · exact hwv h.2

/-- Removing the isolated name does not change the edges of the contracted graph. -/
theorem edgeContraction_card_edges {u v : V} (huv : G.Adj u v) :
    (edgeContraction G u v).edgeFinset.card +
      (G.neighborFinset v ∩ G.neighborFinset u).card + 1 = G.edgeFinset.card := by
  have hs : (contractGraph G u v).support ⊆ ({v}ᶜ : Set V) := by
    intro x hx heq
    have hxv : x = v := heq
    subst x
    obtain ⟨y, hy⟩ := hx
    exact contractGraph_not_adj_removed G huv.ne y hy
  change ((contractGraph G u v).induce ({v}ᶜ : Set V)).edgeFinset.card + _ + 1 = _
  rw [SimpleGraph.card_edgeFinset_induce_of_support_subset hs]
  exact contractGraph_card_edges G huv

/-- An edge contraction removes exactly one vertex. -/
theorem edgeContraction_card_vertices (v : V) :
    Fintype.card ({v}ᶜ : Set V) + 1 = Fintype.card V := by
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  rw [Fintype.card_compl_set]
  have hs : Fintype.card ({v} : Set V) = 1 := Fintype.card_unique
  omega

end GraphMinor.Thomason
