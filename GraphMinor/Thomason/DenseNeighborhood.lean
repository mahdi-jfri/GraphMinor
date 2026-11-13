module

public import GraphMinor.Statement
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.NeighborMinor
import GraphMinor.Thomason.ExactDenseMinor
import GraphMinor.Thomason.ContractionMinor
import GraphMinor.Thomason.DensitySubgraphs
import GraphMinor.Minor.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Reducing a density bound to a small dense minor

Choose a vertex-minimal dense minor and retain exactly `d|V|` edges.
Vertex deletion shows that all its degrees exceed `d`. The degree-sum
formula gives a vertex with degree at most `2d`. Its neighbourhood has
minimum degree at least `d`, by the edge-contraction count. This is the
reduction following Lemma 2.1 in Thomason's *Extremal functions for graph
minors* (2006), page 363.
-/

public section

namespace GraphMinor.Thomason

open SimpleGraph Graph

universe u

/-- Neighbours of a vertex inside a neighbourhood graph are exactly the
common neighbours in the original graph. The equivalence forgets the
extra subtype layer. -/
theorem degree_neighborhood_eq_commonNeighbors {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (x : G.neighborSet u) :
    (G.induce (G.neighborSet u)).degree x = (G.commonNeighbors u x.val).ncard := by
  let e : (G.induce (G.neighborSet u)).neighborSet x ≃ G.commonNeighbors u x.val := {
    toFun := fun z => ⟨z.val.val, z.val.property, z.property⟩
    invFun := fun z => ⟨⟨z.val, z.property.1⟩, z.property.2⟩
    left_inv := fun z => rfl
    right_inv := fun z => rfl }
  simpa only [Nat.card_coe_set_eq, SimpleGraph.ncard_neighborSet] using Nat.card_congr e

/-- Every non-null finite simple graph with at least `d > 0` edges per
vertex has a non-null minor with at most `2d` vertices and minimum degree
at least `d`. Choose a vertex-minimal dense minor and then take the
neighbourhood of a vertex of minimum degree. Its centre extends every
clique minor by one vertex, as in Thomason (1984), Lemma 1, p. 262. -/
theorem exists_small_dense_minor_with_clique_extension {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (hdpos : 0 < d)
    (hd : d * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj)
      (_ : Nonempty W),
      IsIsoMinor (Graph.ofSimpleGraph H) (Graph.ofSimpleGraph G) ∧
      Fintype.card W ≤ 2 * d ∧ (∀ x : W, d ≤ H.degree x) ∧
      ∀ q : ℕ, IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q))) (Graph.ofSimpleGraph H) →
        IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (q + 1)))) (Graph.ofSimpleGraph G) := by
  classical
  obtain ⟨W, hW, H, hH, hne, hm, hcard, hmin⟩ :=
    exists_vertex_minimal_dense_minor_with_exact_edges G d hd
  let := hW
  let := hH
  let := hne
  have hWpos : 0 < Fintype.card W := Fintype.card_pos
  have hWtwo : 2 ≤ Fintype.card W := by
    have hbound := H.card_edgeFinset_le_card_choose_two
    by_contra hsmall
    have hz : (Fintype.card W).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz, hcard] at hbound
    have hpos := Nat.mul_pos hdpos hWpos
    omega
  have hdegree (u : W) : d < H.degree u := by
    by_contra hsmall
    have hdegle : H.degree u ≤ d := by omega
    have hverts := edgeContraction_card_vertices u
    have hneDel : Nonempty ({u}ᶜ : Set W) := Fintype.card_pos_iff.mp (by omega)
    let K := H.induce ({u}ᶜ : Set W)
    have hcount : K.edgeFinset.card = H.edgeFinset.card - H.degree u := by
      exact (H.card_edgeFinset_induce_compl_singleton u).trans
        (H.card_edgeFinset_deleteIncidenceSet u)
    have hdenDel : d * Fintype.card ({u}ᶜ : Set W) ≤ K.edgeFinset.card := by
      rw [hcount, hcard]
      have hmul : d * Fintype.card W = d * Fintype.card ({u}ᶜ : Set W) + d := by
        rw [← hverts, Nat.mul_add, Nat.mul_one]
      rw [hmul]
      omega
    have hle := hmin ({u}ᶜ : Set W) inferInstance K inferInstance hneDel
      (isIsoMinor_ofSimpleGraph_induce H _) hdenDel
    omega
  have hcommon (u v : W) (huv : H.Adj u v) : d ≤ (H.commonNeighbors u v).ncard := by
    have hcn : (H.commonNeighbors u v).ncard =
        (H.neighborFinset v ∩ H.neighborFinset u).card := by
      simp only [Set.ncard_eq_toFinset_card', SimpleGraph.commonNeighbors_eq,
        Set.toFinset_inter, ← SimpleGraph.neighborFinset_def, Finset.inter_comm]
    rw [hcn]
    by_contra hsmall
    have hc : (H.neighborFinset v ∩ H.neighborFinset u).card + 1 ≤ d := by omega
    let K := edgeContraction H u v
    have hneK : Nonempty ({v}ᶜ : Set W) := ⟨⟨u, huv.ne⟩⟩
    have hcount := edgeContraction_card_edges H huv
    have hverts := edgeContraction_card_vertices v
    have hdenK : d * Fintype.card ({v}ᶜ : Set W) ≤ K.edgeFinset.card := by
      rw [← hverts, Nat.mul_add, Nat.mul_one] at hcard
      dsimp only [K]
      omega
    have hle := hmin ({v}ᶜ : Set W) inferInstance K inferInstance hneK
      (edgeContraction_isIsoMinor H huv) hdenK
    omega
  have hsum : H.minDegree * Fintype.card W ≤ 2 * H.edgeFinset.card := by
    calc
      H.minDegree * Fintype.card W = ∑ _ : W, H.minDegree := by simp [Nat.mul_comm]
      _ ≤ ∑ w : W, H.degree w := Finset.sum_le_sum fun w _ => H.minDegree_le_degree w
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
  have hminle : H.minDegree ≤ 2 * d := by
    by_contra hlarge
    have hlt := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge hlarge) hWpos
    rw [hcard, ← Nat.mul_assoc] at hsum
    omega
  obtain ⟨u, hu⟩ := H.exists_minimal_degree_vertex
  obtain ⟨w, hw⟩ := (H.degree_pos_iff_exists_adj u).mp (lt_trans hdpos (hdegree u))
  have hneN : Nonempty (H.neighborSet u) := ⟨⟨w, hw⟩⟩
  let J := H.induce (H.neighborSet u)
  refine ⟨H.neighborSet u, inferInstance, J, inferInstance, hneN,
    (isIsoMinor_ofSimpleGraph_induce H _).trans hm, ?_, ?_, ?_⟩
  · rw [H.card_neighborSet_eq_degree, ← hu]
    exact hminle
  · intro x
    rw [degree_neighborhood_eq_commonNeighbors H u x]
    exact hcommon u x.val x.property

  · intro q hq
    exact (clique_isIsoMinor_of_neighbor_minor H u hq).trans hm

/-- Every non-null finite simple graph with at least `d>0` edges per
vertex has a non-null minor with at most `2d` vertices and minimum degree
at least `d`. -/
theorem exists_small_dense_minor {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (hdpos : 0 < d)
    (hd : d * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj)
      (_ : Nonempty W),
      IsIsoMinor (Graph.ofSimpleGraph H) (Graph.ofSimpleGraph G) ∧
      Fintype.card W ≤ 2 * d ∧ ∀ x : W, d ≤ H.degree x := by
  obtain ⟨W, hW, H, hH, hne, hm, hsize, hdegree, _⟩ :=
    exists_small_dense_minor_with_clique_extension G d hdpos hd
  exact ⟨W, hW, H, hH, hne, hm, hsize, hdegree⟩

end GraphMinor.Thomason
