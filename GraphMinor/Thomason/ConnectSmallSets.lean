module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Tauto

/-!
# Connecting a small vertex set in a graph of minimum degree above half

Any two vertices have a common neighbour. Add one such neighbour for each
new vertex of a nonempty finite set to obtain a connected induced graph.
At most one vertex is added per step. This proves the nonempty-set case
of Thomason's Lemma 2 (1984), page 262, used in the clique construction.
-/

public section

namespace GraphMinor.Thomason

open SimpleGraph

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Above half the order, the neighbourhoods of any two vertices intersect. -/
theorem exists_commonNeighbor_of_degree_gt_half
    (hdeg : ∀ x : V, Fintype.card V < 2 * G.degree x) (u v : V) :
    ∃ w : V, G.Adj u w ∧ G.Adj v w := by
  have hu := hdeg u
  have hv := hdeg v
  have hcard := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  have hle := Finset.card_le_univ (G.neighborFinset u ∪ G.neighborFinset v)
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hcard
  have hpos : 0 < (G.neighborFinset u ∩ G.neighborFinset v).card := by omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  exact ⟨w, (G.mem_neighborFinset u w).mp (Finset.mem_inter.mp hw).1,
    (G.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).2⟩

/-- Thomason's Lemma 2, p. 262, for a nonempty vertex set: at most `|Y|-1`
extra vertices suffice to connect `Y` when the minimum degree exceeds half
the order. Each induction step adds a common neighbour. -/
theorem exists_connecting_set
    (hdeg : ∀ x : V, Fintype.card V < 2 * G.degree x)
    (Y : Finset V) (hne : Y.Nonempty) :
    ∃ Z : Finset V, Z.card ≤ Y.card - 1 ∧
      (G.induce ((Y ∪ Z : Finset V) : Set V)).Connected := by
  revert hne
  induction Y using Finset.induction_on with
  | empty =>
    intro hne
    exact (Finset.not_nonempty_empty hne).elim
  | @insert y S hy ih =>
    intro _
    by_cases hS : S.Nonempty
    · obtain ⟨Z, hZ, hconn⟩ := ih hS
      obtain ⟨x, hx⟩ := hS
      obtain ⟨w, hxw, hyw⟩ := exists_commonNeighbor_of_degree_gt_half G hdeg x y
      refine ⟨insert w Z, ?_, ?_⟩
      · have hi := Finset.card_insert_le w Z
        have hpos := Finset.card_pos.mpr (show S.Nonempty from ⟨x, hx⟩)
        rw [Finset.card_insert_of_notMem hy]
        omega
      · have hpair : (G.induce ({y, w} : Set V)).Connected :=
          SimpleGraph.induce_pair_connected_of_adj hyw
        have hc := G.connected_induce_union hconn.preconnected hpair.preconnected
          (show x ∈ ((S ∪ Z : Finset V) : Set V) from Finset.mem_union_left _ hx)
          (show w ∈ ({y, w} : Set V) from Or.inr rfl) hxw
        have heq : ((insert y S ∪ insert w Z : Finset V) : Set V) =
            ((S ∪ Z : Finset V) : Set V) ∪ {y, w} := by
          ext a
          simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_insert,
            Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        rw [heq]
        exact hc
    · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      refine ⟨∅, by simp, ?_⟩
      have hc : (G.induce ({y} : Set V)).Connected :=
        (SimpleGraph.Subgraph.singletonSubgraph_connected (G := G) (v := y)).induce_verts
      have heq : ((insert y ∅ ∪ ∅ : Finset V) : Set V) = {y} := by
        ext a
        simp
      rw [heq]
      exact hc

end GraphMinor.Thomason
