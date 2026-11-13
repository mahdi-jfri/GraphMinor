module

public import GraphMinor.GM10.DiracMaximalSet
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Absorbing a neighbour of the maximal connected set

This is the maximality step in the proof of the external low-valency
input to Graph Minors X, (4.2). If a neighbour outside the chosen set
is absorbed, no cycle can remain outside the enlarged set. Moreover,
every such neighbour belongs to every cycle outside the original set.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph Classical

universe u

private theorem connected_insert_of_neighbor
    {V : Type u} {G : SimpleGraph V} {H : Set V} (hH : (G.induce H).Connected)
    {a z : V} (ha : a ∈ H) (haz : G.Adj a z) :
    (G.induce (insert z H)).Connected := by
  let : Nonempty ({z} : Set V) := ⟨⟨z, Set.mem_singleton z⟩⟩
  have hzconn : (G.induce ({z} : Set V)).Connected :=
    (SimpleGraph.IsTree.of_subsingleton : (G.induce ({z} : Set V)).IsTree).connected
  have hconn := G.connected_induce_union hH.preconnected hzconn.preconnected ha
    (Set.mem_singleton z) haz
  have heq : H ∪ {z} = insert z H := Set.union_singleton
  exact heq ▸ hconn

/-- Absorbing a neighbour of a largest connected set with a cycle outside
it leaves a forest. Maximality is the local choice made in the proof. -/
theorem acyclic_complement_insert_of_maximal_connected_set
    {V : Type u} [Fintype V] (G : SimpleGraph V) (H : Set V)
    (hH : (G.induce H).Connected)
    (hmax : ∀ K : Set V, (G.induce K).Connected →
      (∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ ∀ x ∈ p.support, x ∉ K) →
      K.ncard ≤ H.ncard)
    {a z : V} (ha : a ∈ H) (hz : z ∉ H) (haz : G.Adj a z) :
    (G.induce (insert z H)ᶜ).IsAcyclic := by
  classical
  have hconn := connected_insert_of_neighbor hH ha haz
  intro b p hp
  let f : G.induce (insert z H)ᶜ →g G := { toFun := Subtype.val, map_rel' := id }
  have hcycle : ∃ b, ∃ q : G.Walk b b, q.IsCycle ∧
      ∀ x ∈ q.support, x ∉ insert z H := by
    refine ⟨b.val, p.map f, hp.map Subtype.val_injective, ?_⟩
    intro x hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
    exact y.property
  have hbound := hmax (insert z H) hconn hcycle
  rw [Set.ncard_insert_of_notMem hz] at hbound
  omega

/-- Every neighbour outside the maximal connected set lies on each cycle
outside that set. Otherwise it could be absorbed without losing the cycle. -/
theorem boundary_neighbor_mem_cycle_of_maximal_connected_set
    {V : Type u} [Fintype V] (G : SimpleGraph V) (H : Set V)
    (hH : (G.induce H).Connected)
    (hmax : ∀ K : Set V, (G.induce K).Connected →
      (∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ ∀ x ∈ p.support, x ∉ K) →
      K.ncard ≤ H.ncard)
    {b : V} (p : G.Walk b b) (hp : p.IsCycle)
    (havoid : ∀ x ∈ p.support, x ∉ H)
    {a z : V} (ha : a ∈ H) (hz : z ∉ H) (haz : G.Adj a z) : z ∈ p.support := by
  classical
  by_contra hnot
  have hconn := connected_insert_of_neighbor hH ha haz
  have hcycle : ∃ b, ∃ q : G.Walk b b, q.IsCycle ∧
      ∀ x ∈ q.support, x ∉ insert z H := by
    refine ⟨b, p, hp, ?_⟩
    intro x hx hxin
    rcases hxin with rfl | hxH
    · exact hnot hx
    · exact havoid x hx hxH
  have hbound := hmax (insert z H) hconn hcycle
  rw [Set.ncard_insert_of_notMem hz] at hbound
  omega

end GraphMinor.GM10
