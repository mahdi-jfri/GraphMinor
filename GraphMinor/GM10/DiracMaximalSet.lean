module

public import GraphMinor.GM10.DiracForest
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Order.Preorder.Finite

/-!
# A maximal connected set with a cycle outside it

For the low-valency input to Graph Minors X, (4.2), we follow the
maximal-component cycle argument of Illingworth and Wood, Theorem 7,
page 450. A maximal connected vertex set with a cycle outside it is
chosen by its cardinality. We first prove that such sets exist when
every vertex has at least three neighbours.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph Classical

universe u

/-- Deleting one vertex removes at most one neighbour of any other vertex. -/
theorem ncard_neighbors_le_induce_compl_singleton_add_one
    {V : Type u} [Fintype V] (G : SimpleGraph V) (a : V) (x : ({a}ᶜ : Set V)) :
    (G.neighborSet x.val).ncard ≤
      ((G.induce ({a}ᶜ : Set V)).neighborSet x).ncard + 1 := by
  classical
  have heq : Subtype.val '' (G.induce ({a}ᶜ : Set V)).neighborSet x =
      G.neighborSet x.val \ {a} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, z.property⟩
    · rintro ⟨hy, hya⟩
      exact ⟨⟨y, hya⟩, hy, rfl⟩
  have hcard := Set.ncard_le_ncard_sdiff_add_ncard (G.neighborSet x.val) {a}
  rw [← heq, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_singleton] at hcard
  exact hcard

/-- A nonempty finite graph with at least three neighbours at each vertex
has a connected nonempty vertex set with a cycle outside it. -/
theorem exists_connected_set_with_cycle_complement
    {V : Type u} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hdeg : ∀ x, 3 ≤ (G.neighborSet x).ncard) :
    ∃ H : Set V, (G.induce H).Connected ∧
      ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ ∀ x ∈ p.support, x ∉ H := by
  classical
  obtain ⟨a⟩ := ‹Nonempty V›
  have hne : (G.neighborSet a).Nonempty := (Set.ncard_pos (Set.toFinite _)).1 (by
    have := hdeg a
    omega)
  obtain ⟨b, hab⟩ := hne
  let : Nonempty ({a}ᶜ : Set V) := ⟨⟨b, by exact hab.ne.symm⟩⟩
  have hdeg' : ∀ x : ({a}ᶜ : Set V),
      2 ≤ ((G.induce ({a}ᶜ : Set V)).neighborSet x).ncard := by
    intro x
    have hle := ncard_neighbors_le_induce_compl_singleton_add_one G a x
    have := hdeg x.val
    omega
  obtain ⟨x, p, hp⟩ := exists_cycle_of_two_le_neighbors (G.induce ({a}ᶜ : Set V)) hdeg'
  have hconn : (G.induce ({a} : Set V)).Connected := by
    let : Nonempty ({a} : Set V) := ⟨⟨a, Set.mem_singleton a⟩⟩
    exact (SimpleGraph.IsTree.of_subsingleton : (G.induce ({a} : Set V)).IsTree).connected
  let f : G.induce ({a}ᶜ : Set V) →g G := { toFun := Subtype.val, map_rel' := id }
  refine ⟨{a}, hconn, x.val, p.map f, hp.map Subtype.val_injective, ?_⟩
  intro y hy
  rw [SimpleGraph.Walk.support_map] at hy
  obtain ⟨z, _, rfl⟩ := List.mem_map.1 hy
  exact z.property

/-- Choose a largest connected vertex set whose complement contains a
cycle. Maximality is a conclusion of this finite choice. -/
theorem exists_maximal_connected_set_with_cycle_complement
    {V : Type u} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hdeg : ∀ x, 3 ≤ (G.neighborSet x).ncard) :
    ∃ H : Set V, (G.induce H).Connected ∧
      (∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ ∀ x ∈ p.support, x ∉ H) ∧
      ∀ K : Set V, (G.induce K).Connected →
        (∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ ∀ x ∈ p.support, x ∉ K) →
        K.ncard ≤ H.ncard := by
  classical
  let 𝒜 : Set (Set V) := {H | (G.induce H).Connected ∧
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ ∀ x ∈ p.support, x ∉ H}
  have hne : 𝒜.Nonempty := exists_connected_set_with_cycle_complement G hdeg
  obtain ⟨H, hH⟩ := Set.Finite.exists_maximalFor Set.ncard 𝒜 (Set.toFinite 𝒜) hne
  refine ⟨H, hH.1.1, hH.1.2, ?_⟩
  intro K hK hcycle
  by_cases hle : K.ncard ≤ H.ncard
  · exact hle
  · exact hH.2 ⟨hK, hcycle⟩ (by omega)

end GraphMinor.GM10
