module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Logic.Relation

/-!
# Connected unions of cells during deletion

Deleting a vertex and its incident edges puts those cells into the
complement of the drawing. They can join old regions when a retained
cell meets another cell's closure. The lemmas here give the connectedness
argument for finite chains of such incidences, for the region update in
(3.3)(i). The sets are ordinary topological subsets, with connectedness
proved rather than stored in an input record.
-/

@[expose] public section
namespace GraphMinor.GM06

open Set Relation

universe u v

/-- Two cells touch when one contains a limit point of the other. -/
def alg34CellTouch {S : Type u} [TopologicalSpace S] {ι : Type v}
    (A : ι → Set S) (i j : ι) : Prop :=
  (A i ∩ closure (A j)).Nonempty ∨ (A j ∩ closure (A i)).Nonempty

/-- Two connected sets have connected union when one meets the other's
closure at a point contained in the union. -/
theorem alg34_connected_union_of_inter_closure {S : Type u} [TopologicalSpace S]
    {A B : Set S} (hA : IsConnected A) (hB : IsConnected B)
    (htouch : (A ∩ closure B).Nonempty) : IsConnected (A ∪ B) := by
  obtain ⟨x, hxA, hxB⟩ := htouch
  have hB' : IsConnected (insert x B) := hB.subset_closure (subset_insert x B)
    (insert_subset hxB subset_closure)
  have hconn := hA.union ⟨x, hxA, mem_insert x B⟩ hB'
  simpa only [union_insert, insert_eq_of_mem (mem_union_left B hxA)] using hconn

/-- A touching pair of connected cells has connected union. -/
theorem alg34_connected_union_of_cellTouch {S : Type u} [TopologicalSpace S]
    {ι : Type v} {A : ι → Set S} {i j : ι}
    (hA : IsConnected (A i)) (hB : IsConnected (A j)) (h : alg34CellTouch A i j) :
    IsConnected (A i ∪ A j) := by
  rcases h with h | h
  · exact alg34_connected_union_of_inter_closure hA hB h
  · simpa only [union_comm] using alg34_connected_union_of_inter_closure hB hA h

/-- Each finite chain of touching connected cells lies in a connected
union of cells from the same chain. -/
theorem alg34_cell_chain_connected {S : Type u} [TopologicalSpace S]
    {ι : Type v} (A : ι → Set S) (K : Set ι) (hA : ∀ i ∈ K, IsConnected (A i))
    {i j : ι} (hi : i ∈ K) (hj : j ∈ K)
    (hpath : ReflTransGen (fun a b => a ∈ K ∧ b ∈ K ∧ alg34CellTouch A a b) i j) :
    ∃ U : Set S, IsConnected U ∧ U ⊆ ⋃ a ∈ K, A a ∧ A i ⊆ U ∧ A j ⊆ U := by
  induction hpath with
  | refl =>
    exact ⟨A i, hA i hi, subset_biUnion_of_mem hi, Subset.rfl, Subset.rfl⟩
  | @tail j k hpath hstep ih =>
    obtain ⟨U, hU, hUK, hiU, hjU⟩ := ih hstep.1
    have htouch : (U ∩ closure (A k)).Nonempty ∨ (A k ∩ closure U).Nonempty := by
      rcases hstep.2.2 with h | h
      · exact Or.inl (h.mono (inter_subset_inter_left _ hjU))
      · exact Or.inr (h.mono (inter_subset_inter_right _ (closure_mono hjU)))
    have hconn : IsConnected (U ∪ A k) := by
      rcases htouch with h | h
      · exact alg34_connected_union_of_inter_closure hU (hA k hj) h
      · simpa only [union_comm] using alg34_connected_union_of_inter_closure (hA k hj) hU h
    exact ⟨U ∪ A k, hconn, union_subset hUK (subset_biUnion_of_mem hj),
      hiU.trans subset_union_left, subset_union_right⟩

end GraphMinor.GM06
