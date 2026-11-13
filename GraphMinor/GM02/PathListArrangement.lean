module

public import GraphMinor.GM02.ListInsertion
public import Mathlib.Data.Set.Basic

/-!
# Path-list arrangements for the crossing-scheme count

The counting proof for II (2.8) records the internal separator vertices of
each original pair's path as a list. The lists are disjoint and have no
repetitions. Unused vertices receive one of two labels, represented by a
subset of the unused vertices. Erasing one vertex preserves this data.
-/

@[expose] public section
namespace GraphMinor.GM02
open Set Classical
universe u t

/-- Auxiliary finite data for counting crossing schemes: disjoint lists
from a fixed vertex set and a subset of the unused vertices. -/
structure PathListArrangement {α : Type u} (S : Set α) (I : Type t) where
  /-- One list for each original pair. -/
  paths : I → List α
  /-- Each list has distinct vertices. -/
  nodup : ∀ i, (paths i).Nodup
  /-- All listed vertices are in the fixed set. -/
  vertex_mem : ∀ i v, v ∈ paths i → v ∈ S
  /-- Different lists have disjoint vertex sets. -/
  disjoint : ∀ i j, i ≠ j → ∀ v ∈ paths i, v ∉ paths j
  /-- One of the two labels for unused vertices. -/
  marked : Set α
  /-- Marked vertices belong to the fixed set. -/
  marked_subset : marked ⊆ S
  /-- No listed vertex is marked. -/
  marked_unused : ∀ v ∈ marked, ∀ i, v ∉ paths i

/-- The lists and the unused labels determine an arrangement. -/
theorem PathListArrangement.ext_data {α : Type u} {S : Set α} {I : Type t}
    {A B : PathListArrangement S I} (hp : A.paths = B.paths) (hm : A.marked = B.marked) :
    A = B := by
  cases A
  cases B
  cases hp
  cases hm
  rfl

/-- Erase one vertex from every path and from the marked unused set. -/
noncomputable def PathListArrangement.erase {α : Type u} {S : Set α} {I : Type t}
    (A : PathListArrangement S I) (a : α) : PathListArrangement (S \ {a}) I where
  paths i := (A.paths i).erase a
  nodup i := List.Nodup.erase a (A.nodup i)
  vertex_mem i v hv := ⟨A.vertex_mem i v (List.mem_of_mem_erase hv),
    fun h => (A.nodup i).not_mem_erase (h ▸ hv)⟩
  disjoint i j hij v hvi hvj :=
    A.disjoint i j hij v (List.mem_of_mem_erase hvi) (List.mem_of_mem_erase hvj)
  marked := A.marked \ {a}
  marked_subset _ hv := ⟨A.marked_subset hv.1, hv.2⟩
  marked_unused v hv i hvi := A.marked_unused v hv.1 i (List.mem_of_mem_erase hvi)

/-- At most one path list contains a given vertex. -/
theorem PathListArrangement.unique_path {α : Type u} {S : Set α} {I : Type t}
    (A : PathListArrangement S I) {i j : I} {a : α}
    (hi : a ∈ A.paths i) (hj : a ∈ A.paths j) : i = j := by
  by_contra h
  exact A.disjoint i j h a hi hj

end GraphMinor.GM02
