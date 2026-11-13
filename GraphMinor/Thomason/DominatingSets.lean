module

public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Tauto

/-!
# Finite domination sets

Thomason, page 262 (1984), says that a set dominates all vertices in the
set itself or adjacent to one of its vertices. We represent those vertices
by a finite union of neighbourhoods and take its complement to record the
vertices left undominated.
-/

@[expose] public section

namespace GraphMinor.Thomason

open SimpleGraph Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The vertices dominated by `Y`, as defined on page 262 of Thomason (1984). -/
def dominatedVertices (Y : Finset V) : Finset V :=
  Y ∪ Y.biUnion (fun v => G.neighborFinset v)

/-- The vertices outside `Y` with no neighbour in `Y`. -/
def undominatedVertices (Y : Finset V) : Finset V :=
  univ \ dominatedVertices G Y

@[simp] theorem dominatedVertices_empty : dominatedVertices G ∅ = ∅ := by
  simp [dominatedVertices]

@[simp] theorem dominatedVertices_singleton (v : V) :
    dominatedVertices G {v} = insert v (G.neighborFinset v) := by
  ext x
  simp [dominatedVertices]

/-- Inserting a vertex adds its closed neighbourhood to the dominated set. -/
theorem dominatedVertices_insert (v : V) (Y : Finset V) :
    dominatedVertices G (insert v Y) = dominatedVertices G Y ∪ insert v (G.neighborFinset v) := by
  ext x
  simp only [dominatedVertices, mem_union, mem_insert, mem_biUnion]
  constructor
  · rintro (h | ⟨y, hy, hxy⟩)
    · rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inl h)
    · rcases hy with rfl | hy
      · exact Or.inr (Or.inr hxy)
      · exact Or.inl (Or.inr ⟨y, hy, hxy⟩)
  · rintro ((h | h) | h | h)
    · exact Or.inl (Or.inr h)
    · obtain ⟨y, hy, hxy⟩ := h
      exact Or.inr ⟨y, Or.inr hy, hxy⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨v, Or.inl rfl, h⟩

@[simp] theorem undominatedVertices_empty : undominatedVertices G ∅ = univ := by
  simp [undominatedVertices]

/-- After inserting a vertex, precisely its closed neighbourhood is removed
from the undominated set. -/
theorem undominatedVertices_insert (v : V) (Y : Finset V) :
    undominatedVertices G (insert v Y) =
      undominatedVertices G Y \ insert v (G.neighborFinset v) := by
  ext x
  simp only [undominatedVertices, dominatedVertices_insert, mem_sdiff,
    mem_univ, true_and, mem_union, not_or]

/-- A vertex of `Y` is dominated by `Y`. -/
theorem mem_dominatedVertices_of_mem {Y : Finset V} {v : V} (hv : v ∈ Y) :
    v ∈ dominatedVertices G Y := Finset.mem_union_left _ hv

/-- The number of vertices outside the closed neighbourhood of `v`. -/
theorem card_undominatedVertices_singleton (v : V) :
    (undominatedVertices G {v}).card = Fintype.card V - (G.degree v + 1) := by
  rw [undominatedVertices, dominatedVertices_singleton,
    card_sdiff_of_subset (subset_univ _), card_univ, card_insert_of_notMem]
  · rw [G.card_neighborFinset_eq_degree]
  · simp

end GraphMinor.Thomason
