module

public import GraphMinor.GM02.TerminationGraph
import Mathlib.Data.Set.Card

/-!
# Degrees of termination matchings

A vertex of a termination matching has one neighbor exactly when it lies
in the support, and none otherwise. For two edge-disjoint terminations,
their union therefore has degree equal to the number of supports containing
the vertex. Comparing this with endpoint and internal degrees of the
contracted paths verifies condition (ii) in corrected II (2.9).
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u

/-- Each neighbor set in a termination matching is finite. -/
theorem Termination.neighborSet_finite {α : Type u} {S : Set α}
    (A : Termination S) (a : α) : (A.pairGraph.neighborSet a).Finite := by
  by_cases ha : a ∈ A.support
  · obtain ⟨b, hab⟩ := (A.mem_support_iff_exists_adj a).1 ha
    apply (Set.finite_singleton b).subset
    intro x hx
    exact A.pairGraph_neighbor_unique hx hab
  · have hempty : A.pairGraph.neighborSet a = ∅ := by
      ext b
      exact ⟨fun h => (ha ((A.mem_support_iff_exists_adj a).2 ⟨b, h⟩)).elim, False.elim⟩
    rw [hempty]
    exact Set.finite_empty

/-- A matching has degree one on its support and zero elsewhere. -/
theorem Termination.neighborSet_ncard {α : Type u} {S : Set α}
    (A : Termination S) (a : α) :
    (A.pairGraph.neighborSet a).ncard = if a ∈ A.support then 1 else 0 := by
  by_cases ha : a ∈ A.support
  · obtain ⟨b, hab⟩ := (A.mem_support_iff_exists_adj a).1 ha
    have heq : A.pairGraph.neighborSet a = {b} := by
      ext x
      exact ⟨fun h => A.pairGraph_neighbor_unique h hab, fun h => h.symm ▸ hab⟩
    rw [heq, Set.ncard_singleton, ite_eq_left ha]
  · have hempty : A.pairGraph.neighborSet a = ∅ := by
      ext b
      exact ⟨fun h => (ha ((A.mem_support_iff_exists_adj a).2 ⟨b, h⟩)).elim, False.elim⟩
    rw [hempty, Set.ncard_empty, ite_eq_right ha]

/-- In the union of edge-disjoint matchings, degree is the sum of the two
support membership indicators. -/
theorem Termination.union_neighborSet_ncard {α : Type u} {S : Set α}
    (A : Termination S) {T : Set α} (B : Termination T) (hdis : Disjoint (A.pairs : Set (Sym2 α)) (B.pairs : Set (Sym2 α))) (a : α) :
    ((A.pairGraph ⊔ B.pairGraph).neighborSet a).ncard =
      (if a ∈ A.support then 1 else 0) + (if a ∈ B.support then 1 else 0) := by
  have hn : Disjoint (A.pairGraph.neighborSet a) (B.pairGraph.neighborSet a) := by
    apply Set.disjoint_left.2
    intro b hA hB
    exact Set.disjoint_left.1 hdis (A.pairGraph_adj_iff.1 hA) (B.pairGraph_adj_iff.1 hB)
  have heq : (A.pairGraph ⊔ B.pairGraph).neighborSet a =
      A.pairGraph.neighborSet a ∪ B.pairGraph.neighborSet a := rfl
  rw [heq, Set.ncard_union_eq hn (A.neighborSet_finite a) (B.neighborSet_finite a),
    A.neighborSet_ncard, B.neighborSet_ncard]

end GraphMinor.GM02
