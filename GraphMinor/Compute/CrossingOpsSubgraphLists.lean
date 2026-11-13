module

public import GraphMinor.Compute.CrossingOpsReplLists

/-!
# Filtering an encoded graph to a subgraph

When edges are deleted, each new adjacency list is the old list filtered by the
new adjacency relation. These lists remain duplicate-free and need no more space
than the old graph's packed lists.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- The numerical test for adjacency in a subgraph, rejecting indices outside the graph. -/
def graphFilterKeep {N : ℕ} (H : SimpleGraph (Fin N)) [DecidableRel H.Adj] (x y : ℕ) : Bool :=
  if hx : x < N then if hy : y < N then decide (H.Adj ⟨x, hx⟩ ⟨y, hy⟩) else false else false

/-- The old adjacency list filtered to the new graph. -/
def graphFilterList {N : ℕ} (lists : Fin N → List ℕ) (H : SimpleGraph (Fin N))
    [DecidableRel H.Adj] (x : ℕ) : List ℕ := (listOf lists x).filter (graphFilterKeep H x)

/-- Filtering to a subgraph gives an adjacency-list family for that subgraph. -/
theorem isAdjListFamily_graphFilterList {N : ℕ} {G H : SimpleGraph (Fin N)}
    [DecidableRel H.Adj] {lists : Fin N → List ℕ} (h : IsAdjListFamily G lists) (hHG : H ≤ G) :
    IsAdjListFamily H (fun u => graphFilterList lists H u.val) := by
  intro u
  simp only [graphFilterList, listOf_fin]
  refine ⟨fun y hy => (h u).1 y (List.mem_of_mem_filter hy), (h u).2.1.filter _,
    (List.length_filter_le _ _).trans (h u).2.2.1, ?_⟩
  intro v
  simp only [List.mem_filter, graphFilterKeep, u.isLt, v.isLt, dite_true, decide_eq_true_eq,
    (h u).2.2.2 v]
  exact ⟨And.right, fun hh => ⟨hHG hh, hh⟩⟩

/-- Filtering cannot increase the total number of adjacency entries. -/
theorem length_flatUpTo_graphFilterList_le {N : ℕ} {G H : SimpleGraph (Fin N)}
    [DecidableRel H.Adj] {lists : Fin N → List ℕ} (h : IsAdjListFamily G lists) :
    (flatUpTo (graphFilterList lists H) N).length ≤ 2 * G.edgeSet.ncard := by
  rw [length_flatUpTo]
  calc
    (∑ x ∈ Finset.range N, (graphFilterList lists H x).length) ≤
        ∑ x ∈ Finset.range N, (listOf lists x).length :=
      Finset.sum_le_sum (fun _ _ => List.length_filter_le _ _)
    _ = 2 * G.edgeSet.ncard := by
      rw [← length_flatUpTo]
      exact length_flatUpTo_eq (fun u => by simpa [listOf_fin] using h u)

end GraphMinor.Compute.Crossing
