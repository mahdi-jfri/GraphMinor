module

public import GraphMinor.GM02.SideTermination

/-!
# The graph of all contracted side pieces

For corrected II (2.9), the union of the two new termination pair sets is
exactly the set of endpoint pairs of all maximal runs. No pair is lost
when this is made a simple graph, because every run is a nontrivial path
with distinct endpoints.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v
variable {α : Type u} {β : Type v} {S : Set α} (A : Termination S) (G H : Graph α β)
variable (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)
variable (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)

/-- The graph whose edges are the endpoint pairs in both side terminations. -/
noncomputable def sidePairGraph : SimpleGraph α := SimpleGraph.fromEdgeSet
  ((sideTermination A G H P hP true).pairs ∪ (sideTermination A G H P hP false).pairs : Finset (Sym2 α))

/-- Its edges are precisely the pairs of maximal side pieces. -/
theorem sidePairGraph_mem_edgeSet (e : Sym2 α) :
    e ∈ (sidePairGraph A G H P hP).edgeSet ↔ ∃ i : RunPieceIndex A G H P, i.pair A G H P = e := by
  rw [sidePairGraph, SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · intro he
    rcases Finset.mem_union.1 he.1 with hL | hR
    · obtain ⟨i, _, hi⟩ := (mem_sideTermination_pairs A G H P hP true e).1 hL
      exact ⟨i, hi⟩
    · obtain ⟨i, _, hi⟩ := (mem_sideTermination_pairs A G H P hP false e).1 hR
      exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    refine ⟨?_, i.pair_not_diag A G H P⟩
    cases hc : i.color A G H P with
    | false =>
      exact Finset.mem_union_right _ ((mem_sideTermination_pairs A G H P hP false _).2 ⟨i, hc, rfl⟩)
    | true =>
      exact Finset.mem_union_left _ ((mem_sideTermination_pairs A G H P hP true _).2 ⟨i, hc, rfl⟩)

/-- Every maximal piece gives an edge in the contracted pair graph. -/
theorem RunPieceIndex.pair_mem_sidePairGraph (i : RunPieceIndex A G H P) :
    i.pair A G H P ∈ (sidePairGraph A G H P hP).edgeSet :=
  (sidePairGraph_mem_edgeSet A G H P hP _).2 ⟨i, rfl⟩

end GraphMinor.GM02
