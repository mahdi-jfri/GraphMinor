module

public import GraphMinor.Compute.GM06PuncturedGraphData

/-!
# The removed vertex is isolated in the search graph

The finite component search for Reduction 2 keeps the removed
vertex's index but removes every edge touching it. This index is
therefore isolated. A search from a different vertex never marks
it, so the retained index does not alter the components of the
graph after the vertex is deleted.
-/

public section
namespace GraphMinor.Compute

/-- Every filtered endpoint pair avoids the removed vertex at both ends. -/
theorem gm06PuncturedPairs_ends_ne {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n)
    {e : Fin n × Fin n} (he : e ∈ gm06PuncturedPairs tagged cut) :
    e.1 ≠ cut ∧ e.2 ≠ cut := by
  change e ∈ tagged.filterMap _ at he
  obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp he
  by_cases hb : p.2 = 1
  · by_cases hA : p.1.1 = cut
    · simp [hb, hA] at hp
    · by_cases hB : p.1.2 = cut
      · simp [hb, hA, hB] at hp
      · have hpe : p.1 = e := by simpa only [hb, hA, hB, ite_true, ite_false, Option.some.injEq] using hp
        exact hpe ▸ ⟨hA, hB⟩
  · simp [hb] at hp

/-- No adjacency in the punctured search graph meets the removed index. -/
theorem gm06PuncturedGraphData_not_adj_cut {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut a : Fin n) :
    ¬ (gm06PuncturedGraphData tagged cut).vertexGraph.Adj a cut := by
  rintro ⟨_, j, hj⟩
  have hends := gm06PuncturedPairs_ends_ne tagged cut (List.getElem_mem j.isLt)
  rcases hj with hj | hj
  · exact hends.2 hj.2.symm
  · exact hends.1 hj.2.symm

/-- Searches from other labels do not reach the isolated removed index. -/
theorem gm06PuncturedGraphData_not_reachable_cut {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut source : Fin n) (hsource : source ≠ cut) :
    ¬ (gm06PuncturedGraphData tagged cut).vertexGraph.Reachable source cut := by
  apply SimpleGraph.not_reachable_of_neighborSet_right_eq_empty hsource
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact gm06PuncturedGraphData_not_adj_cut tagged cut a
    (SimpleGraph.Adj.symm ha)

end GraphMinor.Compute
