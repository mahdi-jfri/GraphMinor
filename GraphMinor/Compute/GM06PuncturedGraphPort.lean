module

public import GraphMinor.Compute.GM06PuncturedGraphCut

/-!
# A searched component attaches only at the removed vertex

For Reduction 2 in VI (5.7), page 133, any active edge from a
searched component either stays in it or meets the removed
vertex. Edges avoiding that vertex occur in the finite graph
searched by breadth-first search. This gives the attachment
condition needed to construct the drawing separation.
-/

public section
namespace GraphMinor.Compute

/-- An active endpoint pair avoiding the removed index occurs in the search graph. -/
theorem gm06PuncturedPairs_mem_of_active {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n)
    {e : Fin n × Fin n} {b : ℕ} (he : (e, b) ∈ tagged) (hb : b = 1)
    (hA : e.1 ≠ cut) (hB : e.2 ≠ cut) : e ∈ gm06PuncturedPairs tagged cut := by
  unfold gm06PuncturedPairs
  exact List.mem_filterMap.mpr ⟨(e, b), he, by simp [hb, hA, hB]⟩

/-- A distinct active pair avoiding the removed vertex is an adjacency of the search graph. -/
theorem gm06PuncturedGraphData_adj_of_active {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n)
    {a b : Fin n} {flag : ℕ} (he : ((a, b), flag) ∈ tagged) (hflag : flag = 1)
    (ha : a ≠ cut) (hb : b ≠ cut) (hab : a ≠ b) :
    (gm06PuncturedGraphData tagged cut).vertexGraph.Adj a b := by
  have hmem := gm06PuncturedPairs_mem_of_active tagged cut he hflag ha hb
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hmem
  refine ⟨hab, ⟨j, hj⟩, Or.inl ?_⟩
  exact ⟨(congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm⟩

/-- Every active edge from a searched component stays in the component
or ends at the removed vertex. Loops need no separate reachability step. -/
theorem gm06PuncturedGraphData_reachable_port {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut source : Fin n) (hsource : source ≠ cut)
    {a b : Fin n} {flag : ℕ} (he : ((a, b), flag) ∈ tagged) (hflag : flag = 1)
    (ha : (gm06PuncturedGraphData tagged cut).vertexGraph.Reachable source a) :
    (gm06PuncturedGraphData tagged cut).vertexGraph.Reachable source b ∨ b = cut := by
  have hac : a ≠ cut := by
    intro h
    exact gm06PuncturedGraphData_not_reachable_cut tagged cut source hsource (h ▸ ha)
  by_cases hbc : b = cut
  · exact Or.inr hbc
  · left
    by_cases hab : a = b
    · exact hab ▸ ha
    · exact ha.trans (gm06PuncturedGraphData_adj_of_active tagged cut he hflag hac hbc hab).reachable

/-- The same attachment property holds when the active edge is read
from its second endpoint towards its first endpoint. -/
theorem gm06PuncturedGraphData_reachable_port_right {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut source : Fin n) (hsource : source ≠ cut)
    {a b : Fin n} {flag : ℕ} (he : ((a, b), flag) ∈ tagged) (hflag : flag = 1)
    (hb : (gm06PuncturedGraphData tagged cut).vertexGraph.Reachable source b) :
    (gm06PuncturedGraphData tagged cut).vertexGraph.Reachable source a ∨ a = cut := by
  have hbc : b ≠ cut := by
    intro h
    exact gm06PuncturedGraphData_not_reachable_cut tagged cut source hsource (h ▸ hb)
  by_cases hac : a = cut
  · exact Or.inr hac
  · left
    by_cases hab : a = b
    · exact hab.symm ▸ hb
    · exact hb.trans (gm06PuncturedGraphData_adj_of_active tagged cut he hflag hac hbc hab).symm.reachable

end GraphMinor.Compute
