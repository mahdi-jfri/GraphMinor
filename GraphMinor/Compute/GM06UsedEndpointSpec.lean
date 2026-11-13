module

public import GraphMinor.Compute.GM06MarkUsedEndpoints

/-!
# Membership in the computed linkage-vertex mask

The endpoint scan marks exactly the endpoints of edges with a
marked directed label. This characterization connects the computed
mask to the vertices of the given drawing paths in VI (5.7).
-/

public section
namespace GraphMinor.Compute

/-- A marked vertex is exactly an endpoint of an edge with a marked direction. -/
theorem gm06UsedEndpointRows_mem_iff {n : ℕ} (es : List (Fin n × Fin n))
    (D : Finset (Fin (2 * es.length))) (v : Fin n) :
    v ∈ (gm06UsedEndpointRows es D).flatten.toFinset ↔
      ∃ i : Fin es.length,
        ((⟨2 * i.val, by omega⟩ : Fin (2 * es.length)) ∈ D ∨
          (⟨2 * i.val + 1, by omega⟩ : Fin (2 * es.length)) ∈ D) ∧
        (v = es[i.val].1 ∨ v = es[i.val].2) := by
  constructor
  · intro hv
    obtain ⟨row, hrow, hvrow⟩ := List.mem_flatten.mp (List.mem_toFinset.mp hv)
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    split_ifs at hvrow with hused
    · exact ⟨i, hused, by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hvrow⟩
    · exact False.elim (List.not_mem_nil hvrow)
  · rintro ⟨i, hused, hv⟩
    apply List.mem_toFinset.mpr
    apply List.mem_flatten.mpr
    refine ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
    simpa only [if_pos hused, List.mem_cons, List.not_mem_nil, or_false] using hv

end GraphMinor.Compute
