module

public import GraphMinor.GM06.Alg34ComponentEnumeration

/-!
# Every unsplit division block belongs to a component branch

Choose a label from a nonempty represented block and its canonical
component root. The no-split test puts every other block label in that
same component. This proves the coverage premise of VI (3.3)(iv) from
the actual input test, rather than assuming a partition of the blocks.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- Every block of an unsplit represented division lies in an indexed
canonical component of the drawing. -/
theorem division_subset_root_component (h : GM06DrawingRep x G Δ)
    (hs : x.hasSplitBlock = false) (hD : IsDivision Δ) {δ : Set S} (hδ : δ ∈ Δ) :
    ∃ i : Fin x.componentRoots.length,
      δ ⊆ (GM06.compOf G.toGraph (h.vertex (x.componentRoots.get i)).val).vertexSet := by
  obtain ⟨L, hL, hLδ⟩ := h.division.subset hδ
  obtain ⟨p, hp⟩ := hD.2.1 δ hδ
  obtain ⟨b, hb, _⟩ := hLδ.symm ▸ hp
  obtain ⟨a, ha, hba⟩ := x.exists_componentRoot b
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  refine ⟨i, ?_⟩
  rw [hi]
  intro q hq
  obtain ⟨c, hc, hcq⟩ := hLδ.symm ▸ hq
  rw [← hcq]
  exact ⟨(h.vertex c).property, (h.vertex_reachable_iff a c).mp
    (hba.symm.trans (x.block_reachable_of_no_split hs hL hb hc))⟩

end GraphMinor.Compute.GM06DrawingRep
