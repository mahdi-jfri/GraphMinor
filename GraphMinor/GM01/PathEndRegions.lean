module

public import GraphMinor.GM01.VertexAvoidanceRegions
public import GraphMinor.GM09.Defs
import GraphMinor.GM09.Basic
import GraphMinor.GM01.PathsInRegions
import GraphMinor.GM16.PathEndSubpath

/-!
# A path to a region boundary stays in the region until its end

The boundary extension in Graph Minors I, (4.8), page 58, takes a path
to the vertex separating the early blocks from the remaining comb.
Every other vertex stays in the later region. For any such vertex,
its initial subpath avoids the final boundary vertex, because an end
of a simple path cannot be internal to a subpath. The region's
reachability condition then extends along that subpath.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- A simple path from an avoidance region to its cut vertex stays
inside the region except at that final vertex. This supplies the
boundary avoidance in GM01 (4.8), page 58. -/
theorem path_subset_vertexAvoidanceRegion_insert_cut {α β : Type*}
    {G P : Graph α β} {last cut a : α}
    (hP : IsGraphPathWithEnds G P a cut)
    (ha : a ∈ vertexAvoidanceRegion G last cut) :
    V(P) ⊆ insert cut (vertexAvoidanceRegion G last cut) := by
  intro x hx
  by_cases hxc : x = cut
  · exact Or.inl hxc
  have hane : a ≠ cut := (vertexAvoidanceRegion_subset G last cut ha).2
  obtain ⟨Q, hQP, _, hQ⟩ := hP.exists_subpath hP.left_mem hx
  have hcut : cut ∉ V(Q) := by
    intro hcQ
    rcases GraphMinor.GM16.path_start_mem_subpath_is_end hP.symm hQ hQP hcQ with hca | hcx
    · exact hane hca.symm
    · exact hxc hcx.symm
  exact Or.inr (path_subset_vertexAvoidanceRegion hQ ha hcut hQ.right_mem)

end GraphMinor.GM01
