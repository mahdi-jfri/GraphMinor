module

public import GraphMinor.GM01.CombShiftRanges
public import GraphMinor.GM01.CombTailCentres
import GraphMinor.GM01.PathsInRegions

/-!
# A selected comb interval lies beyond an earlier cut

Graph Minors I, (4.14), page 59, retains an old comb segment inside
the late block range. Every selected centre is beyond the cut.
The replacing paths avoid the cut centre because neither source end
is that centre. A path with one end in the avoidance region and
avoiding the cut stays in that region. Thus the whole selected
subdivision, including its path interiors, lies beyond the cut.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- A selected interval strictly beyond a spine cut lies in its
avoidance region, as used for the late piece in GM01 (4.14), page 59. -/
theorem combSegmentSupport_subset_later_region {α β : Type*} {γ L m : ℕ}
    {N : Graph α β} (c : (pathComb γ L).verts → α) (hc : Injective c)
    (hcentres : ∀ v, c v ∈ V(N))
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (i : Fin L) (offset : ℕ) (hio : i.val < offset) (hbound : offset + m ≤ L) :
    combSegmentSupport c P offset hbound ⊆ vertexAvoidanceRegion N
      (c ⟨Sum.inl ⟨L - 1, by have := i.isLt; omega⟩, pathComb_spine_mem γ L _⟩)
      (c ⟨Sum.inl i, pathComb_spine_mem γ L i⟩) := by
  let cut : (pathComb γ L).verts := ⟨Sum.inl i, pathComb_spine_mem γ L i⟩
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  intro x hx
  rcases (mem_combSegmentSupport_iff c P offset hbound x).mp hx with ⟨v, hv, _, rfl⟩ | ⟨e, hxe, hEnds⟩
  · exact comb_subdivision_later_vertex_mem_region hc hcentres hPaths i v (by omega)
  · obtain ⟨a, b, he, hP, _⟩ := hPaths e
    have ha := hEnds a (he ▸ Sym2.mem_mk_left a b)
    have hcut : c cut ∉ V(P e) := by
      intro h
      have hmem := (subdivision_centre_mem_path_iff hc hRanges e cut).mp h
      have hh := (hEnds cut hmem).1
      change offset ≤ i.val at hh
      omega
    have hA := comb_subdivision_later_vertex_mem_region hc hcentres hPaths i a (by omega)
    exact path_subset_vertexAvoidanceRegion hP hA hcut hxe

end GraphMinor.GM01
