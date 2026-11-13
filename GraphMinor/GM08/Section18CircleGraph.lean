module

public import GraphMinor.Surface.SurfaceGraph
import GraphMinor.Surface.CutLoop

/-!
# A circle with marked vertices

A circle has a finite graph representation with no isolated vertices.
Subdivide that graph at each point of a finite marked set. Its underlying
set stays the same. For the boundary-touching circle case of VIII (18.2),
the marked set is the intersection with the surface boundary.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- Represent a circle as a finite graph in which every point of a given
finite subset is a vertex. This is the graph preparation for the
boundary-touching circle cut in VIII (18.2), page 286. -/
theorem exists_graph_oArc_with_finite_marks {S : Type w} [TopologicalSpace S]
    [T2Space S] {F M : Set S} (hF : IsOArc F) (hM : M.Finite) (hMF : M ⊆ F) :
    ∃ V : Set S, ∃ E : Set (Set S), IsGraph V E ∧ V ⊆ ⋃₀ E ∧ gr V E = F ∧ M ⊆ V := by
  classical
  induction M, hM using Set.Finite.induction_on with
  | empty =>
      have hc : FinConn (F \ gr (∅ : Set S) ∅) := by
        simpa only [gr, sUnion_empty, union_empty, sdiff_empty] using
          finConn_of_isPreconnected hF.isPreconnected
      obtain ⟨V, E, _, hg, hgr, hno⟩ := isGraph_empty.add_curve hF hc
      refine ⟨V, E, hg, hno (empty_subset _), ?_, empty_subset _⟩
      simpa only [gr, sUnion_empty, union_empty, empty_union] using hgr
  | @insert x M hx _ ih =>
      obtain ⟨V, E, hg, hno, hgr, hMV⟩ := ih ((subset_insert x M).trans hMF)
      obtain ⟨E', hg', hgr', hEE'⟩ := hg.add_point x
      have hxF : x ∈ F := hMF (mem_insert x M)
      have hFedges : F ⊆ ⋃₀ E := by rw [← hgr]; exact union_subset hno subset_rfl
      refine ⟨insert x V, E', hg', ?_, ?_, ?_⟩
      · rintro y (rfl | hy)
        · exact hEE' (hFedges hxF)
        · exact hEE' (hno hy)
      · rw [hgr', hgr, insert_eq_of_mem hxF]
      · rintro y (rfl | hy)
        · exact mem_insert _ _
        · exact mem_insert_of_mem x (hMV hy)

end GraphMinor.GM08
