module

public import GraphMinor.GM07.Defs
public import GraphMinor.Surface.SurfaceGraph
import GraphMinor.GM08.Section18CircleGraph
import GraphMinor.GM08.Section18LoopGraphs
import GraphMinor.GM08.Section18BranchGraphs

/-!
# A graph representation for every schism

Every schism is the support of a finite graph with no isolated vertices,
and every boundary contact can be taken as a vertex. Circles are
subdivided at their boundary contacts. Proper arcs use their two ends.
The other cases use the graph representations of their loops and joining
lines. This supplies a graph for the cut and drawing pullback in VIII
Section 18.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

private theorem graph_proper_arc {S : Type w} [TopologicalSpace S] {F : Set S}
    (hF : IsProperIArc F) :
    ∃ V : Set S, ∃ E : Set (Set S), IsGraph V E ∧ V ⊆ ⋃₀ E ∧ gr V E = F ∧ F ∩ bd S ⊆ V := by
  obtain ⟨u, v, huv, hbd, hl⟩ := hF
  have hends : ({u, v} : Set S) ⊆ F := by
    rintro x (rfl | rfl)
    · exact hl.left_mem
    · exact hl.right_mem
  refine ⟨{u, v}, {F}, ?_, ?_, ?_, hbd.subset⟩
  · refine ⟨(finite_singleton v).insert u, finite_singleton F, ?_, ?_⟩
    · rintro e rfl
      exact ⟨u, v, huv, hl, inter_eq_right.mpr hends⟩
    · rintro e rfl f rfl hne
      exact (hne rfl).elim
  · simpa only [sUnion_singleton] using hends
  · simpa only [gr, sUnion_singleton] using union_eq_self_of_subset_left hends

/-- Every schism has a finite graph representation with no isolated
vertices and with every boundary contact marked. This supplies the graph
of the cut in VIII Section 18, pages 285–286. -/
theorem exists_graph_of_schism {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) {F : Set S} (hF : GM07.IsSchism F) :
    ∃ V : Set S, ∃ E : Set (Set S), IsGraph V E ∧ V ⊆ ⋃₀ E ∧ gr V E = F ∧ F ∩ bd S ⊆ V := by
  have : T2Space S := hS.2.1
  rcases hF with hi | hii | hiii | hiv | hv | hvi
  · exact exists_graph_oArc_with_finite_marks hi.1 hi.2.2.1 inter_subset_left
  · exact graph_proper_arc hii.1
  · exact graph_proper_arc hiii.1
  · obtain ⟨hshape, hoff, _⟩ := hiv
    rcases hshape with hbar | hwedge
    · obtain ⟨A, B, P, u, v, hA, hB, hAB, hP, hu, hv, hPA, hPB, rfl⟩ := hbar
      obtain ⟨V, E, hg, hno, hgr, _, _⟩ := exists_graph_barbell hA hB hAB hP hu hv hPA hPB
      exact ⟨V, E, hg, hno, hgr, hoff ▸ empty_subset _⟩
    · obtain ⟨A, B, u, hA, hB, hAB, rfl⟩ := hwedge
      obtain ⟨V, E, hg, hno, hgr, _⟩ := exists_graph_meeting_circles hA hB hAB
      exact ⟨V, E, hg, hno, hgr, hoff ▸ empty_subset _⟩
  · obtain ⟨hshape, hoff, _⟩ := hv
    obtain ⟨P, Q, R, u, v, huv, hP, hQ, hR, hPQ, hPR, hQR, rfl⟩ := hshape
    obtain ⟨V, E, hg, hno, hgr, _, _⟩ := exists_graph_theta huv hP hQ hR hPQ hPR hQR
    exact ⟨V, E, hg, hno, hgr, hoff ▸ empty_subset _⟩
  · obtain ⟨v, A, P, C, D, u, hA, hP, huv, hPA, rfl, _, _, _, _, _, hbd⟩ := hvi
    obtain ⟨V, E, hg, hno, hgr, _, hvV⟩ := exists_graph_whiskered_circle hA hP huv hPA
    exact ⟨V, E, hg, hno, hgr, hbd ▸ singleton_subset_iff.mpr hvV⟩

end GraphMinor.GM08
