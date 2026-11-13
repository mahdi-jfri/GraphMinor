module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4Segment
import GraphMinor.GM06.Section4Routed
import GraphMinor.GM06.Section3Basic
import GraphMinor.GM06.Section5Red
import GraphMinor.GM07.Section3
import GraphMinor.GM11.Section4b
import GraphMinor.GM11.Walks
import GraphMinor.Surface.DiscMerge

/-!
# Forced boundary vertices of the minimal path

For Graph Minors VI (4.1), page 124, the disc of the minimal boundary path
lies in the disc of every competing path. A point of the surface boundary
inside a closed disc lies on its boundary. Consequently, every boundary vertex
of the minimal path belongs to every competing path in the specified class.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

private theorem proper_subdrawing {S : Type u} [TopologicalSpace S]
    {G Q : Drawing S} (hG : G.IsProper) (hQ : Q.IsSubdrawing G) : Q.IsProper := by
  intro x hx
  have hxG : x ∈ G.V := hG ⟨hx.1, hQ.U_subset hx.2⟩
  by_contra hxQ
  obtain ⟨e, he, hxe⟩ := Q.exists_edge_of_mem hx.2 hxQ
  exact ((hQ.2 he).2.1 hxe).2 hxG

/-- A point of the surface boundary in a closed disc belongs to the boundary
of that disc. This is the topological comparison used in Graph Minors VI
(4.1), page 124. -/
theorem mem_discBd_of_mem_bd_of_mem_disc
    {S : Type u} [TopologicalSpace S] (hS : IsSurface S)
    {Δ : Set S} (hΔ : IsClosedDisc Δ) {x : S} (hx : x ∈ Δ) (hxb : x ∈ bd S) :
    x ∈ discBd Δ := by
  let : T2Space S := hS.2.1
  by_contra hnot
  exact hxb (isInteriorPoint_of_mem_discInt hS.2.2 hΔ ⟨hx, hnot⟩)

/-- Every boundary vertex of the minimal boundary path lies on every path in
its prescribed class. This is the common comparison behind Graph Minors VI
(4.1)(ii) and (iii), page 124. -/
theorem boundary_vertex_mem_of_isMinimalBoundaryPath
    {S : Type u} [TopologicalSpace S] {G P Q : Drawing S} {s t : S} {A : Set S}
    (hS : IsSurface S) (hG : G.IsProper)
    (hseg : IsSegmentOf (bd S) (G.V ∩ bd S) A)
    (hP : IsMinimalBoundaryPath G s t A P)
    (hQ : IsSubpathOf G Q s t) (hQA : PathHomotopicToArc Q s t A)
    {x : S} (hx : x ∈ P.V ∩ bd S) : x ∈ Q.V := by
  let : T2Space S := hS.2.1
  obtain ⟨D, hD, hmin⟩ := hP.2.2.2.2
  obtain ⟨E, hE⟩ := exists_enclosedDisc_of_segment_path hS hG hQ.1 hseg hQA
  have hDE : D ⊆ E := hmin Q E hQ.1 hQ.2.1 hQ.2.2 hQA hE
  have hxD : x ∈ D := by
    apply discBd_subset D
    rw [hD.2.2]
    exact Or.inl (P.V_subset_U hx.1)
  have hxEb := mem_discBd_of_mem_bd_of_mem_disc hS hE.1 (hDE hxD) hx.2
  rw [hE.2.2] at hxEb
  have hxQU : x ∈ Q.U := by
    rcases hxEb with hxQ | hxA
    · exact hxQ
    · have hinter := path_inter_segment_closure_subset_ends hG hP.1 hseg hP.2.2.2.1
      have hxend := hinter ⟨P.V_subset_U hx.1, hxA⟩
      obtain ⟨f, hf⟩ := hQ.2.2.2
      rw [← hf.2.1]
      rcases mem_insert_iff.mp hxend with heq | heq
      · exact ⟨0, hf.2.2.1.trans heq.symm⟩
      · exact ⟨1, hf.2.2.2.trans (mem_singleton_iff.mp heq).symm⟩
  exact proper_subdrawing hG hQ.1 ⟨hx.2, hxQU⟩

private theorem exists_simple_walk_of_isPathDrawing
    {S : Type u} [TopologicalSpace S] {Q : Drawing S} {s t x y : S}
    (hQ : IsPathDrawing Q s t) (hx : x ∈ Q.V) (hy : y ∈ Q.V) :
    ∃ W : GraphWalk Q.toGraph x y, W.IsSimple := by
  classical
  obtain ⟨W, _, hV, _⟩ := hQ.1
  have hxW : x ∈ W.support := by rw [hV] at hx; exact hx
  have hyW : y ∈ W.support := by rw [hV] at hy; exact hy
  obtain ⟨Wx, _, _⟩ := W.exists_append_of_mem hxW
  obtain ⟨Wy, _, _⟩ := W.exists_append_of_mem hyW
  obtain ⟨R, hR, _, _⟩ := GM11.GraphWalk.exists_isSimple (Wx.reverse.append Wy)
  exact ⟨R, hR⟩

private theorem mem_component_of_walk
    {S : Type u} {C H : Graph S (Set S)} (hC : IsGraphComponent C H)
    {x y : S} (hx : x ∈ Graph.vertexSet C) (W : GraphWalk H x y) :
    y ∈ Graph.vertexSet C := by
  rw [hC.eq_compOf_of_mem hx]
  exact ⟨W.mem_vertexSet_of_mem_support W.end_mem_support, ⟨W⟩⟩

/-- Graph Minors VI (4.1)(ii), page 124: a boundary vertex of the minimal
path in another component of `H` rules out a homotopic forest subgraph.
The minimal-path comparison forces this vertex onto the corresponding path
in any hypothetical feasible forest. -/
theorem theorem_4_1_ii
    {S : Type u} [TopologicalSpace S] {G H Hst P : Drawing S} {s t : S} {A : Set S}
    (hS : IsSurface S) (hG : G.IsProper) (hbd : H.V ∩ bd S = G.V ∩ bd S)
    (hseg : IsSegmentOf (bd S) (H.V ∩ bd S) A)
    (hs : s ∈ H.V ∩ bd S) (ht : t ∈ H.V ∩ bd S) (hne : s ≠ t)
    (hHst : IsSubpathOf H Hst s t) (hHA : PathHomotopicToArc Hst s t A)
    (hP : IsMinimalBoundaryPath G s t A P)
    (C : Graph S (Set S)) (hC : IsGraphComponent C H.toGraph)
    (hnot : s ∉ Graph.vertexSet C ∨ t ∉ Graph.vertexSet C)
    (hbad : (P.V ∩ (Graph.vertexSet C ∩ bd S)).Nonempty) :
    ¬ HasHomotopicForestSubgraph G H := by
  let : T2Space S := hS.2.1
  rintro ⟨F, hFG, _, hFH⟩
  have hself : HasHomotopicForestSubgraph F H :=
    ⟨F, Drawing.IsSubdrawing.refl F, subset_rfl, hFH⟩
  obtain ⟨Q, hQF, hQA⟩ :=
    exists_subpath_homotopicToArc_of_hasHomotopicForestSubgraph hself hs ht hne hHst hHA
  have hQG : IsSubpathOf G Q s t :=
    ⟨hQF.1.trans hFG, (hQF.1.trans hFG).U_subset, hQF.2.2⟩
  obtain ⟨x, hxP, hxC, hxb⟩ := hbad
  have hsegG : IsSegmentOf (bd S) (G.V ∩ bd S) A := by rw [← hbd]; exact hseg
  have hxQ : x ∈ Q.V := boundary_vertex_mem_of_isMinimalBoundaryPath
    hS hG hsegG hP hQG hQA ⟨hxP, hxb⟩
  have hmem : ∀ y ∈ Q.V, y ∈ H.V ∩ bd S → y ∈ Graph.vertexSet C := by
    intro y hyQ hyH
    by_cases hxy : x = y
    · exact hxy ▸ hxC
    have hxF : x ∈ F.V ∩ bd S := ⟨hQF.1.1 hxQ, hxb⟩
    have hyF : y ∈ F.V ∩ bd S := ⟨hQF.1.1 hyQ, hyH.2⟩
    obtain ⟨WQ, hWQ⟩ := exists_simple_walk_of_isPathDrawing hQF.2.2 hxQ hyQ
    obtain ⟨WF, hsup, _⟩ := hQF.1.exists_walk_up WQ
    have hWF : WF.IsSimple := by
      unfold GraphWalk.IsSimple
      rw [hsup]
      exact hWQ
    obtain ⟨WH, _⟩ := (hFH.2.2.2.2.2 x hxF y hyF hxy).1.mp ⟨WF, hWF⟩
    exact mem_component_of_walk hC hxC WH
  obtain ⟨W, _, hV, _⟩ := hQF.2.2.1
  have hsQ : s ∈ Q.V := by rw [hV]; exact W.start_mem_support
  have htQ : t ∈ Q.V := by rw [hV]; exact W.end_mem_support
  rcases hnot with hsnot | htnot
  · exact hsnot (hmem s hsQ hs)
  · exact htnot (hmem t htQ ht)

private theorem curvesHomotopic_of_range_subset_disc
    {S : Type u} [TopologicalSpace S] {D : Set S} (hD : IsClosedDisc D)
    {f g : Curve S} (hf : range f ⊆ D) (hg : range g ⊆ D)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) : CurvesHomotopic f g := by
  have hflat : GM11.IsFlat D := by
    intro γ hγ
    obtain ⟨c, _, H, _, hH0, hH1⟩ := hD.isSimplyConnectedSet.2 γ hγ
    exact ⟨c, mem_univ _, H, fun _ => mem_univ _, hH0, hH1⟩
  exact GM07.IsFlat.curvesHomotopic hflat hf hg h0 h1

/-- Graph Minors VI (4.1)(iii), page 124: an incompatible homotopy class from
an intermediate boundary vertex of the minimal path to its last end rules out
feasibility. The two competing subpaths lie in one closed disc. -/
theorem theorem_4_1_iii
    {S : Type u} [TopologicalSpace S] {G H Hst P : Drawing S} {s t : S} {A : Set S}
    (hS : IsSurface S) (hG : G.IsProper) (hbd : H.V ∩ bd S = G.V ∩ bd S)
    (hseg : IsSegmentOf (bd S) (H.V ∩ bd S) A)
    (hs : s ∈ H.V ∩ bd S) (ht : t ∈ H.V ∩ bd S) (hne : s ≠ t)
    (hHst : IsSubpathOf H Hst s t) (hHA : PathHomotopicToArc Hst s t A)
    (hP : IsMinimalBoundaryPath G s t A P)
    {x : S} (hxP : x ∈ P.V ∩ bd S)
    (Hxt Pxt : Drawing S) (hHxt : IsSubpathOf H Hxt x t) (hPxt : IsSubpathOf P Pxt x t)
    (hnot : ¬ PathsHomotopic Hxt Pxt x t) : ¬ HasHomotopicForestSubgraph G H := by
  let : T2Space S := hS.2.1
  rintro ⟨F, hFG, _, hFH⟩
  have hself : HasHomotopicForestSubgraph F H :=
    ⟨F, Drawing.IsSubdrawing.refl F, subset_rfl, hFH⟩
  obtain ⟨Q, hQF, hQA⟩ :=
    exists_subpath_homotopicToArc_of_hasHomotopicForestSubgraph hself hs ht hne hHst hHA
  have hQG : IsSubpathOf G Q s t :=
    ⟨hQF.1.trans hFG, (hQF.1.trans hFG).U_subset, hQF.2.2⟩
  have hsegG : IsSegmentOf (bd S) (G.V ∩ bd S) A := by rw [← hbd]; exact hseg
  have hxQ : x ∈ Q.V := boundary_vertex_mem_of_isMinimalBoundaryPath
    hS hG hsegG hP hQG hQA hxP
  obtain ⟨WQ, _, hVQ, _⟩ := hQF.2.2.1
  have htQ : t ∈ Q.V := by rw [hVQ]; exact WQ.end_mem_support
  obtain ⟨fH, hfH⟩ := hHxt.2.2.2
  have hxt : x ≠ t := by
    intro heq
    exact zero_ne_one (hfH.1 (hfH.2.2.1.trans (heq.trans hfH.2.2.2.symm)))
  obtain ⟨WR, hWR⟩ := exists_simple_walk_of_isPathDrawing hQF.2.2 hxQ htQ
  let R := walkDrawing Q WR
  have hRQ : R.IsSubdrawing Q := walkDrawing_isSubdrawing Q WR
  have hRF : IsSubpathOf F R x t :=
    ⟨hRQ.trans hQF.1, (hRQ.trans hQF.1).U_subset,
      isPathDrawing_walkDrawing_of_isSimple Q hWR hxt⟩
  have hxF : x ∈ F.V ∩ bd S := ⟨hQF.1.1 hxQ, hxP.2⟩
  have htF : t ∈ F.V ∩ bd S := ⟨hQF.1.1 htQ, ht.2⟩
  obtain ⟨fR, gH, hfR, hgH, hRH⟩ :=
    pathsHomotopic_of_subpaths_of_forestsHomotopic hFH hxF htF hxt hRF hHxt
  obtain ⟨fP, hfP⟩ := hPxt.2.2.2
  obtain ⟨D, hD, hmin⟩ := hP.2.2.2.2
  obtain ⟨E, hE⟩ := exists_enclosedDisc_of_segment_path hS hG hQG.1 hsegG hQA
  have hDE : D ⊆ E := hmin Q E hQG.1 hQG.2.1 hQG.2.2 hQA hE
  have hQU : Q.U ⊆ E := fun y hy => discBd_subset E (hE.2.2 ▸ Or.inl hy)
  have hPU : P.U ⊆ D := fun y hy => discBd_subset D (hD.2.2 ▸ Or.inl hy)
  have hRE : range fR ⊆ E := by rw [hfR.2.1]; exact hRQ.U_subset.trans hQU
  have hPE : range fP ⊆ E := by rw [hfP.2.1]; exact hPxt.2.1.trans (hPU.trans hDE)
  have hRP : CurvesHomotopic fR fP := curvesHomotopic_of_range_subset_disc hE.1 hRE hPE
    (hfR.2.2.1.trans hfP.2.2.1.symm) (hfR.2.2.2.trans hfP.2.2.2.symm)
  exact hnot ⟨gH, fP, hgH, hfP,
    GM07.CurvesHomotopic.trans (GM07.CurvesHomotopic.symm hRH) hRP⟩

end GraphMinor.GM06
