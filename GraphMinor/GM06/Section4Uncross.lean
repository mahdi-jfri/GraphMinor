module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section4Segment
import GraphMinor.GM06.Section4Choice
import GraphMinor.GM06.Section4Chord
import GraphMinor.GM06.Section4Excursion
import GraphMinor.GM06.Section4Overlap
import GraphMinor.GM06.Section4NearBoundary
import GraphMinor.GM11.Walks
import GraphMinor.Surface.ChartCells

/-!
# Uncrossing the minimal enclosed path

In Graph Minors VI, Section 4, page 124, choose an enclosed path with no
strictly smaller enclosed disc. If a competing path enters its inside, a
shortest excursion between vertices of its boundary is an interior chord.
Such a chord gives a smaller enclosed path, which is impossible. The competing
path therefore stays outside the inside, so its enclosed disc contains the
chosen disc. This turns the finite minimal choice into the least-disc path.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

private theorem drawing_inter_arc_closure_subset_path
    {S : Type u} [TopologicalSpace S] [T2Space S] {G P : Drawing S}
    {s t : S} {A : Set S} (hG : G.IsProper)
    (hseg : IsSegmentOf (bd S) (G.V ∩ bd S) A)
    (hP : IsPathDrawing P s t) (hPA : PathHomotopicToArc P s t A) :
    G.U ∩ closure A ⊆ P.U := by
  obtain ⟨a, ha, heq⟩ := hseg.1
  have hsub : A ⊆ bd S \ (G.V ∩ bd S) := by
    rw [← heq]
    exact connectedComponentIn_subset _ a
  have hconn : IsPreconnected A := by rw [← heq]; exact isPreconnected_connectedComponentIn
  obtain ⟨_, fA, _, hfA, _⟩ := hPA
  have hends := closure_arc_subset_of_isPreconnected hconn fA hfA.1 hfA.2.1
  rw [hfA.2.2.1, hfA.2.2.2] at hends
  have hclA : closure A ⊆ bd S := closure_minimal (hsub.trans sdiff_subset) (isClosed_bd S)
  obtain ⟨fP, hfP⟩ := hP.2
  intro x hx
  rcases hends hx.2 with hxA | hxend
  · exact False.elim ((hsub hxA).2 ⟨hG ⟨hclA hx.2, hx.1⟩, hclA hx.2⟩)
  · rw [← hfP.2.1]
    rcases mem_insert_iff.mp hxend with heq | heq
    · exact ⟨0, hfP.2.2.1.trans heq.symm⟩
    · exact ⟨1, hfP.2.2.2.trans (mem_singleton_iff.mp heq).symm⟩

/-- A simple competing path cannot enter the inside of an inclusion-minimal
candidate disc. Otherwise its shortest excursion would be the chord excluded
in the choice of the minimal path in Graph Minors VI, Section 4, page 124. -/
theorem competing_path_disjoint_discInt_of_inclusion_minimal
    {S : Type u} [TopologicalSpace S] {G P Q : Drawing S} {s t : S} {A D : Set S}
    (hS : IsSurface S) (hG : G.IsProper) (hst : s ≠ t)
    (hseg : IsSegmentOf (bd S) (G.V ∩ bd S) A)
    (hP : IsSubpathOf G P s t) (hPA : PathHomotopicToArc P s t A)
    (hD : IsEnclosedDisc P A D)
    (hmin : ∀ (R : Drawing S) (E : Set S), IsSubpathOf G R s t →
      PathHomotopicToArc R s t A → IsEnclosedDisc R A E → E ⊆ D → D ⊆ E)
    (hQ : IsSubpathOf G Q s t) : Disjoint Q.U (discInt D) := by
  let : T2Space S := hS.2.1
  apply disjoint_left.mpr
  intro x hxQ hxD
  have hPX : Disjoint P.U (discInt D) := disjoint_left.mpr (fun y hy hyD =>
    hyD.2 (hD.2.2 ▸ Or.inl hy))
  obtain ⟨WP, _, hVP, _⟩ := hP.2.2.1
  have hsP : s ∈ P.V := by rw [hVP]; exact WP.start_mem_support
  have htP : t ∈ P.V := by rw [hVP]; exact WP.end_mem_support
  obtain ⟨u, hu, v, hv, huv, R, hRQ, hRX, hvertices⟩ :=
    exists_subpath_meeting_with_no_internal_vertex hQ.2.2 hsP htP hst ⟨x, hxQ, hxD⟩
  have hRG : R.IsSubdrawing G := hRQ.1.trans hQ.1
  have hinter : R.U ∩ P.U ⊆ {u, v} :=
    path_intersection_subset_ends_of_vertices hRG hP.1 hRQ.2.2 hvertices hRX hPX
  have hGarc := drawing_inter_arc_closure_subset_path hG hseg hP.2.2 hPA
  obtain ⟨fR, hfR⟩ := hRQ.2.2.2
  have hline : IsLineWithEnds R.U u v := by
    have h := IsArcMap.isLineWithEnds (show IsArcMap fR from ⟨fR.continuous, hfR.1⟩)
    rwa [hfR.2.1, hfR.2.2.1, hfR.2.2.2] at h
  have hdisj : Disjoint (R.U \ {u, v}) (discBd D) := by
    apply disjoint_left.mpr
    intro y hy hyD
    rw [hD.2.2] at hyD
    have hyP : y ∈ P.U := hyD.elim id (fun hyA => hGarc ⟨hRG.U_subset hy.1, hyA⟩)
    exact hy.2 (hinter ⟨hy.1, hyP⟩)
  obtain ⟨z, hzR, hzD⟩ := hRX
  have hznot : z ∉ ({u, v} : Set S) := by
    intro hz
    have hzP : z ∈ P.U := by
      rcases mem_insert_iff.mp hz with heq | heq
      · rw [heq]; exact P.V_subset_U hu
      · rw [mem_singleton_iff.mp heq]; exact P.V_subset_U hv
    exact disjoint_left.mp hPX hzP hzD
  have hin : R.U \ {u, v} ⊆ discInt D := by
    rcases hD.1.side hS.2.2 hline.isPreconnected_diff hdisj with h | h
    · exact h
    · exact False.elim (disjoint_left.mp h ⟨hzR, hznot⟩ hzD.1)
  have hRD : R.U ⊆ D := hline.subset_closure_diff.trans
    (closure_minimal (hin.trans (discInt_subset D)) hD.1.isClosed)
  obtain ⟨WR, _, _, _⟩ := hRQ.2.2.1
  exact no_chord_between_vertices_of_inclusion_minimal hS hG hseg hP hPA hD hmin
    hu hv huv hRG WR hRD hinter

/-- The minimal boundary path `P(s,t,S)` exists whenever a path in its class
exists. This proves the existence assertion preceding Graph Minors VI (4.1),
page 124, including its least-disc interpretation. -/
theorem exists_isMinimalBoundaryPath_of_segment_path
    {S : Type u} [TopologicalSpace S] {G P₀ : Drawing S} {s t : S} {A : Set S}
    (hS : IsSurface S) (hG : G.IsProper) (hst : s ≠ t)
    (hseg : IsSegmentOf (bd S) (G.V ∩ bd S) A)
    (hP₀ : IsSubpathOf G P₀ s t) (hPA₀ : PathHomotopicToArc P₀ s t A) :
    ∃ P : Drawing S, IsMinimalBoundaryPath G s t A P := by
  obtain ⟨D₀, hD₀⟩ := exists_enclosedDisc_of_segment_path hS hG hP₀.1 hseg hPA₀
  obtain ⟨P, D, hP, hPA, hD, _, hmin⟩ :=
    exists_inclusion_minimal_enclosed_subpath hP₀ hPA₀ hD₀
  refine ⟨P, hP.1, hP.2.1, hP.2.2, hPA, D, hD, ?_⟩
  intro Q E hQsub hQU hQpath hQA hE
  have hQ : IsSubpathOf G Q s t := ⟨hQsub, hQU, hQpath⟩
  have havoid := competing_path_disjoint_discInt_of_inclusion_minimal
    hS hG hst hseg hP hPA hD hmin hQ
  exact enclosedDisc_subset_of_disjoint_path_discInt hS hG hseg hP.1 hQsub hD hE havoid

end GraphMinor.GM06
