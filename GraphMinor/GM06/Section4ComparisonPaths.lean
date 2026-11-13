module

public import GraphMinor.GM06.Section4Comparison
import GraphMinor.GM06.Section4NoObstructions
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section4InitialInterval
import GraphMinor.GM06.Section5Red
import GraphMinor.GM07.PushForest

/-!
# Minimal boundary paths lie in the comparison graph

In the last argument of VI (4.2), page 126, the two subpaths from the
ends of an edge to the fixed terminal vertex are homotopic to their
forest paths. Joining one to the reverse of the other shows that the
edge is homotopic to the forest path between its ends. Flatness of the
two forests removes the shared terminal part.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- Every edge of the minimal boundary path belongs to G′ in the proof
of Graph Minors VI (4.2), page 126. -/
theorem minimalBoundaryPath_edges_subset_comparison
    {S : Type} [TopologicalSpace S] [T2Space S]
    {G H Hst P : Drawing S} {A : Set S} {s t : S}
    (hforest : IsGraphForest H.toGraph)
    (hno41 : ¬ Section4Condition41Applies G H) (hno2 : ¬ Section4Reduction2Applies G H)
    (hbd : H.V ∩ bd S = G.V ∩ bd S)
    {K : Graph S (Set S)} (hK : IsGraphComponent K H.toGraph) (hsK : s ∈ Graph.vertexSet K)
    (hA : A ∈ segmentsOf (bd S) (H.V ∩ bd S))
    (hs : s ∈ H.V ∩ bd S) (ht : t ∈ H.V ∩ bd S) (hst : s ≠ t)
    (hsA : s ∈ closure A) (htA : t ∈ closure A)
    (hHst : IsSubpathOf H Hst s t) (hHA : PathHomotopicToArc Hst s t A)
    (hP : IsMinimalBoundaryPath G s t A P) :
    P.E ⊆ componentHomotopicEdges G H K := by
  have hPV := minimalBoundaryPath_vertices_component_of_no_obstructions
    hno41 hno2 hbd hK hsK hA hs ht hst hsA htA hHst hHA hP
  have hpath : IsPathDrawing P s t := hP.2.2.1
  have htP : t ∈ P.V := (isPathDrawing_end_vertices hpath).2
  have htK : t ∈ Graph.vertexSet K := (hPV htP).1
  have hreps (v : S) (hv : v ∈ P.V) :
      ∃ p q : Path v t, (∀ z, p z ∈ P.U) ∧ (∀ z, q z ∈ H.U) ∧ p.Homotopic q := by
    by_cases hvt : v = t
    · subst v
      exact ⟨Path.refl t, Path.refl t, fun _ => P.V_subset_U htP,
        fun _ => H.V_subset_U ht.1, Path.Homotopic.refl _⟩
    · obtain ⟨Hvt, hHvt⟩ := exists_subpath_of_mem_component hK (hPV hv).1 htK hvt
      obtain ⟨Qvt, hQvt⟩ := exists_subpath_of_isPathDrawing hpath hv htP hvt
      obtain ⟨f, g, hf, hg, hfg⟩ := pathsHomotopic_of_not_condition41
        hno41 hA hs ht hst hsA htA hHst hHA hP ⟨hv, (hPV hv).2⟩ hHvt hQvt
      let p : Path v t := ⟨g, hg.2.2.1, hg.2.2.2⟩
      let q : Path v t := ⟨f, hf.2.2.1, hf.2.2.2⟩
      refine ⟨p, q, ?_, ?_, ?_⟩
      · intro z
        apply hQvt.2.1
        rw [← hg.2.1]
        exact mem_range_self z
      · intro z
        apply hHvt.2.1
        rw [← hf.2.1]
        exact mem_range_self z
      · exact (GM07.homotopic_of_curves (p := q) (q := p) hfg).symm
  have hPf := isGraphForest_of_isPathDrawing hpath
  intro e he
  refine ⟨hP.1.2 he, ?_⟩
  intro u v hlG
  have hlP : P.toGraph.IsLink e u v := (hP.1.isLink_iff he).mpr hlG
  have huP : u ∈ P.V := hlP.left_mem
  have hvP : v ∈ P.V := hlP.right_mem
  have huv : u ≠ v := GM07.link_ne hPf hlP
  refine ⟨hPV huP, hPV hvP, huv, ?_⟩
  obtain ⟨Huv, hHuv⟩ := exists_subpath_of_mem_component hK (hPV huP).1 (hPV hvP).1 huv
  obtain ⟨f, hf⟩ := exists_parametrizesSet_closure_edge P hlP huv
  obtain ⟨g, hg⟩ := hHuv.2.2.2
  let p : Path u v := ⟨f, hf.2.2.1, hf.2.2.2⟩
  let q : Path u v := ⟨g, hg.2.2.1, hg.2.2.2⟩
  obtain ⟨pu, qu, hpu, hqu, hu⟩ := hreps u huP
  obtain ⟨pv, qv, hpv, hqv, hv⟩ := hreps v hvP
  have hp : ∀ z, p z ∈ P.U := by
    intro z
    apply P.closure_subset_U he
    rw [← hf.2.1]
    exact mem_range_self z
  have hq : ∀ z, q z ∈ H.U := by
    intro z
    apply hHuv.2.1
    rw [← hg.2.1]
    exact mem_range_self z
  have hleft : p.Homotopic (pu.trans pv.symm) :=
    GM07.IsFlat.flat (GM07.isFlat_forest hPf) _ _ hp
      (GM07.mem_trans hpu (fun z => hpv (unitInterval.symm z)))
  have hmiddle : (pu.trans pv.symm).Homotopic (qu.trans qv.symm) := hu.hcomp hv.symm₂
  have hright : (qu.trans qv.symm).Homotopic q :=
    GM07.IsFlat.flat (GM07.isFlat_forest hforest) _ _
      (GM07.mem_trans hqu (fun z => hqv (unitInterval.symm z))) hq
  exact ⟨Huv, hHuv, f, g, hf, hg,
    GM07.curves_of_homotopic (hleft.trans (hmiddle.trans hright))⟩

/-- A routed boundary segment joins its ends in G′ when neither
(4.1) nor Reduction 2 applies. -/
theorem exists_comparison_walk_of_segment
    {S : Type} [TopologicalSpace S] [T2Space S]
    {G H Hst : Drawing S} {A : Set S} {s t : S}
    (hforest : IsGraphForest H.toGraph)
    (hno41 : ¬ Section4Condition41Applies G H) (hno2 : ¬ Section4Reduction2Applies G H)
    (hbd : H.V ∩ bd S = G.V ∩ bd S)
    {K : Graph S (Set S)} (hK : IsGraphComponent K H.toGraph) (hsK : s ∈ Graph.vertexSet K)
    (hA : A ∈ segmentsOf (bd S) (H.V ∩ bd S))
    (hs : s ∈ H.V ∩ bd S) (ht : t ∈ H.V ∩ bd S) (hst : s ≠ t)
    (hsA : s ∈ closure A) (htA : t ∈ closure A)
    (hHst : IsSubpathOf H Hst s t) (hHA : PathHomotopicToArc Hst s t A) :
    Nonempty (GraphWalk (componentComparisonDrawing G H K).toGraph s t) := by
  obtain ⟨P, hP⟩ := exists_minimalBoundaryPath_of_not_condition41
    hno41 hA hs ht hst hsA htA hHst hHA
  have hPV := minimalBoundaryPath_vertices_component_of_no_obstructions
    hno41 hno2 hbd hK hsK hA hs ht hst hsA htA hHst hHA hP
  have hPE := minimalBoundaryPath_edges_subset_comparison
    hforest hno41 hno2 hbd hK hsK hA hs ht hst hsA htA hHst hHA hP
  have hW : Graph.vertexSet K ∩ bd S ⊆ G.V := by
    intro v hv
    exact (hbd ▸ (show v ∈ H.V ∩ bd S from ⟨hK.1.vertexSet_mono hv.1, hv.2⟩)).1
  have hsub : P.IsSubdrawing (componentComparisonDrawing G H K) := by
    constructor
    · rw [componentComparisonDrawing_V G H K hW]
      exact hPV
    · rw [componentComparisonDrawing_E]
      exact hPE
  obtain ⟨W, _, _, _⟩ := hP.2.2.1.1
  have hle : P.toGraph ≤ (componentComparisonDrawing G H K).toGraph :=
    { vertexSet_mono := hsub.1
      isLink_mono := fun _ _ _ hl => (hsub.isLink_iff hl.1).mp hl }
  exact ⟨W.mono hle⟩

end GraphMinor.GM06
