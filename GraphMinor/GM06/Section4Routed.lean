module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Red
import GraphMinor.GM07.Section3

/-!
# Paths in a routed forest

For Graph Minors VI (4.1), a forest subgraph homotopic to the specified forest
must supply a path in each specified boundary-to-boundary homotopy class.
We pass from simple walks to path drawings, and compare their injective
parameterizations with curves tracing the walks.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

universe u

private theorem subdrawing_graph_le {S : Type u} [TopologicalSpace S]
    {P G : Drawing S} (h : P.IsSubdrawing G) : P.toGraph ≤ G.toGraph where
  vertexSet_mono := h.1
  isLink_mono _ _ _ hl := (h.isLink_iff hl.1).mp hl

private theorem traces_mono {S : Type u} [TopologicalSpace S]
    {P G : Drawing S} (h : P.IsSubdrawing G) {s t : S}
    {W : GraphWalk P.toGraph s t} {f : Curve S} (hf : CurveTracesWalk P f W) :
    CurveTracesWalk G f (W.mono (subdrawing_graph_le h)) := by
  induction hf with
  | nil hv f hc => exact .nil (h.1 hv) f hc
  | cons hl f₁ f₂ f hf₁ hf₂ hconcat ih =>
    exact .cons ((h.isLink_iff hl.1).mp hl) f₁ f₂ f hf₁ ih hconcat

private theorem homotopic_to_parameterization {S : Type u}
    [TopologicalSpace S] [T2Space S] {U : Set S} {s t : S} {f g : Curve S}
    (hf : ParametrizesSet f U s t) (hg : range g ⊆ U)
    (hg0 : g 0 = s) (hg1 : g 1 = t) : CurvesHomotopic g f := by
  obtain ⟨H, _, hrest⟩ := curvesHomotopicIn_of_range_subset_parametrizesSet hf hg hg0 hg1
  exact ⟨H, fun _ => mem_univ _, hrest⟩

/-- The path-existence step in Graph Minors VI (4.1), page 124:
a forest subgraph homotopic to `H` supplies a path in `G` homotopic to any
specified path of `H` between distinct boundary vertices. -/
theorem exists_homotopic_subpath_of_hasHomotopicForestSubgraph
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {G H Hst : Drawing S} {s t : S}
    (hfeas : HasHomotopicForestSubgraph G H)
    (hs : s ∈ H.V ∩ bd S) (ht : t ∈ H.V ∩ bd S) (hne : s ≠ t)
    (hHst : IsSubpathOf H Hst s t) :
    ∃ P : Drawing S, IsSubpathOf G P s t ∧ PathsHomotopic P Hst s t := by
  obtain ⟨F, hFG, _, hFH⟩ := hfeas
  obtain ⟨WH, hWH, _, _⟩ := hHst.2.2.1
  obtain ⟨fH, hfH⟩ := hHst.2.2.2
  obtain ⟨gH, hgH⟩ := GM07.exists_curveTracesWalk WH
  let WH' := WH.mono (subdrawing_graph_le hHst.1)
  have hWH' : WH'.IsSimple := by
    simpa only [WH', GraphWalk.IsSimple, GraphWalk.support_mono] using hWH
  have hgH' : CurveTracesWalk H gH WH' := traces_mono hHst.1 hgH
  have hbd := hFH.2.2.2.2.1
  have hsF : s ∈ F.V ∩ bd S := hbd.symm ▸ hs
  have htF : t ∈ F.V ∩ bd S := hbd.symm ▸ ht
  obtain ⟨hiff, hhom⟩ := hFH.2.2.2.2.2 s hsF t htF hne
  obtain ⟨WF, hWF⟩ := hiff.mpr ⟨WH', hWH'⟩
  let P := walkDrawing F WF
  have hPF : P.IsSubdrawing F := walkDrawing_isSubdrawing F WF
  have hpath : IsPathDrawing P s t := isPathDrawing_walkDrawing_of_isSimple F hWF hne
  obtain ⟨WP, hWP, _, _⟩ := hpath.1
  obtain ⟨fP, hfP⟩ := hpath.2
  obtain ⟨gP, hgP⟩ := GM07.exists_curveTracesWalk WP
  let WP' := WP.mono (subdrawing_graph_le hPF)
  have hWP' : WP'.IsSimple := by
    simpa only [WP', GraphWalk.IsSimple, GraphWalk.support_mono] using hWP
  have hgP' : CurveTracesWalk F gP WP' := traces_mono hPF hgP
  have hPgP : CurvesHomotopic gP fP :=
    homotopic_to_parameterization hfP hgP.range_subset_U hgP.endpoints.1 hgP.endpoints.2
  have hHgH : CurvesHomotopic gH fH :=
    homotopic_to_parameterization hfH hgH.range_subset_U hgH.endpoints.1 hgH.endpoints.2
  have hPH : CurvesHomotopic fP fH :=
    GM07.CurvesHomotopic.trans (GM07.CurvesHomotopic.symm hPgP)
      (GM07.CurvesHomotopic.trans (hhom WP' WH' gP gH hWP' hWH' hgP' hgH') hHgH)
  have hPG := hPF.trans hFG
  exact ⟨P, ⟨hPG, hPG.U_subset, hpath⟩, fP, fH, hfP, hfH, hPH⟩

/-- Paths of homotopic forests between the same distinct boundary vertices are
homotopic as path drawings. This is the path comparison in Graph Minors VI
(4.1)(iii), page 124. -/
theorem pathsHomotopic_of_subpaths_of_forestsHomotopic
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {F H R T : Drawing S} {s t : S}
    (hFH : ForestsHomotopic F H) (hs : s ∈ F.V ∩ bd S) (ht : t ∈ F.V ∩ bd S)
    (hne : s ≠ t) (hR : IsSubpathOf F R s t) (hT : IsSubpathOf H T s t) :
    PathsHomotopic R T s t := by
  obtain ⟨WR, hWR, _, _⟩ := hR.2.2.1
  obtain ⟨WT, hWT, _, _⟩ := hT.2.2.1
  obtain ⟨fR, hfR⟩ := hR.2.2.2
  obtain ⟨fT, hfT⟩ := hT.2.2.2
  obtain ⟨gR, hgR⟩ := GM07.exists_curveTracesWalk WR
  obtain ⟨gT, hgT⟩ := GM07.exists_curveTracesWalk WT
  let WR' := WR.mono (subdrawing_graph_le hR.1)
  let WT' := WT.mono (subdrawing_graph_le hT.1)
  have hWR' : WR'.IsSimple := by
    simpa only [WR', GraphWalk.IsSimple, GraphWalk.support_mono] using hWR
  have hWT' : WT'.IsSimple := by
    simpa only [WT', GraphWalk.IsSimple, GraphWalk.support_mono] using hWT
  have htraceR : CurveTracesWalk F gR WR' := traces_mono hR.1 hgR
  have htraceT : CurveTracesWalk H gT WT' := traces_mono hT.1 hgT
  have hgRf : CurvesHomotopic gR fR :=
    homotopic_to_parameterization hfR hgR.range_subset_U hgR.endpoints.1 hgR.endpoints.2
  have hgTf : CurvesHomotopic gT fT :=
    homotopic_to_parameterization hfT hgT.range_subset_U hgT.endpoints.1 hgT.endpoints.2
  have hgRT := (hFH.2.2.2.2.2 s hs t ht hne).2 WR' WT' gR gT hWR' hWT' htraceR htraceT
  exact ⟨fR, fT, hfR, hfT,
    GM07.CurvesHomotopic.trans (GM07.CurvesHomotopic.symm hgRf)
      (GM07.CurvesHomotopic.trans hgRT hgTf)⟩

/-- Homotopic path drawings have the same homotopy classes relative to a cuff arc.
This removes the choice of path parameterization in Graph Minors VI, Section 4,
page 124. -/
theorem pathHomotopicToArc_of_pathsHomotopic
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {P Q : Drawing S} {s t : S} {A : Set S}
    (hPQ : PathsHomotopic P Q s t) (hQA : PathHomotopicToArc Q s t A) :
    PathHomotopicToArc P s t A := by
  obtain ⟨fP, fQ, hfP, hfQ, hPQ⟩ := hPQ
  obtain ⟨gQ, fA, hgQ, hfA, hQA⟩ := hQA
  have hQQ : CurvesHomotopic fQ gQ :=
    homotopic_to_parameterization hgQ (by rw [hfQ.2.1]) hfQ.2.2.1 hfQ.2.2.2
  exact ⟨fP, fA, hfP, hfA,
    GM07.CurvesHomotopic.trans hPQ (GM07.CurvesHomotopic.trans hQQ hQA)⟩

/-- Before choosing the minimal path in Graph Minors VI (4.1)(i), page 124,
feasibility supplies a path of `G` homotopic to the specified cuff arc. -/
theorem exists_subpath_homotopicToArc_of_hasHomotopicForestSubgraph
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {G H Hst : Drawing S} {s t : S} {A : Set S}
    (hfeas : HasHomotopicForestSubgraph G H)
    (hs : s ∈ H.V ∩ bd S) (ht : t ∈ H.V ∩ bd S) (hne : s ≠ t)
    (hHst : IsSubpathOf H Hst s t) (hHA : PathHomotopicToArc Hst s t A) :
    ∃ P : Drawing S, IsSubpathOf G P s t ∧ PathHomotopicToArc P s t A := by
  obtain ⟨P, hP, hPH⟩ :=
    exists_homotopic_subpath_of_hasHomotopicForestSubgraph hfeas hs ht hne hHst
  exact ⟨P, hP, pathHomotopicToArc_of_pathsHomotopic hPH hHA⟩

end GraphMinor.GM06
