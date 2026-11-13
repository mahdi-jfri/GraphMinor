module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section4CuffComponents
import GraphMinor.GM06.Section4CuffSegments
import GraphMinor.GM06.Section4EdgeReduction
import GraphMinor.GM06.Section4Routed
import GraphMinor.GM06.Section4OpenSubarc
import GraphMinor.GM06.Section4Subarc
import GraphMinor.GM06.Section3Induce
import GraphMinor.GM07.PushForest
import GraphMinor.Surface.CutCyl
import GraphMinor.Surface.AddCrosscap

/-!
# Excluding an interval-based bad component

The end of VI (4.2), page 127, restricts G′ to a cuff with at least two
vertices. This is a connected component. Result (4.3) supplies an edge
with no vertex on its base subarc. That subarc is a boundary segment,
and the edge permits Reduction 2, giving the required contradiction.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

/-- The final contradiction in VI (4.2), page 127: an interval-based
bad component cannot survive the excluded obstructions and reductions. -/
theorem not_bad_of_intervalBasedOn_both_cuffs
    {G H : Drawing ClosedCylinder} (hG : G.IsProper) (hH : H.IsProper)
    (hforest : IsGraphForest H.toGraph)
    (hbd : H.V ∩ bd ClosedCylinder = G.V ∩ bd ClosedCylinder)
    (hno41 : ¬ Section4Condition41Applies G H)
    (hno1 : ¬ Section4Reduction1Applies G H) (hno2 : ¬ Section4Reduction2Applies G H)
    {K : Graph ClosedCylinder (Set ClosedCylinder)} (hK : IsGraphComponent K H.toGraph)
    (hbases : ∀ C ∈ cuffs ClosedCylinder, IsIntervalBasedOn H K C) :
    ¬ IsBadComponent K := by
  intro hbad
  obtain ⟨C, hC, hcard⟩ := hbad
  have hX : (Graph.vertexSet K ∩ C).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt (Nat.zero_lt_one.trans hcard))
  obtain ⟨L, hL, hLV⟩ := exists_comparison_component_on_cuff
    hG hH hforest hbd hno41 hno1 hno2 hK hbases hC hX
  let G' := componentComparisonDrawing G H K
  let F := induceDrawing G' (Graph.vertexSet L)
  have hFV : F.V = Graph.vertexSet K ∩ C := (induceDrawing_V G' hL.1.vertexSet_mono).trans hLV
  have hFgraph : F.toGraph = L := induceDrawing_toGraph_of_component G' hL
  have hFsub : F.IsSubdrawing G' := induceDrawing_isSubdrawing G' hL.1.vertexSet_mono
  have hFp : F.IsProper := induceDrawing_isProper G'
    (componentComparisonDrawing_isProper hG K) hL.1.vertexSet_mono
  have hFc : IsGraphConnected F.toGraph := hFgraph.symm ▸ hL.2.1
  obtain ⟨A, hbase⟩ := hbases C hC
  obtain ⟨_, _, ⟨s, hs, t, ht, hst, hA⟩, hbaseEq, hpaths⟩ := hbase
  have hFA : F.V ⊆ A := by rw [hFV, hbaseEq]; exact inter_subset_right
  have hFcard : 2 ≤ F.V.ncard := by rw [hFV]; exact hcard
  obtain ⟨e, he, a, ha, b, hb, hab, hlF, hgap⟩ :=
    theorem_4_3_proof C s t A F hC hs.1 ht.1 hst hA hFp hFc hFcard hFA
  have hlG' : G'.toGraph.IsLink e a b := (hFsub.isLink_iff he).mp hlF
  obtain ⟨haKbd, hbKbd, _, Huv, hHuv, f, g, hf, hg, hfg⟩ :=
    componentComparisonDrawing_edge_data G H K hlG'
  have haA : a ∈ H.V ∩ A := hbaseEq ▸ (hFV ▸ ha)
  have hbA : b ∈ H.V ∩ A := hbaseEq ▸ (hFV ▸ hb)
  obtain ⟨Hab, hHab, hHabA⟩ := hpaths a haA b hbA hab
  obtain ⟨g', hg'⟩ := hHab.2.2.2
  have hgg' : CurvesHomotopic g g' := GM07.IsFlat.curvesHomotopic
    (GM07.isFlat_forest hforest)
    (by rw [hg.2.1]; exact hHuv.2.1)
    (by rw [hg'.2.1]; exact hHab.2.1)
    (hg.2.2.1.trans hg'.2.2.1.symm) (hg.2.2.2.trans hg'.2.2.2.symm)
  have hHuvA : PathHomotopicToArc Huv a b (cuffSubArc C A a b) :=
    pathHomotopicToArc_of_pathsHomotopic ⟨g, g', hg, hg', hgg'⟩ hHabA
  have hcases : C = cylinderCuff1 ∨ C = cylinderCuff2 := by
    rw [cuffs_closedCylinder] at hC
    exact hC
  have hCO : IsOArc C := hcases.elim
    (fun h => h ▸ isOArc_cylinderCuff1) (fun h => h ▸ isOArc_cylinderCuff2)
  have hline := isLineWithEnds_closure_component_of_oArc hCO hs.1 ht.1 hst hA
  have hB := cuffSubArc_mem_componentsIn_of_interval hCO hA hline haA.2 hbA.2 hab
  obtain ⟨k, hk, hkA⟩ := exists_parametrizesSet_cuffSubArc hCO hA hline haA.2 hbA.2 hab
  have hdis : Disjoint (cuffSubArc C A a b) (H.V ∩ bd ClosedCylinder) := by
    apply disjoint_left.mpr
    intro x hx hxH
    have hxA : x ∈ A := hkA (by rw [hk.2.1]; exact subset_closure hx)
    have hxF : x ∈ F.V := by rw [hFV, hbaseEq]; exact ⟨hxH.1, hxA⟩
    exact disjoint_left.mp hgap hx hxF
  have hseg : cuffSubArc C A a b ∈ segmentsOf (bd ClosedCylinder) (H.V ∩ bd ClosedCylinder) :=
    isSegmentOf_boundary_of_cuff_component hC hB ⟨haA.1, haKbd.2⟩
      ⟨hbA.1, hbKbd.2⟩ hdis k hk
  have haCl : a ∈ closure (cuffSubArc C A a b) := by
    rw [← hk.2.1]
    exact ⟨0, hk.2.2.1⟩
  have hbCl : b ∈ closure (cuffSubArc C A a b) := by
    rw [← hk.2.1]
    exact ⟨1, hk.2.2.2⟩
  have hlG : G.toGraph.IsLink e a b :=
    ((componentComparisonDrawing_isSubdrawing G H K).isLink_iff hlG'.1).mp hlG'
  obtain ⟨m⟩ := nonempty_cyl_homeo
  have hS : IsSurface ClosedCylinder := isSurface_of_homeo m (isSurface_model 0 0 2).1
  exact hno2 (reduction2_of_edge_homotopic_to_segment hS hG hbd hseg
    ⟨haA.1, haKbd.2⟩ ⟨hbA.1, hbKbd.2⟩ hab haCl hbCl hHuv hHuvA hlG f g hf hg hfg)

end GraphMinor.GM06
