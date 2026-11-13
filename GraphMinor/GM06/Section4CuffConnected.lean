module

public import GraphMinor.GM06.Section4Comparison
import GraphMinor.GM06.Section4
import GraphMinor.Surface.Cylinder
import GraphMinor.GM06.Section4ComparisonPaths
import GraphMinor.GM06.Section4CuffSegments
import GraphMinor.GM06.Section4Consecutive
import GraphMinor.GM06.Section4Subarc
import GraphMinor.GM06.Section4OpenSubarc
import GraphMinor.GM06.Section3Basic

/-!
# Each cuff base is joined in G′

For the final argument of VI (4.2), page 126, parameterize a cuff base
and order its finitely many forest vertices. Consecutive vertices bound
a whole-boundary segment. Its minimal path lies in G′. Chaining these
paths joins any two vertices of the base in G′.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

/-- The vertices on either cuff of an interval-based component are
joined in G′, as asserted in the proof of VI (4.2), page 126. -/
theorem exists_comparison_walk_of_cuffBase
    {G H : Drawing ClosedCylinder} (hforest : IsGraphForest H.toGraph)
    (hbd : H.V ∩ bd ClosedCylinder = G.V ∩ bd ClosedCylinder)
    (hno41 : ¬ Section4Condition41Applies G H) (hno2 : ¬ Section4Reduction2Applies G H)
    {K : Graph ClosedCylinder (Set ClosedCylinder)} {C A : Set ClosedCylinder}
    (hbase : IsCuffBase H K C A) {a b : ClosedCylinder}
    (ha : a ∈ Graph.vertexSet K ∩ C) (hb : b ∈ Graph.vertexSet K ∩ C) :
    Nonempty (GraphWalk (componentComparisonDrawing G H K).toGraph a b) := by
  classical
  obtain ⟨hC, hK, ⟨s, hs, t, ht, hst, hA⟩, hbaseEq, hpaths⟩ := hbase
  have hcases : C = cylinderCuff1 ∨ C = cylinderCuff2 := by
    rw [cuffs_closedCylinder] at hC
    exact hC
  have hCO : IsOArc C := hcases.elim
    (fun h => h ▸ isOArc_cylinderCuff1) (fun h => h ▸ isOArc_cylinderCuff2)
  have hAC : A ⊆ C := by
    obtain ⟨x, _, rfl⟩ := hA
    exact (connectedComponentIn_subset _ x).trans sdiff_subset
  have hCBD : C ⊆ bd ClosedCylinder := by
    obtain ⟨x, _, rfl⟩ := hC
    exact connectedComponentIn_subset _ x
  have hline := isLineWithEnds_closure_component_of_oArc hCO hs.1 ht.1 hst hA
  obtain ⟨f, hf⟩ := exists_parametrizesSet_of_isLineWithEnds hline
  have hpre := preimage_component_of_parametrizes_closure hA f hf
  let W : Set unitInterval := f ⁻¹' (H.V ∩ A)
  have hW : W.Finite := Set.Finite.preimage hf.1.injOn (H.finite_V.inter_of_left A)
  have hWV : Graph.vertexSet K ∩ bd ClosedCylinder ⊆ G.V := by
    intro v hv
    exact (hbd ▸ (show v ∈ H.V ∩ bd ClosedCylinder from ⟨hK.1.vertexSet_mono hv.1, hv.2⟩)).1
  have hGV := componentComparisonDrawing_V G H K hWV
  let R : unitInterval → unitInterval → Prop := fun p q =>
    p = q ∨ Nonempty (GraphWalk (componentComparisonDrawing G H K).toGraph (f p) (f q))
  have hR : Equivalence R := by
    refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
    · intro p q hpq
      change p = q ∨ Nonempty (GraphWalk _ (f p) (f q)) at hpq
      rcases hpq with he | hw
      · exact Or.inl he.symm
      · obtain ⟨P⟩ := hw
        exact Or.inr ⟨P.reverse⟩
    · intro p q r hpq hqr
      change p = q ∨ Nonempty (GraphWalk _ (f p) (f q)) at hpq
      change q = r ∨ Nonempty (GraphWalk _ (f q) (f r)) at hqr
      rcases hpq with he | hw
      · subst q
        exact hqr
      · rcases hqr with he | hw'
        · subst r
          exact Or.inr hw
        · obtain ⟨P⟩ := hw
          obtain ⟨Q⟩ := hw'
          exact Or.inr ⟨P.append Q⟩
  have hnext : ∀ p ∈ W, ∀ q ∈ W, p < q →
      (∀ r ∈ W, ¬ (p < r ∧ r < q)) → R p q := by
    intro p hp q hq hpq hgap
    have hpA : f p ∈ A := hp.2
    have hqA : f q ∈ A := hq.2
    have hne : f p ≠ f q := fun he => hpq.ne (hf.1 he)
    let B := cuffSubArc C A (f p) (f q)
    have hB : B ∈ componentsIn (C \ {f p, f q}) :=
      cuffSubArc_mem_componentsIn_of_interval hCO hA hline hpA hqA hne
    obtain ⟨k, hk, _⟩ := exists_parametrizesSet_cuffSubArc hCO hA hline hpA hqA hne
    have hBim : B = f '' Ioo p q :=
      cuffSubArc_eq_image_Ioo_of_parametrizes_closure hCO hA f hf
        (hpre ▸ hpA) (hpre ▸ hqA) hpq
    have hdis : Disjoint B (H.V ∩ bd ClosedCylinder) := by
      apply Set.disjoint_left.mpr
      intro z hz hzH
      rw [hBim] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      have hp0 : 0 < p := (show p ∈ Ioo 0 1 from hpre ▸ hpA).1
      have hq1 : q < 1 := (show q ∈ Ioo 0 1 from hpre ▸ hqA).2
      have hrA : f r ∈ A := by
        change r ∈ f ⁻¹' A
        rw [hpre]
        exact ⟨hp0.trans hr.1, hr.2.trans hq1⟩
      exact hgap r ⟨hzH.1, hrA⟩ hr
    have hpbd : f p ∈ H.V ∩ bd ClosedCylinder := ⟨hp.1, hCBD (hAC hpA)⟩
    have hqbd : f q ∈ H.V ∩ bd ClosedCylinder := ⟨hq.1, hCBD (hAC hqA)⟩
    have hseg : B ∈ segmentsOf (bd ClosedCylinder) (H.V ∩ bd ClosedCylinder) :=
      isSegmentOf_boundary_of_cuff_component hC hB hpbd hqbd hdis k hk
    obtain ⟨Hpq, hHpq, hHarc⟩ := hpaths (f p) hp (f q) hq hne
    have hpK : f p ∈ Graph.vertexSet K :=
      (hbaseEq.symm ▸ (show f p ∈ H.V ∩ A from hp)).1
    have hpcl : f p ∈ closure B := hk.2.2.1 ▸ (hk.2.1 ▸ mem_range_self 0)
    have hqcl : f q ∈ closure B := hk.2.2.2 ▸ (hk.2.1 ▸ mem_range_self 1)
    exact Or.inr (exists_comparison_walk_of_segment hforest hno41 hno2 hbd hK hpK
      hseg hpbd hqbd hne hpcl hqcl hHpq hHarc)
  have haA : a ∈ H.V ∩ A := hbaseEq ▸ ha
  have hbA : b ∈ H.V ∩ A := hbaseEq ▸ hb
  obtain ⟨p, hp⟩ := hf.2.1.symm ▸ (subset_closure haA.2)
  obtain ⟨q, hq⟩ := hf.2.1.symm ▸ (subset_closure hbA.2)
  have hpW : p ∈ W := by change f p ∈ H.V ∩ A; rw [hp]; exact haA
  have hqW : q ∈ W := by change f q ∈ H.V ∩ A; rw [hq]; exact hbA
  rcases relation_of_consecutive_finite hW hR hnext p hpW q hqW with hpq | hwalk
  · have hab : a = b := hp.symm.trans ((congrArg f hpq).trans hq)
    rw [← hab]
    have haV : a ∈ (componentComparisonDrawing G H K).V := by
      rw [hGV]
      exact ⟨ha.1, hCBD ha.2⟩
    exact ⟨.nil haV⟩
  · simpa only [hp, hq] using hwalk

end GraphMinor.GM06
