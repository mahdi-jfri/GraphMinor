module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section4Segment
import GraphMinor.GM06.Section4Subarc
import GraphMinor.GM06.Section4CuffCurve
import GraphMinor.GM06.Section4OpenSubarc
import GraphMinor.Surface.DiscGrow
import GraphMinor.GM11.Walks

/-!
# Graph Minors VI (4.2), claim (1)

A path in the forest is homotopic to a cuff arc. Every other forest path
with both ends on its closure is homotopic to the subarc between those
ends. The lifted crossing argument rules out an extra turn. The two-arc
decomposition of the cuff identifies the subarc with `cuffSubArc`.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

/-- Graph Minors VI (4.2), claim (1), page 125: a forest path with ends on
the closure of a cuff arc homotopic to another forest path is homotopic
to the subarc between its ends. The base includes the original ends, as
in the paper's set `S ∪ {a, b}`. -/
theorem lemma_4_2_claim_1
    {H P Q : Drawing ClosedCylinder} (hH : IsGraphForest H.toGraph)
    {C A : Set ClosedCylinder} (hC : C ∈ cuffs ClosedCylinder)
    {a b c d : ClosedCylinder} (hab : a ≠ b)
    (hA : A ∈ componentsIn (C \ {a, b}))
    (hP : IsSubpathOf H P a b) (hPA : PathHomotopicToArc P a b A)
    (hQ : IsSubpathOf H Q c d)
    (hc : c ∈ A ∪ {a, b}) (hd : d ∈ A ∪ {a, b}) (hcd : c ≠ d) :
    PathHomotopicToArc Q c d (cuffSubArc C (A ∪ {a, b}) c d) := by
  have hCcases : C = cylinderCuff1 ∨ C = cylinderCuff2 := by
    rw [cuffs_closedCylinder] at hC
    exact hC
  have hCO : IsOArc C := hCcases.elim
    (fun h => h ▸ isOArc_cylinderCuff1) (fun h => h ▸ isOArc_cylinderCuff2)
  have hCC : IsClosed C := hCO.isCompact.isClosed
  have hAsub : A ⊆ C := by
    obtain ⟨x, _, rfl⟩ := hA
    exact (connectedComponentIn_subset _ x).trans sdiff_subset
  have hAcl : closure A ⊆ C := closure_minimal hAsub hCC
  have hAconn : IsPreconnected A := by
    obtain ⟨x, _, rfl⟩ := hA
    exact isPreconnected_connectedComponentIn
  obtain ⟨f, k, hf, hk, hfk⟩ := hPA
  have hbase : closure A = A ∪ {a, b} := by
    apply Subset.antisymm
    · simpa only [hk.2.2.1, hk.2.2.2] using
        closure_arc_subset_of_isPreconnected hAconn k hk.1 hk.2.1
    · refine union_subset subset_closure ?_
      rintro x (rfl | rfl)
      · rw [← hk.2.1, ← hk.2.2.1]; exact mem_range_self 0
      · rw [← hk.2.1, ← hk.2.2.2]; exact mem_range_self 1
  obtain ⟨s, hs⟩ := (show c ∈ range k by rw [hk.2.1, hbase]; exact hc)
  obtain ⟨t, ht⟩ := (show d ∈ range k by rw [hk.2.1, hbase]; exact hd)
  have hst : s ≠ t := fun he => hcd (hs.symm.trans ((congrArg k he).trans ht))
  obtain ⟨g, hg⟩ := hQ.2.2.2
  have hki : Function.Injective (GM07.subPathSeg k s t) := by
    intro x y hxy
    have he := congrArg Subtype.val (hk.1 hxy)
    dsimp [GM07.subPathSeg] at he
    apply Subtype.ext
    have hn : (t : ℝ) - (s : ℝ) ≠ 0 := sub_ne_zero.mpr
      (Ne.symm (Subtype.val_injective.ne hst))
    have hmul : ((x : ℝ) - (y : ℝ)) * ((t : ℝ) - (s : ℝ)) = 0 := by
      nlinarith only [he]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hn)
  have hL : IsLineWithEnds (range (GM07.subPathSeg k s t)) c d := by
    simpa only [GM07.subPathSeg_zero, GM07.subPathSeg_one, hs, ht] using
      (IsArcMap.isLineWithEnds (a := GM07.subPathSeg k s t)
        ⟨(GM07.subPathSeg k s t).continuous, hki⟩)
  have hK : IsLine (closure A) := by
    obtain ⟨e, _, _⟩ := IsArcMap.isLineWithEnds ⟨k.continuous, hk.1⟩
    exact ⟨hk.2.1 ▸ e⟩
  have hclosure : closure (cuffSubArc C (A ∪ {a, b}) c d) =
      range (GM07.subPathSeg k s t) := by
    rw [← hbase]
    exact closure_cuffSubArc_eq_of_line hCO hK hAcl hL
      (by rw [← hk.2.1]; exact GM07.range_subPathSeg_subset k s t)
  refine ⟨g, GM07.subPathSeg k s t, hg, ?_, ?_⟩
  · exact ⟨hki, hclosure.symm, by simpa only [GM07.subPathSeg_zero] using hs,
      by simpa only [GM07.subPathSeg_one] using ht⟩
  · obtain ⟨outer, houter⟩ : ∃ outer : Bool,
        C = if outer then cylinderCuff2 else cylinderCuff1 := by
      rcases hCcases with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    have hkr : ∀ v, (k v).1.1 = (if outer then 2 else 1) := by
      intro v
      have hv := hAcl (hk.2.1 ▸ mem_range_self (f := k) v)
      rw [houter] at hv
      cases outer <;> exact hv
    exact forest_curve_homotopic_to_cuff_subcurve hH outer
      (by rw [hf.2.1]; exact hP.2.1)
      (by rw [hg.2.1]; exact hQ.2.1) hk.1 hkr hfk
      (hg.2.2.1.trans hs.symm) (hg.2.2.2.trans ht.symm)

/-- The interior-endpoint form of Graph Minors VI (4.2), claim (1).
When both ends lie in the open arc, adjoining its original ends to the
base does not change their subarc. This is the form used in claim (2). -/
theorem lemma_4_2_claim_1_of_mem_arc
    {H P Q : Drawing ClosedCylinder} (hH : IsGraphForest H.toGraph)
    {C A : Set ClosedCylinder} (hC : C ∈ cuffs ClosedCylinder)
    {a b c d : ClosedCylinder} (hab : a ≠ b)
    (hA : A ∈ componentsIn (C \ {a, b}))
    (hP : IsSubpathOf H P a b) (hPA : PathHomotopicToArc P a b A)
    (hQ : IsSubpathOf H Q c d) (hc : c ∈ A) (hd : d ∈ A) (hcd : c ≠ d) :
    PathHomotopicToArc Q c d (cuffSubArc C A c d) := by
  have hCO : IsOArc C := by
    rw [cuffs_closedCylinder] at hC
    rcases hC with rfl | rfl
    · exact isOArc_cylinderCuff1
    · exact isOArc_cylinderCuff2
  have hline : IsLineWithEnds (closure A) a b := by
    obtain ⟨f, k, hf, hk, hhom⟩ := hPA
    simpa only [hk.2.1, hk.2.2.1, hk.2.2.2] using
      IsArcMap.isLineWithEnds ⟨k.continuous, hk.1⟩
  have hbase := closure_component_eq_union_pair hA hline
  have hcl := closure_cuffSubArc_closure_base_eq hCO hA hline hc hd hcd
  have hhom := lemma_4_2_claim_1 hH hC hab hA hP hPA hQ (Or.inl hc) (Or.inl hd) hcd
  simpa only [PathHomotopicToArc, ← hbase, hcl] using hhom

end GraphMinor.GM06
