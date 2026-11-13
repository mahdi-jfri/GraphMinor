module

public import GraphMinor.Surface.Defs
public import GraphMinor.Surface.DomainPair
import GraphMinor.Surface.DiscUnion
import GraphMinor.Surface.PlaneOrientation
import GraphMinor.Surface.ArcTools
import GraphMinor.Surface.SurfaceGraph
import GraphMinor.Surface.EdgeLoop

/-!
# Complementary boundary arcs for contour substitution

Part IV, Section 7b of the planarity note replaces an attachment interval
by a child's boundary detour. A line in a circle has one complementary
closed boundary arc with the same ends. The two open arcs are separated
after their ends are removed, so any connected open line interior lies
on one of them. This identifies the original line and its complement.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface Topology

/-- A connected set avoiding the intersection of two closed covering pieces
lies wholly in one piece. -/
theorem preconnected_subset_or_subset_of_closed_cover {K A B : Set ℂ}
    (hK : IsPreconnected K) (hA : IsClosed A) (hB : IsClosed B)
    (hcover : K ⊆ A ∪ B) (havoid : Disjoint K (A ∩ B)) : K ⊆ A ∨ K ⊆ B := by
  classical
  by_cases hKA : K ⊆ A
  · exact Or.inl hKA
  by_cases hKB : K ⊆ B
  · exact Or.inr hKB
  obtain ⟨x,hxK,hxA⟩ := not_subset.mp hKA
  obtain ⟨y,hyK,hyB⟩ := not_subset.mp hKB
  have hopen : K ⊆ Aᶜ ∪ Bᶜ := by
    intro z hz
    by_cases hzA : z ∈ A
    · exact Or.inr (fun hzB => disjoint_left.mp havoid hz ⟨hzA,hzB⟩)
    · exact Or.inl hzA
  obtain ⟨z,hzK,hzA,hzB⟩ := hK Aᶜ Bᶜ hA.isOpen_compl hB.isOpen_compl hopen
    ⟨x,hxK,hxA⟩ ⟨y,hyK,hyB⟩
  exact ((hcover hzK).elim hzA hzB).elim

private theorem line_open_interior_preconnected {L : Set ℂ} {a b : ℂ}
    (hL : IsLineWithEnds L a b) : IsPreconnected (L \ {a,b}) := by
  obtain ⟨f,hf,hrange,hzero,hone⟩ := hL.exists_arc
  have heq : L \ {a,b} = f '' Ioo (0 : unitInterval) 1 := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨t,rfl⟩ := hrange.symm ▸ hx.1
      have ht0 : (0 : unitInterval) < t := lt_of_le_of_ne bot_le (fun he =>
        hx.2 (Or.inl ((congrArg f he.symm).trans hzero)))
      have ht1 : t < (1 : unitInterval) := lt_of_le_of_ne le_top (fun he =>
        hx.2 (Or.inr ((congrArg f he).trans hone)))
      exact ⟨t,⟨ht0,ht1⟩,rfl⟩
    · rintro x ⟨t,ht,rfl⟩
      refine ⟨hrange ▸ mem_range_self t, ?_⟩
      rintro (he | he)
      · exact ht.1.ne' (hf.2 (he.trans hzero.symm))
      · exact ht.2.ne (hf.2 (he.trans hone.symm))
  rw [heq]
  exact isPreconnected_Ioo.image f hf.1.continuousOn

/-- Part IV, Section 7b: an attachment interval on a boundary circle has
one complementary closed boundary arc with the same ends. -/
theorem exists_complementary_boundary_arc {C L : Set ℂ} {a b : ℂ}
    (hC : IsOArc C) (hL : IsLineWithEnds L a b) (hsub : L ⊆ C) :
    ∃ R : Set ℂ, IsLineWithEnds R a b ∧ L ∪ R = C ∧ L ∩ R = {a,b} := by
  obtain ⟨k,hk,hkrange,hk0,hk1⟩ := hL.exists_arc
  have hab : a ≠ b := by
    intro he
    exact zero_ne_one (hk.2 (hk0.trans (he.trans hk1.symm)))
  obtain ⟨f,g,hfg,hf0,hf1,hfgC⟩ := hC.exists_arcs (hsub hL.left_mem) (hsub hL.right_mem) hab
  have hg0 : g 0 = a := hfg.zero.trans hf0
  have hg1 : g 1 = b := hfg.one.trans hf1
  have hfline : IsLineWithEnds (range f) a b := by
    simpa only [hf0,hf1] using hfg.arc_left.isLineWithEnds
  have hgline : IsLineWithEnds (range g) a b := by
    simpa only [hg0,hg1] using hfg.arc_right.isLineWithEnds
  have hmeet : range f ∩ range g = {a,b} := by
    simpa only [hf0,hf1] using hfg.inter
  have hpc : IsPreconnected L := by
    rw [← hkrange]
    exact isPreconnected_range hk.1
  have hchoices : L \ {a,b} ⊆ range f ∨ L \ {a,b} ⊆ range g := by
    apply preconnected_subset_or_subset_of_closed_cover (line_open_interior_preconnected hL)
      hfline.isCompact.isClosed hgline.isCompact.isClosed
    · intro x hx
      exact hfgC.symm ▸ hsub hx.1
    · rw [hmeet]
      exact disjoint_sdiff_left
  have hadd : ∀ J : Set ℂ, a ∈ J → b ∈ J → L \ {a,b} ⊆ J → L ⊆ J := by
    intro J ha hb hJ x hx
    by_cases he : x ∈ ({a,b} : Set ℂ)
    · exact he.elim (fun h => h.symm ▸ ha) (fun h => h.symm ▸ hb)
    · exact hJ ⟨hx,he⟩
  rcases hchoices with hf | hg
  · have heq : L = range f := hfline.eq_of_subset hpc
      (hadd _ hfline.left_mem hfline.right_mem hf) hL.left_mem hL.right_mem
    exact ⟨range g,hgline,heq.symm ▸ hfgC,heq.symm ▸ hmeet⟩
  · have heq : L = range g := hgline.eq_of_subset hpc
      (hadd _ hgline.left_mem hgline.right_mem hg) hL.left_mem hL.right_mem
    refine ⟨range f,hfline,?_,?_⟩
    · rw [heq,union_comm]
      exact hfgC
    · rw [heq,inter_comm]
      exact hmeet

private theorem arc_meeting_at_ends {c d : unitInterval → ℂ} {a b : ℂ}
    (hc : IsArcMap c) (hd : IsArcMap d) (hc0 : c 0 = a) (hc1 : c 1 = b)
    (hd0 : d 0 = a) (hd1 : d 1 = b) (hinter : range c ∩ range d = {a,b}) :
    ∀ s t, c s = d t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
  intro s t he
  have hm : c s ∈ range c ∩ range d := ⟨mem_range_self s,⟨t,he.symm⟩⟩
  rw [hinter] at hm
  rcases hm with ha | hb
  · exact Or.inl ⟨hc.2 (ha.trans hc0.symm),hd.2 (he.symm.trans (ha.trans hd0.symm))⟩
  · exact Or.inr ⟨hc.2 (hb.trans hc1.symm),hd.2 (he.symm.trans (hb.trans hd1.symm))⟩

/-- Part IV, Section 7b: replacing one boundary interval by another line
with the same ends admits a boundary match fixing the complementary arc
pointwise and carrying the old interval onto the new detour. -/
theorem boundary_interval_replacement_match {L M R : Set ℂ} {a b : ℂ}
    (hL : IsLineWithEnds L a b) (hM : IsLineWithEnds M a b)
    (hR : IsLineWithEnds R a b) (hLR : L ∩ R = {a,b}) (hMR : M ∩ R = {a,b}) :
    ∃ h k : ℂ → ℂ, BdMatch (L ∪ R) (M ∪ R) h k ∧
      (∀ x ∈ R, h x = x) ∧ h '' L = M := by
  obtain ⟨c,hc,hcL,hc0,hc1⟩ := hL.exists_arc
  obtain ⟨c',hc',hcM,hc'0,hc'1⟩ := hM.exists_arc
  obtain ⟨d,hd,hdR,hd0,hd1⟩ := hR.exists_arc
  have hold : range c ∩ range d = {a,b} := by rw [hcL,hdR]; exact hLR
  have hnew : range c' ∩ range d = {a,b} := by rw [hcM,hdR]; exact hMR
  obtain ⟨h,k,hmatch,hcmap,hdmap⟩ := exists_bdMatch_of_arcs hc hd hc' hd
    (hd0.trans hc0.symm) (hd1.trans hc1.symm) (hd0.trans hc'0.symm) (hd1.trans hc'1.symm)
    (arc_meeting_at_ends hc hd hc0 hc1 hd0 hd1 hold)
    (arc_meeting_at_ends hc' hd hc'0 hc'1 hd0 hd1 hnew)
  rw [hcL,hdR,hcM] at hmatch
  refine ⟨h,k,hmatch,?_,?_⟩
  · intro x hx
    obtain ⟨t,rfl⟩ := hdR.symm ▸ hx
    exact hdmap t
  · rw [← hcL,← hcM]
    ext x
    constructor
    · rintro ⟨y,⟨t,rfl⟩,rfl⟩
      exact ⟨t,(hcmap t).symm⟩
    · rintro ⟨t,rfl⟩
      exact ⟨c t,⟨t,rfl⟩,hcmap t⟩

/-- Part IV, Section 7b: one leaf attachment replaces precisely its old
boundary interval by a complementary child detour. The boundary match fixes
the rest of the old boundary pointwise. -/
theorem leaf_attachment_boundary_replacement {N R P L K : Set ℂ} {a b c d : ℂ}
    (hN : IsClosedDisc N) (hR : IsClosedDisc R) (hP : IsClosedDisc P)
    (hL : IsLineWithEnds L a b) (hK : IsLineWithEnds K c d)
    (hNR : N ∩ R = L) (hRP : R ∩ P = K) (hNP : Disjoint N P)
    (hLN : L ⊆ discBd N) (hLR : L ⊆ discBd R)
    (hKR : K ⊆ discBd R) (hKP : K ⊆ discBd P) :
    IsClosedDisc (N ∪ R ∪ P) ∧ ∃ J M : Set ℂ,
      IsLineWithEnds J a b ∧ IsLineWithEnds M a b ∧
      L ∪ J = discBd N ∧ L ∩ J = {a,b} ∧
      J ∪ M = discBd (N ∪ R ∪ P) ∧ J ∩ M = {a,b} ∧
      ∃ h k : ℂ → ℂ, BdMatch (discBd N) (discBd (N ∪ R ∪ P)) h k ∧
        (∀ x ∈ J, h x = x) ∧ h '' L = M := by
  obtain ⟨hchild,hchildbd⟩ := disc_union R P K c d hR hP hK hRP hKR hKP
  have hLchild : L ⊆ discBd (R ∪ P) := by
    rw [hchildbd]
    intro x hx
    refine ⟨Or.inl (hLR hx), ?_⟩
    intro hcut
    have hxN : x ∈ N ∩ R := hNR.symm ▸ hx
    have hxP : x ∈ R ∩ P := hRP.symm ▸ hcut.1
    exact disjoint_left.mp hNP hxN.1 hxP.2
  have hNchild : N ∩ (R ∪ P) = L := by
    rw [inter_union_distrib_left,hNR,hNP.inter_eq,union_empty]
  obtain ⟨hfinal,hfinalbd⟩ := disc_union N (R ∪ P) L a b hN hchild hL hNchild hLN hLchild
  rw [← union_assoc] at hfinal hfinalbd
  obtain ⟨J,hJ,hOld,hOldinter⟩ := exists_complementary_boundary_arc hN.isOArc_discBd hL hLN
  obtain ⟨M,hM,hNew,hNewinter⟩ := exists_complementary_boundary_arc hchild.isOArc_discBd hL hLchild
  have hMJ : M ∩ J = {a,b} := by
    apply Subset.antisymm
    · intro x hx
      have hxC : x ∈ N ∩ (R ∪ P) :=
        ⟨discBd_subset N (hOld ▸ Or.inr hx.2),discBd_subset (R ∪ P) (hNew ▸ Or.inr hx.1)⟩
      have hxL : x ∈ L := hNchild ▸ hxC
      have hm : x ∈ L ∩ M := ⟨hxL,hx.1⟩
      exact hNewinter ▸ hm
    · intro x hx
      rcases hx with he | he
      · subst x
        exact ⟨hM.left_mem,hJ.left_mem⟩
      · subst x
        exact ⟨hM.right_mem,hJ.right_mem⟩
  have hset : ((L ∪ J) ∪ (L ∪ M)) \ (L \ {a,b}) = J ∪ M := by
    apply Subset.antisymm
    · intro x hx
      have hLcase : x ∈ L → x ∈ J ∪ M := by
        intro hxL
        have he : x ∈ ({a,b} : Set ℂ) := by
          by_contra hne
          exact hx.2 ⟨hxL,hne⟩
        have hm : x ∈ L ∩ J := hOldinter.symm ▸ he
        exact Or.inl hm.2
      rcases hx.1 with (hxL | hxJ) | (hxL | hxM)
      · exact hLcase hxL
      · exact Or.inl hxJ
      · exact hLcase hxL
      · exact Or.inr hxM
    · intro x hx
      rcases hx with hxJ | hxM
      · refine ⟨Or.inl (Or.inr hxJ), ?_⟩
        intro hcut
        have hm : x ∈ L ∩ J := ⟨hcut.1,hxJ⟩
        exact hcut.2 (hOldinter ▸ hm)
      · refine ⟨Or.inr (Or.inr hxM), ?_⟩
        intro hcut
        have hm : x ∈ L ∩ M := ⟨hcut.1,hxM⟩
        exact hcut.2 (hNewinter ▸ hm)
  rw [← hOld,← hNew,hset] at hfinalbd
  obtain ⟨h,k,hmatch,hfix,himage⟩ := boundary_interval_replacement_match hL hM hJ
    hOldinter hMJ
  have hnewcircle : M ∪ J = discBd (N ∪ R ∪ P) := by
    rw [union_comm]
    exact hfinalbd.symm
  rw [hOld,hnewcircle] at hmatch
  exact ⟨hfinal,J,M,hJ,hM,hOld,hOldinter,hfinalbd.symm,
    (inter_comm J M).trans hMJ,h,k,hmatch,hfix,himage⟩

end GraphMinor.LRPlanarity
