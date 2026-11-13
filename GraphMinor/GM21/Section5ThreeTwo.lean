module

public import GraphMinor.GM21.Section4Tangle
public import GraphMinor.GM12.Section3Theorem
public import GraphMinor.GM07.Bridge
public import GraphMinor.GM07.Section7
public import GraphMinor.GM07.CuffSlide
public import GraphMinor.GM07.Section35
import GraphMinor.GM12.Section3SeparatedDiscs
import GraphMinor.GM12.Section3TwoDiscs
import GraphMinor.GM12.Section3ThreeDiscsForest
import GraphMinor.GM12.Section3OneDisc
import GraphMinor.GM12.Section3OneDiscComplement
import GraphMinor.GM12.Section3SphereChordTransfer
import GraphMinor.GM12.Section3SphereChordBound
import GraphMinor.GM12.Section3SphereSideDisc
import GraphMinor.GM12.Section3SphereSeparatorCount
import GraphMinor.GM12.Section3SmallCircleConditions
import GraphMinor.GM12.Section3SelectedSmallDisc
import GraphMinor.GM12.Section3DiscRegion
import GraphMinor.GM12.Section3EmptyClasses
import GraphMinor.GM12.Section3CandidateExistence
import GraphMinor.GM12.Section2NormalNoncover
import GraphMinor.GM11.Theorem66
import GraphMinor.GM12.Section3DiscVIEmpty
import GraphMinor.GM12.Section3DiscCrossFree
import GraphMinor.GM12.Section3BoundaryEquality
import GraphMinor.GM12.Section3AmbientTransfer
import GraphMinor.GM12.Section3SubspaceArcs
import GraphMinor.GM12.Section3AmbientFeasibilityForest
import GraphMinor.GM12.Section3AuxiliaryDisc
import GraphMinor.GM12.Section3PuncturedForest
import GraphMinor.GM12.Section3EmptyBoundaryDisc
import GraphMinor.GM11.Section6
import GraphMinor.GM11.CitedResults
import GraphMinor.GM19.CutFragment
import GraphMinor.GM19.RadialExists
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

/-!
# Graph Minors XXI, Section 5: Cuff Regions and the XII (3.2) Variant for (5.1)

This file defines `capDrawing` and `IsCuffRegion` (Section 5, page 14 of the preprint),
establishes the uniqueness and closure properties of cuff regions, and proves the variant
`theorem_3_2_of_cuff_ins` of Graph Minors XII, (3.2) used at the end of the proof of (5.1)
(pages 16–17 of the preprint), where the freeness hypothesis on `V(Γ') ∩ C` is replaced by
Claim (4) of (5.1).
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Function Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM10
  GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM19

/-! ## 1. Capped drawings and cuff regions -/

/-- The drawing in the capped surface `Shat` obtained by embedding a drawing `Γ : Drawing S`
along `cap.emb : S → Shat` (Graph Minors XXI, Section 4, page 10 of the preprint). -/
def capDrawing {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) (Γ : Surface.Drawing S) :
    Surface.Drawing Shat :=
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have : T2Space Shat := cap.isSurface.2.1
  mapDrawingInjOn Γ cap.emb cap.isEmbedding.continuous.continuousOn cap.isEmbedding.injective.injOn

@[simp]
theorem capDrawing_U {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) (Γ : Surface.Drawing S) :
    (capDrawing hS cap Γ).U = cap.emb '' Γ.U := rfl

@[simp]
theorem capDrawing_V {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) (Γ : Surface.Drawing S) :
    (capDrawing hS cap Γ).V = cap.emb '' Γ.V := rfl

theorem capDrawing_E {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) (Γ : Surface.Drawing S) :
    (capDrawing hS cap Γ).E = (image cap.emb) '' Γ.E := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have : T2Space Shat := cap.isSurface.2.1
  exact mapDrawingInjOn_E Γ cap.emb
    cap.isEmbedding.continuous.continuousOn cap.isEmbedding.injective.injOn

/-- Graph Minors XXI, Section 5 (page 14 of the preprint):
"If $C$ is a cuff of $\Sigma$ and $\Gamma$ is a drawing in $\Sigma$, there is a unique region of
$\Gamma$ in $\hat{\Sigma}$ which includes $C \setminus V(\Gamma)$, and we call it the *cuff region
of $\Gamma$ in $\hat{\Sigma}$ corresponding to $C$*." -/
def IsCuffRegion {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) (Γ : Surface.Drawing S)
    (C : Set S) (r : Set Shat) : Prop :=
  C ∈ cuffs S ∧ r ∈ (capDrawing hS cap Γ).R ∧ cap.emb '' (C \ Γ.V) ⊆ r

/-- For a proper drawing `Γ` in `S`, a subset `X ⊆ bd S` meets `Γ.U` only in `Γ.V`. -/
theorem proper_drawing_inter_subset_bd {S : Type} [TopologicalSpace S]
    {Γ : Surface.Drawing S} (hprop : Γ.IsProper) {X : Set S} (hX : X ⊆ bd S) :
    Γ.U ∩ X = Γ.V ∩ X := by
  apply Subset.antisymm
  · rintro x ⟨hxU, hxX⟩
    exact ⟨hprop ⟨hX hxX, hxU⟩, hxX⟩
  · exact inter_subset_inter_left X Γ.V_subset_U

/-- For a proper drawing `Γ` in `S` and a cuff `C ∈ cuffs S`, the closed cuff disc
`Δ = closure (cap.cuffDisc C)` meets `(capDrawing hS cap Γ).U` precisely in
`(capDrawing hS cap Γ).V ∩ discBd Δ`. -/
theorem capDrawing_inter_closure_cuffDisc {S Shat : Type}
    [TopologicalSpace S] [TopologicalSpace Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) {Γ : Surface.Drawing S}
    (hprop : Γ.IsProper) {C : Set S} (hC : C ∈ cuffs S) :
    (capDrawing hS cap Γ).U ∩ closure (cap.cuffDisc C) =
      (capDrawing hS cap Γ).V ∩ discBd (closure (cap.cuffDisc C)) := by
  have : T2Space S := hS.2.1
  have : T2Space Shat := cap.isSurface.2.1
  have hC_bd : C ⊆ bd S := by
    rcases hC with ⟨x, hx, rfl⟩
    exact connectedComponentIn_subset (bd S) x
  rw [cap.cuffDisc_bd C hC, cap.closure_cuffDisc hS hC, capDrawing_U, capDrawing_V]
  have hdisj_disc : Disjoint (cap.emb '' Γ.U) (cap.cuffDisc C) := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, _, rfl⟩ hxD
    have : cap.emb x ∈ (range cap.emb)ᶜ := by
      rw [cap.compl_eq]
      exact mem_iUnion₂.mpr ⟨C, hC, hxD⟩
    exact this (mem_range_self x)
  calc
    cap.emb '' Γ.U ∩ (cap.cuffDisc C ∪ cap.emb '' C)
      = (cap.emb '' Γ.U ∩ cap.cuffDisc C) ∪ (cap.emb '' Γ.U ∩ cap.emb '' C) :=
        inter_union_distrib_left _ _ _
    _ = cap.emb '' (Γ.U ∩ C) := by
        rw [hdisj_disc.inter_eq, empty_union, ← image_inter cap.isEmbedding.injective]
    _ = cap.emb '' (Γ.V ∩ C) := by
        rw [proper_drawing_inter_subset_bd hprop hC_bd]
    _ = cap.emb '' Γ.V ∩ cap.emb '' C :=
        image_inter cap.isEmbedding.injective

/-- Every cuff `C ∈ cuffs S` has a unique cuff region `r` of `capDrawing hS cap Γ` in `Shat`.
Moreover `cap.cuffDisc C ⊆ r`, `closure (cap.cuffDisc C) ⊆ closure r`, `cap.emb '' C ⊆ closure r`,
and a region `s ∈ (capDrawing hS cap Γ).R` satisfies `IsCuffRegion hS cap Γ C s` if and only if
`(s ∩ closure (cap.cuffDisc C)).Nonempty`. -/
theorem exists_unique_cuffRegion {S Shat : Type}
    [TopologicalSpace S] [TopologicalSpace Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) {Γ : Surface.Drawing S}
    (hprop : Γ.IsProper) {C : Set S} (hC : C ∈ cuffs S) :
    ∃ r : Set Shat,
      IsCuffRegion hS cap Γ C r ∧
      cap.cuffDisc C ⊆ r ∧
      closure (cap.cuffDisc C) ⊆ closure r ∧
      cap.emb '' C ⊆ closure r ∧
      ∀ s ∈ (capDrawing hS cap Γ).R,
        (IsCuffRegion hS cap Γ C s ↔ s = r) ∧
        ((s ∩ closure (cap.cuffDisc C)).Nonempty ↔ s = r) := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hcl : IsClosedSurface Shat := cap.isClosedSurface
  have : T2Space Shat := hcl.2.1
  have : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hcl
  let Γ_hat := capDrawing hS cap Γ
  let Δ := closure (cap.cuffDisc C)
  have hΔ : IsClosedDisc Δ := cap.cuffDisc_closedDisc C hC
  have havoid : Γ_hat.U ∩ Δ = Γ_hat.V ∩ discBd Δ :=
    capDrawing_inter_closure_cuffDisc hS cap hprop hC
  obtain ⟨r, hr, hInt, hΔr, huniq⟩ := exists_unique_region_meeting_disc hcl hΔ havoid
  have hInt_eq : discInt Δ = cap.cuffDisc C := (cap.cuffDisc_eq_discInt hS hC).symm
  have hdisc_r : cap.cuffDisc C ⊆ r := hInt_eq ▸ hInt
  have hC_Δ : cap.emb '' C ⊆ Δ := by
    rw [← cap.cuffDisc_bd C hC]
    exact Surface.discBd_subset Δ
  have hC_clr : cap.emb '' C ⊆ closure r := hC_Δ.trans hΔr
  have hCdiff_r : cap.emb '' (C \ Γ.V) ⊆ r := by
    rintro _ ⟨x, ⟨hxC, hxV⟩, rfl⟩
    have hx_not_U : cap.emb x ∉ Γ_hat.U := by
      rintro ⟨y, hyU, hyx⟩
      have hyx_eq : y = x := cap.isEmbedding.injective hyx
      cases hyx_eq
      have hC_bd : C ⊆ bd S := by
        rcases hC with ⟨z, hz, rfl⟩
        exact connectedComponentIn_subset (bd S) z
      have hx_in_V : x ∈ Γ.V ∩ C :=
        (proper_drawing_inter_subset_bd hprop hC_bd).subset ⟨hyU, hxC⟩
      exact hxV hx_in_V.1
    obtain ⟨s, hs, hxs⟩ := exists_region_of_notMem (Γ := Γ_hat) hx_not_U
    have hsr : s = r := huniq s hs ⟨cap.emb x, hxs, hC_Δ (mem_image_of_mem cap.emb hxC)⟩
    exact hsr ▸ hxs
  have hC_oarc : IsOArc C := (cuff_statement S hS).2.2 C hC
  have hC_inf : C.Infinite := infinite_of_isOArc hC_oarc
  obtain ⟨x₀, hx₀C, hx₀V⟩ := hC_inf.exists_notMem_finite Γ.finite_V
  refine ⟨r, ⟨hC, hr, hCdiff_r⟩, hdisc_r, hΔr, hC_clr, fun s hs ↦ ⟨?_, ?_⟩⟩
  · constructor
    · intro hs_cuff
      exact huniq s hs ⟨cap.emb x₀, hs_cuff.2.2 ⟨x₀, ⟨hx₀C, hx₀V⟩, rfl⟩,
        hC_Δ (mem_image_of_mem cap.emb hx₀C)⟩
    · rintro rfl
      exact ⟨hC, hr, hCdiff_r⟩
  · constructor
    · exact huniq s hs
    · rintro rfl
      obtain ⟨y, hy⟩ := hΔ.nonempty_discInt
      exact ⟨y, hInt hy, hy.1⟩

/-! ## 2. Variant of Graph Minors XII, (3.2) under Claim (4) of (5.1) -/

private theorem vertex_count_le_of_union_count_le'
    {S : Type*} [TopologicalSpace S] (Γ : Surface.Drawing S) {A B P : Set S}
    (hcap : A ∩ B = A ∩ P)
    (hcount : (Γ.V ∩ (A ∪ B)).ncard ≤ (Γ.V ∩ (A ∪ P)).ncard) :
    (Γ.V ∩ B).ncard ≤ (Γ.V ∩ P).ncard := by
  have hcommon : (Γ.V ∩ A) ∩ (Γ.V ∩ B) = (Γ.V ∩ A) ∩ (Γ.V ∩ P) := by
    have h₁ : (Γ.V ∩ A) ∩ (Γ.V ∩ B) = Γ.V ∩ (A ∩ B) := by
      ext x; simp only [mem_inter_iff]; tauto
    have h₂ : (Γ.V ∩ A) ∩ (Γ.V ∩ P) = Γ.V ∩ (A ∩ P) := by
      ext x; simp only [mem_inter_iff]; tauto
    rw [h₁, h₂, hcap]
  have h₁ := Set.ncard_union_add_ncard_inter (Γ.V ∩ A) (Γ.V ∩ B)
    (Γ.finite_V.inter_of_left A) (Γ.finite_V.inter_of_left B)
  have h₂ := Set.ncard_union_add_ncard_inter (Γ.V ∩ A) (Γ.V ∩ P)
    (Γ.finite_V.inter_of_left A) (Γ.finite_V.inter_of_left P)
  rw [hcommon] at h₁
  rw [inter_union_distrib_left, inter_union_distrib_left] at hcount
  omega

/-- On a sphere `S`, if `D` and `D_sel` are distinct closed discs with the same boundary `F`,
then `closure (univ \ D) ⊆ D_sel`. -/
private theorem closure_compl_subset_of_sphere_disc_ne
    {S : Type*} [TopologicalSpace S] [T2Space S] ( hs : IsSphere S)
    {D D_sel F : Set S} (hD : IsClosedDisc D) (hDsel : IsClosedDisc D_sel)
    (hbD : discBd D = F) (hbDsel : discBd D_sel = F) (hne : D_sel ≠ D) :
    closure (univ \ D) ⊆ D_sel := by
  obtain ⟨Δ₁, Δ₂, _, _, _, _, _, hcov, _, _, huniq⟩ :=
    sphere_disc S hs F (hbD ▸ hD.isOArc_discBd)
  have hunion : D ∪ D_sel = univ := by
    rcases huniq D hD hbD with rfl | rfl <;>
    rcases huniq D_sel hDsel hbDsel with rfl | rfl
    · exact (hne rfl).elim
    · exact hcov
    · exact (Set.union_comm _ _).trans hcov
    · exact (hne rfl).elim
  refine closure_minimal ?_ hDsel.isCompact.isClosed
  intro x hx
  have hx_all : x ∈ D ∪ D_sel := hunion.symm.subset (mem_univ x)
  exact hx_all.resolve_left hx.2

/-- Replacement for `normal_chord_vertex_count_ge_min` in the one-disc sphere case of XII, (3.2)
when freeness is replaced by Claim (4) of XXI, (5.1). -/
private theorem normal_chord_vertex_count_ge_min_of_cuff_ins
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hs : IsSphere S) {Γ : Surface.Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    {Δ A B P : Set S} {a b : S}
    (hΔ : IsClosedDisc Δ) (hbΔ : discBd Δ = A ∪ B)
    (havoid : Γ.U ∩ Δ = Γ.V ∩ discBd Δ)
    (hzθ : (Γ.V ∩ discBd Δ).ncard ≤ θ)
    (hno_ins : ∀ F D : Set S,
      Γ.IsNormal F → IsOArc F → F ⊆ closure (univ \ Δ) →
      (Γ.V ∩ F).ncard < (Γ.V ∩ discBd Δ).ncard →
      IsClosedDisc D → subBd D = F →
      ((PaintingOrDrawing.drawing Γ).inter D,
        (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T →
      ¬ discBd Δ ⊆ D)
    (hA : IsLineWithEnds A a b) (hB : IsLineWithEnds B a b) (hP : IsLineWithEnds P a b)
    (hAB : A ∩ B = {a, b}) (hAP : A ∩ P = {a, b}) (hBP : B ∩ P = {a, b})
    (hPΔ : P ∩ Δ = {a, b}) (hP_comp : P ⊆ closure (univ \ Δ)) (hnP : Γ.IsNormal P) :
    min (Γ.V ∩ A).ncard (Γ.V ∩ B).ncard ≤ (Γ.V ∩ P).ncard := by
  obtain ⟨D, hD, hbD, _, hnA, houtD⟩ := exists_sphere_theta_side_disc hS hs hA hB hP hAB hAP hBP
  obtain ⟨E, hE, hbE, _, hnB, houtE⟩ := exists_sphere_theta_side_disc hS hs hB hA hP
    ((Set.inter_comm B A).trans hAB) hBP hAP
  have hnPΔ : ¬ P ⊆ Δ := by
    intro hsub
    obtain ⟨x, hxP, hxne⟩ := line_sdiff_ends_nonempty hP
    exact hxne (hPΔ.subset ⟨hxP, hsub hxP⟩)
  have hcov := GM11.theta_cover hS hP hA hB
    ((Set.inter_comm P A).trans hAP) hAB hBP hΔ hD hE
    ((GM14.IsClosedDisc.frontier_eq_discBd hS hΔ).trans hbΔ)
    ((GM14.IsClosedDisc.frontier_eq_discBd hS hD).trans hbD)
    ((GM14.IsClosedDisc.frontier_eq_discBd hS hE).trans (hbE.trans (Set.union_comm A P))) hnPΔ hnA hnB
  have hΓcov : Γ.U ⊆ D ∪ E := by
    intro x hx
    have hxcover : x ∈ Δ ∪ D ∪ E := hcov.symm.subset (mem_univ x)
    rcases hxcover with (hxΔ | hxD) | hxE
    · have hxBd := (havoid.subset ⟨hx, hxΔ⟩).2
      rw [hbΔ] at hxBd
      rcases hxBd with hxA | hxB
      · exact Or.inr (Surface.discBd_subset E (hbE.symm.subset (Or.inl hxA)))
      · exact Or.inl (Surface.discBd_subset D (hbD.symm.subset (Or.inl hxB)))
    · exact Or.inl hxD
    · exact Or.inr hxE
  have hn : Γ.IsNormal (A ∪ B ∪ P) := by
    intro x hx
    rcases hx.1 with hxAB | hxP
    · have hxBd : x ∈ discBd Δ := hbΔ.symm.subset hxAB
      exact (havoid.subset ⟨hx.2, Surface.discBd_subset Δ hxBd⟩).1
    · exact hnP ⟨hxP, hx.2⟩
  let G : PaintingOrDrawing S := .drawing Γ
  have hfD : frontier D = B ∪ P := (GM14.IsClosedDisc.frontier_eq_discBd hS hD).trans hbD
  have hfE : frontier E = A ∪ P := (GM14.IsClosedDisc.frontier_eq_discBd hS hE).trans hbE
  have hnD : G.IsNormal (frontier D) := by
    rw [hfD]
    intro x hx
    exact hn ⟨hx.1.elim (fun h => Or.inl (Or.inr h)) Or.inr, hx.2⟩
  have hnE : G.IsNormal (frontier E) := by
    rw [hfE]
    intro x hx
    exact hn ⟨hx.1.elim (fun h => Or.inl (Or.inl h)) Or.inr, hx.2⟩
  have hnot : (G.inter D, G.interOutside D) ∉ T ∨ (G.inter E, G.interOutside E) ∉ T := by
    by_cases hmD : (G.inter D, G.interOutside D) ∈ T
    · right
      intro hmE
      exact not_support_subset_of_normal_frontiers (Γ := G) (GM11.IsTangle.isPretangle hT)
        hD.isCompact.isClosed hE.isCompact.isClosed hE.isCompact.isClosed hnD hnE hnE
        hmD hmE hmE (fun x hx => Or.inl (hΓcov hx))
    · exact Or.inl hmD
  have hbdΔ_sub_comp : discBd Δ ⊆ closure (univ \ Δ) := by
    rw [← GM14.IsClosedDisc.frontier_eq_discBd hS hΔ, frontier_eq_closure_inter_closure,
      compl_eq_univ_sdiff]
    exact inter_subset_right
  have hA_comp : A ⊆ closure (univ \ Δ) :=
    (subset_union_left (s := A) (t := B)).trans (hbΔ ▸ hbdΔ_sub_comp)
  have hB_comp : B ⊆ closure (univ \ Δ) :=
    (subset_union_right (s := A) (t := B)).trans (hbΔ ▸ hbdΔ_sub_comp)
  rcases hnot with hnDsel | hnEsel
  · have hcount : (Γ.V ∩ (B ∪ A)).ncard ≤ (Γ.V ∩ (B ∪ P)).ncard := by
      by_contra hlt
      push Not at hlt
      have hcount_Δ : (Γ.V ∩ (B ∪ P)).ncard < (Γ.V ∩ discBd Δ).ncard := by
        rwa [hbΔ, Set.union_comm A B]
      have hcard_θ : ((B ∪ P) ∩ Γ.V).ncard < θ := by
        rw [Set.inter_comm]
        exact hcount_Δ.trans_le hzθ
      have hBP_oarc : IsOArc (B ∪ P) := hbD ▸ hD.isOArc_discBd
      have hnBP : Γ.IsNormal (B ∪ P) := hfD ▸ hnD
      obtain ⟨D_sel, hDsel, hbd_sel, hm_sel⟩ := hrespect.2 (B ∪ P) hBP_oarc hnBP hcard_θ
      have hbDsel : discBd D_sel = B ∪ P :=
        (GM14.IsClosedDisc.frontier_eq_discBd hS hDsel).symm.trans
          ((subBd_eq_frontier D_sel).symm.trans hbd_sel)
      have hne_D : D_sel ≠ D := fun heq ↦ hnDsel (heq ▸ hm_sel)
      have hcomp_sub : closure (univ \ D) ⊆ D_sel :=
        closure_compl_subset_of_sphere_disc_ne hs hD hDsel hbD hbDsel hne_D
      have hbdΔ_in : discBd Δ ⊆ D_sel := by
        rw [hbΔ]
        exact houtD.trans hcomp_sub
      exact hno_ins (B ∪ P) D_sel hnBP hBP_oarc (union_subset hB_comp hP_comp)
        hcount_Δ hDsel hbd_sel hm_sel hbdΔ_in
    have hcap : B ∩ A = B ∩ P := (Set.inter_comm B A).trans (hAB.trans hBP.symm)
    exact (min_le_left _ _).trans (vertex_count_le_of_union_count_le' Γ hcap hcount)
  · have hcount : (Γ.V ∩ (A ∪ B)).ncard ≤ (Γ.V ∩ (A ∪ P)).ncard := by
      by_contra hlt
      push Not at hlt
      have hcount_Δ : (Γ.V ∩ (A ∪ P)).ncard < (Γ.V ∩ discBd Δ).ncard := by
        rwa [hbΔ]
      have hcard_θ : ((A ∪ P) ∩ Γ.V).ncard < θ := by
        rw [Set.inter_comm]
        exact hcount_Δ.trans_le hzθ
      have hAP_oarc : IsOArc (A ∪ P) := hbE ▸ hE.isOArc_discBd
      have hnAP : Γ.IsNormal (A ∪ P) := hfE ▸ hnE
      obtain ⟨E_sel, hEsel, hbd_sel, hm_sel⟩ := hrespect.2 (A ∪ P) hAP_oarc hnAP hcard_θ
      have hbEsel : discBd E_sel = A ∪ P :=
        (GM14.IsClosedDisc.frontier_eq_discBd hS hEsel).symm.trans
          ((subBd_eq_frontier E_sel).symm.trans hbd_sel)
      have hne_E : E_sel ≠ E := fun heq ↦ hnEsel (heq ▸ hm_sel)
      have hcomp_sub : closure (univ \ E) ⊆ E_sel :=
        closure_compl_subset_of_sphere_disc_ne hs hE hEsel hbE hbEsel hne_E
      have hbdΔ_in : discBd Δ ⊆ E_sel := by
        rw [hbΔ, Set.union_comm A B]
        exact houtE.trans hcomp_sub
      exact hno_ins (A ∪ P) E_sel hnAP hAP_oarc (union_subset hA_comp hP_comp)
        hcount_Δ hEsel hbd_sel hm_sel hbdΔ_in
    exact (min_le_right _ _).trans
      (vertex_count_le_of_union_count_le' Γ (hAB.trans hAP.symm) hcount)

/-- Replacement for `sphere_chord_bound_in_complement` using Claim (4) of XXI, (5.1). -/
private theorem sphere_chord_bound_in_complement_of_cuff_ins
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hs : IsSphere S) (Γ : Surface.Drawing S) {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    {Δ : Set S} (hΔ : IsClosedDisc Δ) (havoid : Γ.U ∩ Δ = Γ.V ∩ discBd Δ)
    (hzθ : (Γ.V ∩ discBd Δ).ncard ≤ θ)
    (hno_ins : ∀ F D : Set S,
      Γ.IsNormal F → IsOArc F → F ⊆ closure (univ \ Δ) →
      (Γ.V ∩ F).ncard < (Γ.V ∩ discBd Δ).ncard →
      IsClosedDisc D → subBd D = F →
      ((PaintingOrDrawing.drawing Γ).inter D,
        (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T →
      ¬ discBd Δ ⊆ D)
    (C : Set S) (hC_eq : C = closure (univ \ Δ)) (hUC : Γ.U ⊆ C)
    (hbdC : bd C = (Subtype.val : C → S) ⁻¹' discBd Δ)
    (hCΔ : C ∩ Δ = discBd Δ)
    (x y : C) (A B P : Set C) (hA : IsLineWithEnds A x y) (hB : IsLineWithEnds B x y)
    (hP : IsLineWithEnds P x y) (hAB : A ∩ B = {x, y}) (hAP : A ∩ P = {x, y})
    (hBP : B ∩ P = {x, y}) (hbd : bd C = A ∪ B) (hcap : P ∩ bd C = {x, y})
    (hn : (drawingInSubspace Γ C hUC).IsNormal P) :
    min ((drawingInSubspace Γ C hUC).V ∩ A).ncard
      ((drawingInSubspace Γ C hUC).V ∩ B).ncard ≤
      ((drawingInSubspace Γ C hUC).V ∩ P).ncard := by
  let f : C → S := Subtype.val
  have hbdΔC : discBd Δ ⊆ C := hCΔ.symm.subset.trans inter_subset_left
  have hbimage : f '' bd C = discBd Δ := by
    rw [hbdC, Subtype.image_preimage_coe]
    exact inter_eq_right.mpr hbdΔC
  have hbd' : discBd Δ = f '' A ∪ f '' B :=
    hbimage.symm.trans ((congrArg (Set.image f) hbd).trans (image_union f A B))
  have himageInter : ∀ {L M : Set C}, L ∩ M = {x, y} →
      f '' L ∩ f '' M = {x.val, y.val} := by
    intro L M hLM
    rw [← image_inter Subtype.val_injective, hLM, image_pair]
  have hPΔ : f '' P ∩ Δ = {x.val, y.val} := by
    apply Subset.antisymm
    · rintro z ⟨⟨w, hw, rfl⟩, hwΔ⟩
      have hwBd : w.val ∈ discBd Δ := hCΔ.subset ⟨w.property, hwΔ⟩
      have hwB : w ∈ bd C := hbdC.symm ▸ hwBd
      rcases hcap.subset ⟨hw, hwB⟩ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro z hz
      rcases hz with rfl | rfl
      · have hx := hcap.symm.subset (Or.inl rfl)
        exact ⟨⟨x, hx.1, rfl⟩, Surface.discBd_subset Δ (hbdC.subset hx.2)⟩
      · have hy := hcap.symm.subset (Or.inr rfl)
        exact ⟨⟨y, hy.1, rfl⟩, Surface.discBd_subset Δ (hbdC.subset hy.2)⟩
  have hP_comp : f '' P ⊆ closure (univ \ Δ) := by
    rw [← hC_eq]
    rintro _ ⟨w, _, rfl⟩
    exact w.2
  have hcount := normal_chord_vertex_count_ge_min_of_cuff_ins hS hs hT hrespect hΔ hbd'
    havoid hzθ hno_ins
    (isLineWithEnds_subtype_image hA) (isLineWithEnds_subtype_image hB)
    (isLineWithEnds_subtype_image hP) (himageInter hAB) (himageInter hAP) (himageInter hBP)
    hPΔ hP_comp (drawingInSubspace_isNormal_image Γ C hUC hn)
  have hcounts : ∀ Q : Set C, (Γ.V ∩ f '' Q).ncard = ((drawingInSubspace Γ C hUC).V ∩ Q).ncard := by
    intro Q
    rw [← drawingInSubspace_image_vertices_inter Γ C hUC Q,
      Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [hcounts A, hcounts B, hcounts P] at hcount
  exact hcount

/-- Replacement for `theorem_3_2_one_disc` using Claim (4) of XXI, (5.1). -/
private theorem theorem_3_2_one_disc_of_cuff_ins
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hs : IsSphere S) (Γ : Surface.Drawing S) {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    (Δ : Fin 1 → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i)) (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i))
    {p : ℕ} (Zs : Fin p → Set S) (hcover : (⋃ j, Zs j) = discBoundaryVertices Γ Δ)
    (hdisZ : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) (hfeasible : IsTopologicallyFeasible Δ Zs)
    (hzθ : (discBoundaryVertices Γ Δ).ncard ≤ θ)
    (hno_ins : ∀ (F D : Set S) (i : Fin 1),
      Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
      (Γ.V ∩ F).ncard < (Γ.V ∩ discBd (Δ i)).ncard →
      IsClosedDisc D → subBd D = F →
      ((PaintingOrDrawing.drawing Γ).inter D,
        (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T →
      ¬ discBd (Δ i) ⊆ D) :
    HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs := by
  have hdis : Pairwise (fun i j => Disjoint (Δ i) (Δ j)) := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim _ _))
  let C := discComplement Δ
  let hUC := drawing_support_subset_discComplement hS Γ Δ hΔ hdis havoid
  let G := drawingInSubspace Γ C hUC
  have hDisc : GM06.IsClosedDiscSpace C := isClosedDiscSpace_discComplement_one hS hs Δ hΔ
  have hGproper : G.IsProper := drawingInDiscComplement_isProper hS Γ Δ hΔ hdis havoid
  have hZbd : ∀ j, Zs j ⊆ ⋃ i, discBd (Δ i) := by
    intro j x hx
    have hxZ := hcover.subset (mem_iUnion.mpr ⟨j, hx⟩)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxZ
    exact mem_iUnion.mpr ⟨i, hi.2⟩
  have hZC : ∀ j, Zs j ⊆ C := by
    intro j x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hZbd j hx)
    exact disc_boundary_subset_discComplement hS Δ hΔ hdis i hi
  have hGB : G.V ∩ bd C = (Subtype.val : C → S) ⁻¹' discBoundaryVertices Γ Δ := by
    dsimp only [G, C]
    rw [drawingInSubspace_V, discComplement_boundary_eq hS Δ hΔ]
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_iUnion, discBoundaryVertices]
    exact ⟨fun ⟨hv, i, hi⟩ => ⟨i, hv, hi⟩, fun ⟨i, hv, hi⟩ => ⟨hv, i, hi⟩⟩
  have hcoverC : (⋃ j, (Subtype.val : C → S) ⁻¹' Zs j) = G.V ∩ bd C := by
    rw [hGB, ← hcover]
    ext x
    simp only [mem_iUnion, mem_preimage]
  have hCF := isCrossFree_of_topological_feasible_in_discComplement hS Δ hΔ hdis Zs
    hZbd hfeasible hDisc
  have hunionBd : (⋃ i, discBd (Δ i)) = discBd (Δ 0) := by
    ext x
    simp only [mem_iUnion, Fin.exists_fin_one]
  have hbdC : bd C = (Subtype.val : C → S) ⁻¹' discBd (Δ 0) := by
    have h := discComplement_boundary_eq hS Δ hΔ
    rw [hunionBd] at h
    exact h
  have hCΔ : C ∩ Δ 0 = discBd (Δ 0) := by
    apply Subset.antisymm (discComplement_inter_disc_subset_boundary hS Δ hΔ 0)
    intro x hx
    exact ⟨disc_boundary_subset_discComplement hS Δ hΔ hdis 0 hx, Surface.discBd_subset _ hx⟩
  have hsingle : (⋃ i, Δ i) = Δ 0 := by
    ext x
    simp only [mem_iUnion, Fin.exists_fin_one]
  have hC_eq : C = closure (univ \ Δ 0) := by
    dsimp only [C]
    rw [discComplement, hsingle, compl_eq_univ_sdiff]
  have hz0_θ : (Γ.V ∩ discBd (Δ 0)).ncard ≤ θ := by
    refine (Set.ncard_le_ncard (fun x hx ↦ mem_iUnion.mpr ⟨0, hx⟩) ?_).trans hzθ
    exact Γ.finite_V.subset fun x hx ↦ by
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact hj.1
  have hno_ins0 : ∀ F D : Set S,
      Γ.IsNormal F → IsOArc F → F ⊆ closure (univ \ Δ 0) →
      (Γ.V ∩ F).ncard < (Γ.V ∩ discBd (Δ 0)).ncard →
      IsClosedDisc D → subBd D = F →
      ((PaintingOrDrawing.drawing Γ).inter D,
        (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T →
      ¬ discBd (Δ 0) ⊆ D := by
    intro F D hnF hF hF_sub hlt hD hbdD hmD
    have hF_disc : F ⊆ discComplement Δ := by
      simpa only [← hC_eq, C] using hF_sub
    exact hno_ins F D 0 hnF hF hF_disc hlt hD hbdD hmD
  have hconnect := connecting_subdrawings_of_disc_chord_bound_allowing_empty G hDisc hGproper
    (fun j => (Subtype.val : C → S) ⁻¹' Zs j) hcoverC
    (fun i j hij => (hdisZ i j hij).preimage Subtype.val) hCF
    (sphere_chord_bound_in_complement_of_cuff_ins hS hs Γ hT hrespect (hΔ 0) (havoid 0)
      hz0_θ hno_ins0 C hC_eq hUC hbdC hCΔ)
  rw [hGB] at hconnect
  exact hasConnectingSubdrawings_from_closed_subspace Γ C isClosed_closure hUC hZC hconnect

/-- Replacement for `free_boundary_count_le_of_enclosing_disc` using Claim (4) of XXI, (5.1). -/
private theorem boundary_count_le_of_enclosing_disc_of_cuff_ins
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) {Γ K : Surface.Drawing S} {θ η z : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Surface.Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    (hη : η ≤ θ) (hzη : z ≤ η) (Δ r : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι) (hr : ∀ i, r i ∈ Γ.R)
    (hrΔ : ∀ i, (r i ∩ Δ i).Nonempty)
    (hsep : ∀ i j, i ≠ j → η ≤ tangleMetric Γ K ins θ (r i) (r j))
    (hsmall : (discBoundaryVertices Γ Δ).ncard ≤ z)
    (hno_ins : ∀ (F D : Set S) (i : ι),
      Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
      (Γ.V ∩ F).ncard < (Γ.V ∩ discBd (Δ i)).ncard →
      IsClosedDisc D → subBd D = F →
      ((PaintingOrDrawing.drawing Γ).inter D,
        (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T →
      ¬ discBd (Δ i) ⊆ D)
    {F D : Set S} (hF : IsOArc F) (hn : Γ.IsNormal F) (hFstar : F ⊆ discComplement Δ)
    (hD : IsClosedDisc D) (hbd : discBd D = F) (i : ι)
    (hexact : ∀ j, Δ j ⊆ D ↔ j = i) :
    (Γ.V ∩ discBd (Δ i)).ncard ≤ (Γ.V ∩ F).ncard := by
  by_cases hshort : (Γ.V ∩ F).ncard < η
  · have hone : ∀ j k, Δ j ⊆ D → Δ k ⊆ D → j = k := by
      intro j k hj hk
      exact ((hexact j).mp hj).trans ((hexact k).mp hk).symm
    have hm := small_disc_is_selected_of_at_most_one_prescribed_disc hS hT hrespect hK hd
      hη Δ r hΔ hcase hr hrΔ hsep hF hn hshort hFstar hD hbd hone
    have hsubBd : subBd D = F :=
      (subBd_eq_frontier D).trans ((GM14.IsClosedDisc.frontier_eq_discBd hS hD).trans hbd)
    by_contra hlt
    push Not at hlt
    exact hno_ins F D i hn hF hFstar hlt hD hsubBd hm
      ((Surface.discBd_subset (Δ i)).trans ((hexact i).mpr rfl))
  · have hfinite : (discBoundaryVertices Γ Δ).Finite := Γ.finite_V.subset (by
      intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact hj.1)
    have hsub : Γ.V ∩ discBd (Δ i) ⊆ discBoundaryVertices Γ Δ :=
      fun _ hx => mem_iUnion.mpr ⟨i, hx⟩
    exact (Set.ncard_le_ncard hsub hfinite).trans
      (hsmall.trans (hzη.trans (le_of_not_gt hshort)))

/-- Variant of Graph Minors XII, (3.2) (pages 245–248) where the freeness hypothesis on
`V(Γ) ∩ bd(Δ_i)` is replaced by Claim (4) of Graph Minors XXI, (5.1) (page 16 of the preprint). -/
theorem theorem_3_2_of_cuff_ins
    {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (t z : ℕ) :
    ∃ η : ℕ, 1 ≤ η ∧ ∀ (Δ : Fin t → Set S) (Γ : Surface.Drawing S) (θ : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (p : ℕ) (Zs : Fin p → Set S),
      (∀ i, IsClosedDisc (Δ i) ∧ Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i)) →
      Pairwise (fun i j => Disjoint (Δ i) (Δ j)) →
      (discBoundaryVertices Γ Δ).ncard ≤ z →
      (⋃ j, Zs j) = discBoundaryVertices Γ Δ →
      (∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) → IsTopologicallyFeasible Δ Zs →
      η ≤ θ → HasTangleMetric Γ θ T d →
      (∀ i j, i ≠ j → ∀ ri ∈ Γ.R, (ri ∩ Δ i).Nonempty →
        ∀ rj ∈ Γ.R, (rj ∩ Δ j).Nonempty → η ≤ d ri rj) →
      (∀ (F D : Set S) (i : Fin t),
        Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
        (Γ.V ∩ F).ncard < (Γ.V ∩ discBd (Δ i)).ncard →
        IsClosedDisc D → subBd D = F →
        ((PaintingOrDrawing.drawing Γ).inter D,
          (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T →
        ¬ discBd (Δ i) ⊆ D) →
      HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs := by
  have h75 : GM07Theorem75Statement.{0} :=
    GM07.gm07_theorem_7_5
  have h51 : GM07Theorem51Statement.{0} := GM07.gm07_theorem_5_1
  have h55 : GM07Theorem55Statement.{0} := GM07.gm07_theorem_5_5
  by_cases hcase : ¬ IsSphere S ∨ 3 ≤ t
  · obtain ⟨N, hN⟩ := GM12.theorem_3_1_proof hS t z hcase
    let η := 2 * max N z + 1
    have h2N : 2 * N < η := Nat.lt_succ_of_le (Nat.mul_le_mul_left 2 (le_max_left N z))
    have hNη : N < η := (Nat.le_mul_of_pos_left N (by decide : 0 < 2)).trans_lt h2N
    have hzη : z ≤ η := (le_max_right N z).trans
      ((Nat.le_mul_of_pos_left (max N z) (by decide : 0 < 2)).trans (Nat.le_succ _))
    refine ⟨η, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
    intro Δ Γ θ T d p Zs hΔ hdis hcount hcover hdisZ hfeasible horder hm hsep hno_ins
    have hregion : ∀ i, ∃ r ∈ Γ.R, (r ∩ Δ i).Nonempty := by
      intro i
      obtain ⟨r, hr, hInt, _, _⟩ := exists_unique_region_meeting_disc hS (hΔ i).1 (hΔ i).2
      obtain ⟨x, hx⟩ := (hΔ i).1.nonempty_discInt
      exact ⟨r, hr, x, hInt hx, hx.1⟩
    choose r hr hrΔ using hregion
    obtain ⟨hT, K, ins, hK, hd, heq⟩ := hm
    have hsep' : ∀ i j, i ≠ j → η ≤ tangleMetric Γ K ins θ (r i) (r j) := by
      intro i j hij
      rw [← heq (r i) (Or.inr (hr i)) (r j) (Or.inr (hr j))]
      exact hsep i j hij (r i) (hr i) (hrΔ i) (r j) (hr j) (hrΔ j)
    have hcase' : ¬ IsSphere S ∨ 3 ≤ Nat.card (Fin t) := by simpa only [Nat.card_fin] using hcase
    apply hN Γ Δ (fun i => (hΔ i).1) hdis (fun i => (hΔ i).2) p Zs
    · intro F hn hF _ hsmall
      exact small_circle_bounds_at_most_one_prescribed_disc hS hT.2.1 hT.2.2 hK hd horder hNη
        Δ r hr hrΔ hsep' hF hn hsmall
    · intro A B P D E u v hn hA hB hP hu hv hPA hPB hstar hD hE hbD hbE hDE hi hj
      exact joined_circle_vertex_count_gt hS hT.2.1 hT.2.2 hK hd horder Δ r (fun i => (hΔ i).1)
        hcase' hr hrΔ hsep' h2N hn hA hB hP hu hv hPA hPB hstar hD hE hbD hbE hDE hi hj
    · intro A B D E hn hA hB hstar hD hE hbD hbE hcap hi hj
      exact meeting_circle_vertex_count_gt hS hT.2.1 hT.2.2 hK hd horder Δ r (fun i => (hΔ i).1)
        hcase' hr hrΔ hsep' h2N hn hA hB hstar hD hE hbD hbE hcap hi hj
    · intro ht _ P D a b _ hn hP hPP hstar hDs
      subst t
      apply theta_vertex_count_gt hS hT.2.1 hT.2.2 hK hd horder Δ r (fun i => (hΔ i).1)
        hr hrΔ hsep' hNη P D hn hP hPP hstar (fun i => (hDs i).1) (fun i => (hDs i).2.1)
      · intro i
        simpa only [Fin.cast_refl, id_eq] using (hDs i).2.2.1
      · exact fun i => (hDs i).2.2.2
    · exact hcover
    · exact hdisZ
    · exact hfeasible
    · intro F hn hF hstar D hD hbD i hi
      exact boundary_count_le_of_enclosing_disc_of_cuff_ins hS hT.2.1 hT.2.2 hK hd horder hzη
        Δ r (fun i => (hΔ i).1) hcase' hr hrΔ hsep' hcount hno_ins hF hn hstar hD hbD i hi
    · exact hcount
  · have hs : IsSphere S := by
      by_contra hn
      exact hcase (Or.inl hn)
    have ht : t ≤ 2 := by
      by_contra hn
      exact hcase (Or.inr (by omega))
    interval_cases t
    · refine ⟨1, le_rfl, ?_⟩
      intro Δ Γ θ T d p Zs _ _ _ hcover _ _ _ _ _ _
      have hZ : discBoundaryVertices Γ Δ = ∅ := by simp [discBoundaryVertices]
      rw [hZ] at hcover ⊢
      exact hasConnectingSubdrawings_of_empty_union Γ Zs hcover
    · refine ⟨max 1 z, le_max_left _ _, ?_⟩
      intro Δ Γ θ T d p Zs hΔ _ hcount hcover hdisZ hfeas horder hm _ hno_ins
      have hzθ : (discBoundaryVertices Γ Δ).ncard ≤ θ :=
        hcount.trans ((le_max_right 1 z).trans horder)
      exact theorem_3_2_one_disc_of_cuff_ins hS hs Γ hm.1.2.1 hm.1.2.2 Δ
        (fun i => (hΔ i).1) (fun i => (hΔ i).2) Zs hcover hdisZ hfeas hzθ hno_ins
    · have hcase3 : ¬ IsSphere S ∨ 3 ≤ 3 := Or.inr le_rfl
      obtain ⟨a, b, hcomplex, hmodel⟩ := exists_uniform_discComplement_model hS 3 hcase3
      let N := 42 * (z + 3 + 1) * GM07.vModel a b (3 + 1) (z + 3 + 1)
      let η' := 2 * max N z + 1
      have hη'pos : 1 ≤ η' := Nat.succ_le_succ (Nat.zero_le _)
      have h2N : 2 * N < η' := Nat.lt_succ_of_le (Nat.mul_le_mul_left 2 (le_max_left N z))
      have hNη : N < η' := (Nat.le_mul_of_pos_left N (by decide : 0 < 2)).trans_lt h2N
      have hzη : z ≤ η' := (le_max_right N z).trans
        ((Nat.le_mul_of_pos_left (max N z) (by decide : 0 < 2)).trans (Nat.le_succ _))
      refine ⟨2 * η' + 1, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
      intro Δ Γ θ T d p Zs hΔ hdis hcount hcover hdisZ hfeas horder hm hsep hno_ins
      have hreg : ∀ i, ∃ r ∈ Γ.R, (r ∩ Δ i).Nonempty := by
        intro i
        obtain ⟨r, hr, hInt, _, _⟩ := exists_unique_region_meeting_disc hS (hΔ i).1 (hΔ i).2
        obtain ⟨x, hx⟩ := (hΔ i).1.nonempty_discInt
        exact ⟨r, hr, x, hInt hx, hx.1⟩
      choose r hr hrΔ using hreg
      have hsep2 : ∀ i j, i ≠ j → 2 * η' + 1 ≤ d (r i) (r j) :=
        fun i j hij => hsep i j hij (r i) (hr i) (hrΔ i) (r j) (hr j) (hrΔ j)
      have hfar := hsep2 0 1 (by decide)
      obtain ⟨q, hq, hq0, _, hq1⟩ := exists_intermediate_region hS hm hη'pos (hr 0) (hr 1) hfar
      have hqfar : ∀ i : Fin 2, η' ≤ d (r i) q := by
        intro i; fin_cases i
        · exact hq0
        · exact hq1
      have h91 := GM11.gm15_theorem_9_1 Γ θ T d hS inferInstance hm
      have hqne : ∀ i, q ≠ r i := by
        intro i heq
        have h := hqfar i
        rw [heq, h91.2.1 (r i) (Or.inr (hr i))] at h
        exact (Nat.not_succ_le_zero _ (hη'pos.trans h))
      have hZV : ∀ j, Zs j ⊆ Γ.V := by
        intro j x hx
        have hxZ : x ∈ discBoundaryVertices Γ Δ := hcover.subset (mem_iUnion.mpr ⟨j, hx⟩)
        obtain ⟨i, hi⟩ := mem_iUnion.mp hxZ
        exact hi.1
      have hZbd : ∀ j, Zs j ⊆ ⋃ i, discBd (Δ i) := by
        intro j x hx
        have hxZ : x ∈ discBoundaryVertices Γ Δ := hcover.subset (mem_iUnion.mpr ⟨j, hx⟩)
        obtain ⟨i, hi⟩ := mem_iUnion.mp hxZ
        exact mem_iUnion.mpr ⟨i, hi.2⟩
      obtain ⟨F_amb, hFF, hFU, hFV, hFclasses⟩ := exists_ambient_feasibility_forest hS Δ
        (fun i => (hΔ i).1) hdis Zs (fun j => Γ.finite_V.subset (hZV j)) hZbd hfeas
      obtain ⟨E, hE, hEq, hEU, hEF, hED⟩ := exists_auxiliary_disc_in_region hS Γ F_amb Δ r
        (fun i => (hΔ i).1) (fun i => (hΔ i).2) hr hrΔ hq hqne
      let Δ' : Fin 3 → Set S := Fin.cons E Δ
      let r' : Fin 3 → Set S := Fin.cons q r
      have hΔ' : ∀ i, IsClosedDisc (Δ' i) := Fin.forall_fin_succ.mpr ⟨hE, fun i => (hΔ i).1⟩
      have hdis' : Pairwise (fun i j => Disjoint (Δ' i) (Δ' j)) := by
        intro i j
        refine Fin.cases ?_ (fun i => ?_) i
        · refine Fin.cases ?_ (fun j => ?_) j
          · intro hij; exact False.elim (hij rfl)
          · intro _; exact hED j
        · refine Fin.cases ?_ (fun j => ?_) j
          · intro _; exact (hED i).symm
          · intro hij; exact hdis (fun he => hij (congrArg Fin.succ he))
      have hVE : Γ.V ∩ discBd E = ∅ := boundary_vertices_eq_empty_of_disc_disjoint Γ hEU
      have havoid' : ∀ i, Γ.U ∩ Δ' i = Γ.V ∩ discBd (Δ' i) := by
        refine Fin.forall_fin_succ.mpr ⟨?_, fun i => (hΔ i).2⟩
        exact hEU.symm.inter_eq.trans hVE.symm
      have hr' : ∀ i, r' i ∈ Γ.R := Fin.forall_fin_succ.mpr ⟨hq, hr⟩
      have hrΔ' : ∀ i, (r' i ∩ Δ' i).Nonempty := by
        refine Fin.forall_fin_succ.mpr ⟨?_, hrΔ⟩
        obtain ⟨x, hx⟩ := hE.nonempty_discInt
        exact ⟨x, hEq hx.1, hx.1⟩
      have hsep' : ∀ i j, i ≠ j → η' ≤ d (r' i) (r' j) := by
        intro i j
        refine Fin.cases ?_ (fun i => ?_) i
        · refine Fin.cases ?_ (fun j => ?_) j
          · intro hij; exact False.elim (hij rfl)
          · intro _
            change η' ≤ d q (r j)
            rw [h91.2.2.2.1 q (Or.inr hq) (r j) (Or.inr (hr j))]
            exact hqfar j
        · refine Fin.cases ?_ (fun j => ?_) j
          · intro _; exact hqfar i
          · intro hij
            change η' ≤ d (r i) (r j)
            exact (Nat.le_add_right η' η' |>.trans (Nat.le_succ _)).trans
              (by simpa only [two_mul] using hsep2 i j (fun he => hij (congrArg Fin.succ he)))
      have hno_ins' : ∀ (F D : Set S) (i : Fin 3),
          Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ' →
          (Γ.V ∩ F).ncard < (Γ.V ∩ discBd (Δ' i)).ncard →
          IsClosedDisc D → subBd D = F →
          ((PaintingOrDrawing.drawing Γ).inter D,
            (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T →
          ¬ discBd (Δ' i) ⊆ D := by
        intro F D i hnF hF hF_sub hlt hD hbdD hmD
        refine Fin.cases ?_ (fun j => ?_) i hlt
        · intro hlt0
          change (Γ.V ∩ F).ncard < (Γ.V ∩ discBd E).ncard at hlt0
          rw [hVE, ncard_empty] at hlt0
          exact (Nat.not_lt_zero _ hlt0).elim
        · intro hltj
          have hcomp_sub : discComplement Δ' ⊆ discComplement Δ := by
            unfold discComplement
            refine closure_mono (compl_subset_compl.mpr ?_)
            intro x hx
            obtain ⟨k, hk⟩ := mem_iUnion.mp hx
            exact mem_iUnion.mpr ⟨k.succ, hk⟩
          exact hno_ins F D j hnF hF (hF_sub.trans hcomp_sub) hltj hD hbdD hmD
      have hZeq : discBoundaryVertices Γ Δ' = discBoundaryVertices Γ Δ :=
        discBoundaryVertices_fin_cons_of_disjoint Γ Δ hEU
      have hcontacts := drawing_contact_fin_cons_of_disjoint F_amb Δ hEF
      have hZbd' : (⋃ j, Zs j) ⊆ ⋃ i, discBd (Δ' i) := by
        intro x hx
        obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hZbd j hj)
        exact mem_iUnion.mpr ⟨i.succ, hi⟩
      have hclasses' : ∀ j, ∀ x ∈ Zs j, ∀ y ∈ F_amb.V ∩ ⋃ i, Δ' i,
          Nonempty (GraphWalk F_amb.toGraph x y) ↔ y ∈ Zs j := by
        intro j x hx y hy
        exact hFclasses j x hx y (hcontacts.2.subset hy)
      obtain ⟨H, hHF, hHB, hclasses⟩ := exists_punctured_forest_of_ambient hS Δ' hΔ' hdis' Zs
        F_amb hFF (hcontacts.1.trans hFU) (hcontacts.2.trans hFV) hZbd' hclasses'
      obtain ⟨hT, K, ins, hK, hd, heq⟩ := hm
      have hsepmetric : ∀ i j, i ≠ j → η' ≤ tangleMetric Γ K ins θ (r' i) (r' j) := by
        intro i j hij
        rw [← heq (r' i) (Or.inr (hr' i)) (r' j) (Or.inr (hr' j))]
        exact hsep' i j hij
      have hηorder : η' ≤ θ := (Nat.le_add_right η' η' |>.trans (Nat.le_succ _)).trans
        (by simpa only [two_mul] using horder)
      have hcase3' : ¬ IsSphere S ∨ 3 ≤ Nat.card (Fin 3) := by simpa only [Nat.card_fin] using hcase3
      have hbound : ∀ F : Set S, Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ' →
          ∀ D : Set S, IsClosedDisc D → discBd D = F →
          ∀ i, (∀ j, Δ' j ⊆ D ↔ j = i) →
            (Γ.V ∩ discBd (Δ' i)).ncard ≤ (Γ.V ∩ F).ncard := by
        intro F hn hF hstar D hD hbD i hi
        exact boundary_count_le_of_enclosing_disc_of_cuff_ins hS hT.2.1 hT.2.2 hK hd hηorder hzη
          Δ' r' hΔ' hcase3' hr' hrΔ' hsepmetric (hZeq ▸ hcount) hno_ins' hF hn hstar hD hbD i hi
      have hresult : HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ') Zs := by
        apply connecting_subdrawings_of_alpha_bound_of_forest hS Γ Δ' hΔ' hdis' havoid' Zs
          (hcover.trans hZeq.symm) hdisZ H hHF hHB hclasses hbound a b 3 z hcomplex
          (hmodel Δ' hΔ' hdis') (hZeq ▸ hcount)
        apply Nat.le_of_lt
        have hUC := drawing_support_subset_discComplement hS Γ Δ' hΔ' hdis' havoid'
        apply alpha_gt_of_geometric_conditions hS Γ Δ' hΔ' hdis' hcase3 hUC N
        · intro F hn hF _ hsmall
          exact small_circle_bounds_at_most_one_prescribed_disc hS hT.2.1 hT.2.2 hK hd hηorder hNη
            Δ' r' hr' hrΔ' hsepmetric hF hn hsmall
        · intro A B P D E u v hn hA hB hP hu hv hPA hPB hstar hD hE hbD hbE hDE hi hj
          exact joined_circle_vertex_count_gt hS hT.2.1 hT.2.2 hK hd hηorder Δ' r' hΔ'
            hcase3' hr' hrΔ' hsepmetric h2N hn hA hB hP hu hv hPA hPB hstar hD hE hbD hbE hDE hi hj
        · intro A B D E hn hA hB hstar hD hE hbD hbE hcap hi hj
          exact meeting_circle_vertex_count_gt hS hT.2.1 hT.2.2 hK hd hηorder Δ' r' hΔ'
            hcase3' hr' hrΔ' hsepmetric h2N hn hA hB hstar hD hE hbD hbE hcap hi hj
        · intro ht _ P D a_pt b_pt _ hn hP hPP hstar hDs
          apply theta_vertex_count_gt hS hT.2.1 hT.2.2 hK hd hηorder Δ' r' hΔ' hr' hrΔ'
            hsepmetric hNη P D hn hP hPP hstar (fun i => (hDs i).1) (fun i => (hDs i).2.1)
          · intro i
            have hcast : Fin.cast ht.symm i = i := Fin.ext rfl
            simpa only [hcast] using (hDs i).2.2.1
          · exact fun i => (hDs i).2.2.2
        · exact exists_alphaCandidate_in_discComplement hS (by decide : 3 ≠ 0)
            hcase3 Γ Δ' hΔ' hdis' havoid'
      rwa [hZeq] at hresult

end GM21
end GraphMinor
