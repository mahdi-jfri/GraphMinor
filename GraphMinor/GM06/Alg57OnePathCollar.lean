module

public import GraphMinor.GM06.Alg57OnePathSound
public import GraphMinor.GM06.Section5OpenCutSheet
import GraphMinor.GM06.Section5CutSeam
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5CutStripProjection
import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Alg57OnePathComplete

/-!
# The two sides of the one path, seen from the cut disc

For `k = 1` both sides of the linkage path `P₁` lie in the same strip of the cylinder. They are
told apart in the cut disc `D`: a point of the cylinder near `P₁` but off it has one lift in `D`,
and that lift is near `Γ₁` or near `Γ₂`. Here we make this precise.

Take disjoint open sets `U₁ ⊇ Γ₁` and `U₂ ⊇ Γ₂` of the angular cover. A point `x` of the
cylinder is on side `U` (`OnSide`) if it has a lift in `D` that lies in `U`. The main facts:
* the lifts in `D` of a point `P₁(t)` are `Γ₁(t)` and `Γ₂(t)` (`eq_lift_of_proj_eq_curve`);
* near `P₁(t)` every lift in `D` is near `Γ₁(t)` or near `Γ₂(t)` (`exists_nbhd_lift_mem`), since
  the cover image of `D` is compact;
* so a connected set near `P₁(t)` that misses `P₁` is on one side (`side_dichotomy`), because the
  lift off `P₁` is continuous (`exists_open_sheet_on_single_strip`).
-/

public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-- The lifts of the linkage path in the angular cover. -/
@[expose] noncomputable def coverLift (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (m : ℤ) (t : unitInterval) : CylinderCover :=
  planeToCylinderCover (liftedLinkageCurve hG.1 L m t)

theorem continuous_coverLift (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (m : ℤ) : Continuous (coverLift L hG m) :=
  continuous_planeToCylinderCover.comp (liftedLinkageCurve hG.1 L m).continuous

theorem proj_coverLift (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (m : ℤ) (t : unitInterval) : cylinderCoverProjection (coverLift L hG m t) = L.curve 0 t :=
  radialCylinderProjection_lift_one L hG.1 m t

/-- Clamping is injective on the radial strip. -/
theorem planeToCylinderCover_injOn_strip :
    InjOn planeToCylinderCover {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2} := by
  intro p hp q hq h
  have h' := congrArg cylinderCoverCoordinates h
  change (max 1 (min 2 p.1), p.2) = (max 1 (min 2 q.1), q.2) at h'
  rw [min_eq_right hp.2, max_eq_right hp.1, min_eq_right hq.2, max_eq_right hq.1] at h'
  exact h'

/-- **Inner points of `P₁` are off the cuffs.** A point of `P₁` on a cuff is a vertex of `G`, by
properness, so it lies in `M₁ ∪ M₂`. For `k = 1` these sets are the two ends of `P₁`, and the
curve of `P₁` is injective. -/
theorem curve_notMem_bd (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    {t : unitInterval} (h0 : t ≠ 0) (h1 : t ≠ 1) : L.curve 0 t ∉ bd ClosedCylinder := by
  intro hb
  have hpar := L.curve_parametrizes 0
  have hU : L.curve 0 t ∈ G.U := (L.isSubdrawing 0).2 (by rw [← hpar.2.1]; exact mem_range_self t)
  have hV : L.curve 0 t ∈ G.V := hG.2.1 ⟨hb, hU⟩
  have hM : L.curve 0 t ∈ cylinderM1 1 ∪ cylinderM2 1 := hG.2.2 ▸ ⟨hV, hb⟩
  rcases hM with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hj0 : j = 0 := Subsingleton.elim _ _
    subst hj0
    exact h0 (hpar.1 (hj.symm.trans hpar.2.2.1.symm))
  · obtain ⟨j', hj'⟩ := L.curve_one_mem 0
    have hjj : j = j' := Subsingleton.elim _ _
    subst hjj
    exact h1 (hpar.1 (hj.symm.trans hj'))

/-- A point `x` of the cylinder is on the side `U` if a lift of it in the cut disc lies in `U`. -/
@[expose] def OnSide (D : Set (ℝ × ℝ)) (U : Set CylinderCover) (x : ClosedCylinder) : Prop :=
  ∃ q ∈ planeToCylinderCover '' D, cylinderCoverProjection q = x ∧ q ∈ U

section Setting

variable (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})

include hθ hD hBd hstrip in
/-- **The lifts of a point of `P₁` in the cut disc are its points on `Γ₁` and `Γ₂`.** -/
theorem eq_lift_of_proj_eq_curve {p : ℝ × ℝ} (hp : p ∈ D) {t : unitInterval}
    (h : radialCylinderProjection p = L.curve 0 t) :
    p = liftedLinkageCurve hG.1 L 1 t ∨ p = liftedLinkageCurve hG.1 L 2 t := by
  have hseam := preimage_path_inter_single_strip_eq_seams L hG hθ 1 hD hBd hstrip
  have h12 : liftedLinkageCurve hG.1 L (1 + 1) = liftedLinkageCurve hG.1 L 2 := rfl
  rw [h12] at hseam
  have hmem : p ∈ D ∩ radialCylinderProjection ⁻¹' (L.pathDrawing 0).U := by
    refine ⟨hp, ?_⟩
    change radialCylinderProjection p ∈ (L.pathDrawing 0).U
    rw [h, ← (L.curve_parametrizes 0).2.1]
    exact mem_range_self t
  rw [hseam] at hmem
  have hinj := (L.curve_parametrizes 0).1
  rcases hmem with ⟨t', rfl⟩ | ⟨t', rfl⟩
  · left
    rw [radialCylinderProjection_lift_one L hG.1 1 t'] at h
    rw [hinj h]
  · right
    rw [radialCylinderProjection_lift_one L hG.1 2 t'] at h
    rw [hinj h]

include hθ hD hBd hstrip in
/-- **Near `P₁(t)` the lifts in `D` are near `Γ₁(t)` or `Γ₂(t)`.** The part of the compact cover
image of `D` outside `W₁ ∪ W₂` has a compact projection, which misses `P₁(t)`. -/
theorem exists_nbhd_lift_mem (t : unitInterval) {W₁ W₂ : Set CylinderCover} (hW₁ : IsOpen W₁)
    (hW₂ : IsOpen W₂) (h₁ : coverLift L hG 1 t ∈ W₁) (h₂ : coverLift L hG 2 t ∈ W₂) :
    ∃ N : Set ClosedCylinder, IsOpen N ∧ L.curve 0 t ∈ N ∧
      ∀ q ∈ planeToCylinderCover '' D, cylinderCoverProjection q ∈ N → q ∈ W₁ ∪ W₂ := by
  set K := (planeToCylinderCover '' D) \ (W₁ ∪ W₂)
  have hK : IsCompact K :=
    (hD.isCompact.image continuous_planeToCylinderCover).diff (hW₁.union hW₂)
  have hKc : IsClosed (cylinderCoverProjection '' K) :=
    (hK.image continuous_cylinderCoverProjection).isClosed
  refine ⟨(cylinderCoverProjection '' K)ᶜ, hKc.isOpen_compl, ?_, ?_⟩
  · rintro ⟨q, ⟨⟨p, hp, rfl⟩, hq⟩, hpx⟩
    rcases eq_lift_of_proj_eq_curve L hG hθ hD hBd hstrip hp hpx with rfl | rfl
    · exact hq (Or.inl h₁)
    · exact hq (Or.inr h₂)
  · intro q hq hqN
    by_contra hn
    exact hqN ⟨q, ⟨hq, hn⟩, rfl⟩

/-- Disjoint open sets around the two lifts. -/
theorem exists_side_sets :
    ∃ U₁ U₂ : Set CylinderCover, IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧
      (∀ t, coverLift L hG 1 t ∈ U₁) ∧ ∀ t, coverLift L hG 2 t ∈ U₂ := by
  have hdis : Disjoint (range (coverLift L hG 1)) (range (coverLift L hG 2)) := by
    rw [disjoint_left]
    rintro _ ⟨t, rfl⟩ ⟨t', ht'⟩
    have h := planeToCylinderCover_injOn_strip ((liftedLinkageCurve_props_raw hG.1 L 2).1 t')
      ((liftedLinkageCurve_props_raw hG.1 L 1).1 t) ht'
    exact disjoint_left.mp (disjoint_range_liftedLinkageCurve hG.1 L (show (1 : ℤ) ≠ 2 by norm_num))
      ⟨t, rfl⟩ ⟨t', h⟩
  obtain ⟨U₁, U₂, hU₁, hU₂, h₁, h₂, hU⟩ := SeparatedNhds.of_isCompact_isCompact
    (isCompact_range (continuous_coverLift L hG 1)) (isCompact_range (continuous_coverLift L hG 2))
    hdis
  exact ⟨U₁, U₂, hU₁, hU₂, hU, fun t => h₁ ⟨t, rfl⟩, fun t => h₂ ⟨t, rfl⟩⟩

section Sides

variable {U₁ U₂ : Set CylinderCover} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU : Disjoint U₁ U₂)
  (h₁ : ∀ t, coverLift L hG 1 t ∈ U₁) (h₂ : ∀ t, coverLift L hG 2 t ∈ U₂)

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ in
/-- **A connected set near `P₁(t)` that misses `P₁` is on one side.** -/
theorem side_dichotomy (t : unitInterval) :
    ∃ N : Set ClosedCylinder, IsOpen N ∧ L.curve 0 t ∈ N ∧
      ∀ S ⊆ N, IsPreconnected S → Disjoint S (L.pathDrawing 0).U →
        (∀ x ∈ S, OnSide D U₁ x) ∨ (∀ x ∈ S, OnSide D U₂ x) := by
  obtain ⟨N, hN, hxN, hNlift⟩ := exists_nbhd_lift_mem L hG hθ hD hBd hstrip t hU₁ hU₂ (h₁ t) (h₂ t)
  obtain ⟨s, -, hproj, hrange⟩ := exists_open_sheet_on_single_strip L hG hθ hD hBd hstrip
  refine ⟨N, hN, hxN, fun S hSN hS hSP => ?_⟩
  let T : Set (↥((L.pathDrawing 0).Uᶜ)) := Subtype.val ⁻¹' S
  have hTS : Subtype.val '' T = S := by
    rw [Subtype.image_preimage_coe]
    exact inter_eq_right.mpr fun x hx => disjoint_left.mp hSP hx
  have hT : IsPreconnected T := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, hTS]
    exact hS
  have hsT : s '' T ⊆ U₁ ∪ U₂ := by
    rintro _ ⟨y, hy, rfl⟩
    have hmem : s y ∈ range s := mem_range_self y
    rw [hrange] at hmem
    refine hNlift _ hmem.1 ?_
    rw [hproj]
    exact hSN hy
  have hlift : ∀ x ∈ S, ∀ U : Set CylinderCover, s '' T ⊆ U → OnSide D U x := by
    intro x hx U hTU
    have hxP : x ∈ (L.pathDrawing 0).Uᶜ := fun h => disjoint_left.mp hSP hx h
    have hmem : s ⟨x, hxP⟩ ∈ range s := mem_range_self _
    rw [hrange] at hmem
    exact ⟨_, hmem.1, hproj _, hTU ⟨⟨x, hxP⟩, hx, rfl⟩⟩
  rcases (hT.image s s.continuous.continuousOn).subset_or_subset hU₁ hU₂ hU hsT with h | h
  · exact Or.inl fun x hx => hlift x hx U₁ h
  · exact Or.inr fun x hx => hlift x hx U₂ h

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ in
/-- A point off `P₁` is on at most one side. -/
theorem not_onSide_two_of_onSide_one {x : ClosedCylinder} (hx : x ∉ (L.pathDrawing 0).U)
    (h1 : OnSide D U₁ x) : ¬ OnSide D U₂ x := by
  rintro ⟨q₂, ⟨p₂, hp₂, rfl⟩, hx₂, hq₂⟩
  obtain ⟨_, ⟨p₁, hp₁, rfl⟩, hx₁, hq₁⟩ := h1
  have he : (⟨p₁, hp₁⟩ : D) = ⟨p₂, hp₂⟩ :=
    single_strip_projection_inj_off_path L hG hθ hD hBd hstrip
      (p := ⟨p₁, hp₁⟩) (q := ⟨p₂, hp₂⟩)
      (by change cylinderCoverProjection (planeToCylinderCover p₁) ∉ (L.pathDrawing 0).U
          rw [hx₁]; exact hx)
      (by change cylinderCoverProjection (planeToCylinderCover p₁) =
            cylinderCoverProjection (planeToCylinderCover p₂)
          rw [hx₁, hx₂])
  have hp : p₁ = p₂ := congrArg Subtype.val he
  rw [hp] at hq₁
  exact disjoint_left.mp hU hq₁ hq₂

include hθ hD hBd hstrip hU₂ h₂ in
/-- **Lifts on side one converge to `Γ₁`.** Near `P₁(t)` a lift in `U₁` lies in any given
neighbourhood of `Γ₁(t)`. -/
theorem exists_nbhd_lift_mem_one (hU : Disjoint U₁ U₂) (t : unitInterval) {W : Set CylinderCover}
    (hW : IsOpen W) (hy : coverLift L hG 1 t ∈ W) :
    ∃ N : Set ClosedCylinder, IsOpen N ∧ L.curve 0 t ∈ N ∧
      ∀ q ∈ planeToCylinderCover '' D, cylinderCoverProjection q ∈ N → q ∈ U₁ → q ∈ W := by
  obtain ⟨N, hN, hxN, hlift⟩ := exists_nbhd_lift_mem L hG hθ hD hBd hstrip t hW hU₂ hy (h₂ t)
  refine ⟨N, hN, hxN, fun q hq hqN hq₁ => ?_⟩
  rcases hlift q hq hqN with h | h
  · exact h
  · exact absurd h (disjoint_left.mp hU hq₁)

include hθ hD hBd hstrip hU₁ h₁ in
/-- **Lifts on side two converge to `Γ₂`.** -/
theorem exists_nbhd_lift_mem_two (hU : Disjoint U₁ U₂) (t : unitInterval) {W : Set CylinderCover}
    (hW : IsOpen W) (hy : coverLift L hG 2 t ∈ W) :
    ∃ N : Set ClosedCylinder, IsOpen N ∧ L.curve 0 t ∈ N ∧
      ∀ q ∈ planeToCylinderCover '' D, cylinderCoverProjection q ∈ N → q ∈ U₂ → q ∈ W := by
  obtain ⟨N, hN, hxN, hlift⟩ := exists_nbhd_lift_mem L hG hθ hD hBd hstrip t hU₁ hW (h₁ t) hy
  refine ⟨N, hN, hxN, fun q hq hqN hq₂ => ?_⟩
  rcases hlift q hq hqN with h | h
  · exact absurd hq₂ (disjoint_left.mp hU h)
  · exact h

end Sides

include hθ hD hBd hstrip in
/-- **Inner points of the cut disc near a lift.** Every neighbourhood of `Γₘ(t)` in the cover
contains the lift of a point of the open cylinder off `P₁`. -/
theorem exists_inner_point_near_lift {m : ℤ} (hm : m = 1 ∨ m = 2) (t : unitInterval)
    {W : Set CylinderCover} (hW : IsOpen W) (hy : coverLift L hG m t ∈ W) :
    ∃ p ∈ D, planeToCylinderCover p ∈ W ∧
      radialCylinderProjection p ∉ bd ClosedCylinder ∧
      radialCylinderProjection p ∉ (L.pathDrawing 0).U := by
  have hΓD : liftedLinkageCurve hG.1 L m t ∈ D := by
    apply discBd_subset D
    rw [hBd]
    have h12 : liftedLinkageCurve hG.1 L (1 + 1) = liftedLinkageCurve hG.1 L 2 := rfl
    rw [liftedStripBoundary, h12]
    rcases hm with rfl | rfl
    · exact Or.inl (Or.inl (Or.inl (mem_range_self t)))
    · exact Or.inl (Or.inl (Or.inr (mem_range_self t)))
  have hcl := hD.subset_closure_discInt hΓD
  obtain ⟨p, hpW, hpI⟩ := mem_closure_iff.mp hcl _ (hW.preimage continuous_planeToCylinderCover) hy
  refine ⟨p, hpI.1, hpW, ?_⟩
  have hpb : (⟨p, hpI.1⟩ : D) ∉ bd D := fun h => hpI.2 ((val_mem_discBd_iff _).mpr h)
  have hpre := preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip
  have hnot : (⟨p, hpI.1⟩ : D) ∉ (fun p : D => radialCylinderProjection p.1) ⁻¹'
      (bd ClosedCylinder ∪ (L.pathDrawing 0).U) := by
    rw [hpre]; exact hpb
  exact ⟨fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩

end Setting

end GraphMinor.GM06
