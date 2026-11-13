module

public import GraphMinor.GM06.Alg57OnePathWedge
public import GraphMinor.GM06.Alg57WedgeFacts
public import GraphMinor.GM06.Alg57InnerCuffCorner
public import GraphMinor.GM06.Alg57CuffRotation
public import GraphMinor.GM06.Alg57EdgeCorner
import GraphMinor.GM06.Section5CappedBarrierNice
import GraphMinor.GM06.Alg511CuffEnumeration
import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Alg57OnePathComplete
import GraphMinor.GM06.Section5CutStripSurface

/-!
# The left side of the one path at its start

For `k = 1` the path `P₁` starts at `s₁` on the inner cuff. Here we show that the corner after the
direction along which `P₁` leaves `s₁`, in a small counterclockwise star at `s₁`, is on side one
(`exists_start_chart_sideOne`). With `exists_wedgeQ_path` this gives side one for all left wedges
of `P₁`.

The idea. Let `c⁺` be the dart of the inner cuff edge `e` at `s₁` that goes counterclockwise
around the cuff, and `ĉ` its reverse. The dart after `c⁺` at `s₁` is `ĉ` (`inner_cuff_rotation`),
and the corner after `c⁺` is the inner cap. So the cone from the leaving direction `F` of `P₁`
counterclockwise to `c⁺` misses `P₁` and the cuffs (`disjoint_wedgeSet_of_rot`), and the side does
not change on it (`sphere_sideDich_cuffs`). To find its side we go to a point `y` of `e` close to
`s₁`. Its lift `(1, 2π + 2πt₀)` lies on the boundary of the cut disc `D` close to `Γ₁(0) = (1, 2π)`,
so the open cylinder near `y` has points on side one. Near `y` the drawing is just `e`, which has
the inner cap on one side. So the other corner at `y`, the corner after the direction along which
`ĉ` leaves `y`, is on side one. This corner meets the cone at `s₁` (`wedge_meet_of_in`), since
`ĉ` arrives at `s₁` along `c⁺`.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

section Points

variable (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})

include hθ hD hBd hstrip in
/-- **Inner points of the cut disc near a point of it.** Every neighbourhood of the lift of a point
of `D` contains the lift of a point of `D` over the open cylinder off `P₁`. -/
theorem exists_inner_point_near {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ D) {W : Set CylinderCover}
    (hW : IsOpen W) (hy : planeToCylinderCover p₀ ∈ W) :
    ∃ p ∈ D, planeToCylinderCover p ∈ W ∧
      radialCylinderProjection p ∉ bd ClosedCylinder ∧
      radialCylinderProjection p ∉ (L.pathDrawing 0).U := by
  have hcl := hD.subset_closure_discInt hp₀
  obtain ⟨p, hpW, hpI⟩ := mem_closure_iff.mp hcl _ (hW.preimage continuous_planeToCylinderCover) hy
  refine ⟨p, hpI.1, hpW, ?_⟩
  have hpb : (⟨p, hpI.1⟩ : D) ∉ bd D := fun h => hpI.2 ((val_mem_discBd_iff _).mpr h)
  have hpre := preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip
  have hnot : (⟨p, hpI.1⟩ : D) ∉ (fun p : D => radialCylinderProjection p.1) ⁻¹'
      (bd ClosedCylinder ∪ (L.pathDrawing 0).U) := by
    rw [hpre]; exact hpb
  exact ⟨fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩

include hBd in
/-- The lifts `(1, 2π + 2πu)` of the points of the inner cuff edge lie in the cut disc. -/
theorem inner_arc_mem {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ((1 : ℝ), 2 * Real.pi + 2 * Real.pi * u) ∈ D := by
  apply Surface.discBd_subset D
  rw [hBd]
  have h1 := (liftedLinkageCurve_props_raw hG.1 L 1).2.2.2.1
  have h2 := (liftedLinkageCurve_props_raw hG.1 L (1 + 1)).2.2.2.1
  refine Or.inl (Or.inr ⟨rfl, ?_, ?_⟩)
  · rw [h1]; push_cast; nlinarith [Real.pi_pos, hu.1]
  · rw [h2]; push_cast; nlinarith [Real.pi_pos, hu.2]

end Points

/-- The lift `(1, 2π + 2πu)` lies over the point `u` of the inner cuff edge. -/
theorem cylinderCoverProjection_inner_arc (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    cylinderCoverProjection (planeToCylinderCover ((1 : ℝ), 2 * Real.pi + 2 * Real.pi * u)) =
      initialCuffGapCurve 1 0 ⟨u, hu⟩ := by
  apply Subtype.ext
  apply Prod.ext
  · simp [cylinderCoverProjection, planeToCylinderCover, initialCuffGapCurve, cylinderPoint]
  · simp only [cylinderCoverProjection, planeToCylinderCover, initialCuffGapCurve, cylinderPoint]
    congr 1
    push_cast
    simp only [Fin.isValue, Fin.val_zero, Nat.cast_zero]
    ring

theorem spherePath_zero (L : CylinderLinkage 1 G) :
    spherePath L 0 = cylinderToSphere (cylinderM1Point 1 0) := by
  rw [spherePath_of_mem L ⟨le_rfl, zero_le_one⟩]
  exact congrArg cylinderToSphere (L.curve_parametrizes 0).2.2.1

section Start

variable (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
  {H : Drawing ClosedCylinder}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart (cylinderSphereDrawing H))}
  (hγ : EdgePar (cylinderSphereDrawing H) γ)
  (heI : ∀ j : Fin 1, cylinderToSphere '' (initialCuffGapCurve 1 j '' Ioo 0 1) ∈
    (cylinderSphereDrawing H).E)
  (hγI : ∀ j : Fin 1, ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve 1 j '' Ioo 0 1)) t =
    cylinderToSphere (initialCuffGapCurve 1 j t))

include hG hγI in
/-- Both darts of the inner cuff edge are at `s₁`. -/
theorem dartVertex_innerCuff (b : Bool) :
    dartVertex γ (⟨(cylinderToSphere '' (initialCuffGapCurve 1 0 '' Ioo 0 1), b), heI 0⟩ :
      DrawingDart (cylinderSphereDrawing H)) = spherePath L 0 := by
  rw [spherePath_zero L]
  cases b
  · simp only [dartVertex, endOf, Bool.false_eq_true, ↓reduceIte, hγI,
      (initialCuffGapCurve_props hG 0).1]
  · simp only [dartVertex, endOf, ↓reduceIte, hγI, (initialCuffGapCurve_props hG 0).2.1]
    rw [Subsingleton.elim (finSuccCycle (0 : Fin 1)) 0]

include hγ in
/-- **The directions of the cuffs at `s₁`.** In a counterclockwise star at `s₁` that misses the
outer cuff, the only directions in the cuffs are those of the two darts of the inner cuff edge. -/
theorem innerCuff_dirs {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    {Ψ : C(ClosedUnitDisc, EuclideanPlane)} {z : DrawingDart (cylinderSphereDrawing H) → Circle}
    (hst : IsCcwStar (cylinderSphereDrawing H) γ R (spherePath L 0) Φ z)
    (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    (hK : Disjoint (range Φ) (cylinderToSphere '' cylinderCuff2)) {w : Circle}
    (hw : polarRimMap Φ w ∈ cylinderToSphere '' bd ClosedCylinder) :
    w = z ⟨(cylinderToSphere '' (initialCuffGapCurve 1 0 '' Ioo 0 1), false), heI 0⟩ ∨
      w = z ⟨(cylinderToSphere '' (initialCuffGapCurve 1 0 '' Ioo 0 1), true), heI 0⟩ := by
  obtain ⟨x, hxbd, hxw⟩ := hw
  have hx1 : x ∈ cylinderCuff1 := by
    rw [bd_closedCylinder] at hxbd
    rcases hxbd with h | h
    · exact h
    · exact absurd ⟨x, h, hxw⟩ (disjoint_left.mp hK (mem_range_self _))
  have hxM : x ∉ cylinderM1 1 := by
    rintro ⟨j, rfl⟩
    rw [Subsingleton.elim j 0, ← spherePath_zero L, ← hst.polar.centre] at hxw
    exact polarDiscPoint_one_ne_centre w (hst.polar.inj hxw.symm)
  obtain ⟨i, hi⟩ := alg511_initial_gaps_cover_cuff one_pos hx1 hxM
  rw [Subsingleton.elim i 0] at hi
  have hwe : polarRimMap Φ w ∈ cylinderToSphere '' (initialCuffGapCurve 1 0 '' Ioo 0 1) :=
    hxw ▸ mem_image_of_mem _ hi
  have hwU : w ∈ rimDirs (cylinderSphereDrawing H) Φ := ((heI 0).2.1 hwe).1
  rw [hst.rimDirs_eq hγ] at hwU
  obtain ⟨a, ha, rfl⟩ := hwU
  have hae : polarRimMap Φ (z a) ∈ a.1.1 := by
    have h1 := hst.ray_mem_edge hγ hΨ ha one_pos le_rfl
    have h2 := discPt_mul ⟨1, zero_le_one, le_rfl⟩ (z a)
    simp only at h2
    rw [toSph_chartC hΨ, h2] at h1
    exact h1
  have he := (cylinderSphereDrawing H).edge_eq_of_mem a.2 (heI 0) hae hwe
  obtain ⟨⟨ae, ab⟩, haE⟩ := a
  simp only at he
  subst he
  cases ab
  · exact Or.inl rfl
  · exact Or.inr rfl

end Start

section Main

variable (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
  {U₁ U₂ : Set CylinderCover} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU : Disjoint U₁ U₂)
  (h₁ : ∀ t, coverLift L hG 1 t ∈ U₁) (h₂ : ∀ t, coverLift L hG 2 t ∈ U₂)
  {H : Drawing ClosedCylinder} (hGH : G.IsSubdrawing H) (hFU : H.U = G.U ∪ bd ClosedCylinder)
  (hFV : H.V = G.V)
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart (cylinderSphereDrawing H))}
  (hγ : EdgePar (cylinderSphereDrawing H) γ) (hR : IsDrawingRotation (cylinderSphereDrawing H) γ R)
  (hccw : IsCcwRotation (cylinderSphereDrawing H) γ R)
  (heI : ∀ j : Fin 1, cylinderToSphere '' (initialCuffGapCurve 1 j '' Ioo 0 1) ∈
    (cylinderSphereDrawing H).E)
  (hγI : ∀ j : Fin 1, ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve 1 j '' Ioo 0 1)) t =
    cylinderToSphere (initialCuffGapCurve 1 j t))

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw heI hγI in
/-- **The corner after the leaving direction of `P₁` at `s₁` is on side one.** -/
theorem exists_start_chart_sideOne :
    ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (Ψ : C(ClosedUnitDisc, EuclideanPlane))
      (F : Circle) (δ : ℝ),
      IsPolar (cylinderSphereDrawing H) (spherePath L 0) Φ ∧
      (∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) ∧
      0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) ∧
      (rimDirs (cylinderSphereDrawing H) Φ).Finite ∧
      F ∈ rimDirs (cylinderSphereDrawing H) Φ ∧ RunsOut Ψ F (spherePath L) 0 δ ∧
      CornerQ (cylinderSphereDrawing H) (sphereSide D U₁) Φ Ψ F := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩).1
  have hinf := infty_notMem_cylinderSphereDrawing_U H
  have hπ := Real.pi_pos
  set e := cylinderToSphere '' (initialCuffGapCurve 1 0 '' Ioo 0 1) with he_def
  set cp : DrawingDart (cylinderSphereDrawing H) := ⟨(e, false), heI 0⟩ with hcp_def
  set cn : DrawingDart (cylinderSphereDrawing H) := ⟨(e, true), heI 0⟩ with hcn_def
  have hcpv : dartVertex γ cp = spherePath L 0 := dartVertex_innerCuff L hG heI hγI false
  have hrot : R.rot cp = cn := by
    apply Subtype.ext
    have := inner_cuff_rotation hG hGH hFU hFV hγ hR hccw heI hγI 0
    rw [Subsingleton.elim (finPredCycle (0 : Fin 1)) 0] at this
    exact this
  have hXU := spherePath_subset_U L hGH
  have hCU : cylinderToSphere '' bd ClosedCylinder ⊆ (cylinderSphereDrawing H).U := by
    rw [cylinderSphereDrawing_U, hFU]; exact image_mono subset_union_right
  have hXCU : cylinderToSphere '' ((L.pathDrawing 0).U ∪ bd ClosedCylinder) ⊆
      (cylinderSphereDrawing H).U := by
    rw [image_union]; exact union_subset hXU hCU
  have hXC : IsGammaNice (cylinderSphereDrawing H)
      (cylinderToSphere '' ((L.pathDrawing 0).U ∪ bd ClosedCylinder)) := by
    have h := isGammaNice_capped_linkage_and_cuffs L hGH (by rw [hFU]; exact subset_union_right)
    have heq : (⋃ j, (L.pathDrawing j).U) = (L.pathDrawing 0).U := by
      ext x; simp only [mem_iUnion, Fin.exists_fin_one]
    rwa [heq] at h
  have hdc : dartCurve γ cp = edgeCurve γ e := by funext s; simp [dartCurve, cp]
  have hdcn : dartCurve γ cn = fun s => edgeCurve γ e (1 - s) := by
    funext s; simp [dartCurve, cn]
  have he0 : edgeCurve γ e 0 = spherePath L 0 := by rw [← hdc, dartCurve_zero, hcpv]
  have hγe : ∀ {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1),
      edgeCurve γ e t = cylinderToSphere (initialCuffGapCurve 1 0 ⟨t, ht⟩) := by
    intro t ht
    rw [edgeCurve_of_mem γ e ht, hγI 0]
  have hcuff1 : ∀ u, initialCuffGapCurve 1 0 u ∈ bd ClosedCylinder := by
    intro u
    rw [bd_closedCylinder]
    exact Or.inl ((initialCuffGapCurve_props hG 0).2.2.1 (mem_range_self u))
  -- the set where the side does not change, and a small star at `s₁`
  obtain ⟨N₀, hN₀, h0N₀, hdich⟩ := sphere_sideDich_cuffs L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ 0
  have h0N₀' : spherePath L 0 ∈ N₀ := by
    rw [spherePath_of_mem L ⟨le_rfl, zero_le_one⟩]; exact h0N₀
  set K₁ := spherePath L '' Icc (1 / 2) 1
  have hK₁ : IsClosed K₁ := (isCompact_Icc.image (continuous_spherePath L)).isClosed
  have h0K₁ : spherePath L 0 ∉ K₁ := by
    rintro ⟨s, hs, hs0⟩
    have := injOn_spherePath L ⟨by linarith [hs.1], hs.2⟩ ⟨le_rfl, zero_le_one⟩ hs0
    linarith [hs.1]
  set K₂ := cylinderToSphere '' cylinderCuff2
  have hK₂ : IsClosed K₂ := isClosedEmbedding_cylinderToSphere.isClosedMap _
    (isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const)
  have h0K₂ : spherePath L 0 ∉ K₂ := by
    rintro ⟨x, hx, hx0⟩
    rw [spherePath_zero L] at hx0
    have := injective_cylinderToSphere hx0
    rw [this] at hx
    change (cylinderM1Point 1 0).1.1 = 2 at hx
    simp [cylinderM1Point, cylinderPoint] at hx
  obtain ⟨Φ0, z, hst0⟩ := hccw (spherePath L 0) ⟨cp, hcpv⟩
  obtain ⟨Φ, hst, hsub⟩ := hst0.exists_small hS
    ((hN₀.inter hK₁.isOpen_compl).inter hK₂.isOpen_compl) ⟨⟨h0N₀', h0K₁⟩, h0K₂⟩
  obtain ⟨Ψ, hΨ, hw⟩ := hst.pos
  have hpos : 0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) := by
    rw [wind_chartC]; exact hw
  have hfin := hst.rimDirs_finite hγ
  have hrN₀ : range Φ ⊆ N₀ := fun x hx => (hsub hx).1.1
  have hrK₂ : Disjoint (range Φ) K₂ := disjoint_left.mpr fun x hx => (hsub hx).2
  have hloc : range Φ ∩ cylinderToSphere '' (L.pathDrawing 0).U ⊆
      spherePath L '' Icc 0 (1 / 2) := by
    rintro x ⟨hxΦ, hxX⟩
    rw [← image_spherePath L] at hxX
    obtain ⟨s, hs, rfl⟩ := hxX
    refine ⟨s, ⟨hs.1, ?_⟩, rfl⟩
    by_contra h
    exact (hsub hxΦ).1.2 ⟨s, ⟨(not_le.mp h).le, hs.2⟩, rfl⟩
  have hsub01 : Icc (0 : ℝ) (1 / 2) ⊆ Icc 0 1 := Icc_subset_Icc le_rfl (by norm_num)
  obtain ⟨F, hFX, ⟨δ, hrun⟩, hFonly⟩ := exists_path_dirs_start (t₀ := 0) hst.polar hΨ
    (isGammaNice_spherePath L hGH) (continuous_spherePath L) (by norm_num : (0 : ℝ) < 1 / 2)
    ((injOn_spherePath L).mono hsub01) ((image_mono hsub01).trans (image_spherePath L).subset) hloc
  refine ⟨Φ, Ψ, F, δ, hst.polar, hΨ, hpos, hfin, hXU hFX, hrun, ?_⟩
  -- the leaving direction of `P₁` is not that of `c⁺`
  have hcpe : polarRimMap Φ (z cp) ∈ e := by
    have h1 := hst.ray_mem_edge hγ hΨ hcpv one_pos le_rfl
    have h2 := discPt_mul ⟨1, zero_le_one, le_rfl⟩ (z cp)
    simp only at h2
    rw [toSph_chartC hΨ, h2] at h1
    exact h1
  have hFne : F ≠ z cp := by
    intro hFc
    rw [hFc, ← image_spherePath L] at hFX
    obtain ⟨s, hs, hsF⟩ := hFX
    obtain ⟨_, ⟨u, -, rfl⟩, hue⟩ := hcpe
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, ← hst.polar.centre] at hsF
      exact polarDiscPoint_one_ne_centre _ (hst.polar.inj hsF).symm
    rcases eq_or_lt_of_le hs.2 with h1 | h1
    · rw [h1, spherePath_of_mem L ⟨zero_le_one, le_rfl⟩] at hsF
      obtain ⟨j, hj⟩ := L.curve_one_mem 0
      refine disjoint_left.mp hrK₂ (mem_range_self (polarDiscPoint 1 (z cp)))
        ⟨L.curve 0 1, ?_, hsF⟩
      rw [← hj]
      change (cylinderM2Point 1 j).1.1 = 2
      simp [cylinderM2Point, cylinderPoint]
    · rw [spherePath_of_mem L hs] at hsF
      exact curve_notMem_bd L hG (t := ⟨s, hs⟩) (fun h => h0.ne' (congrArg Subtype.val h))
        (fun h => h1.ne (congrArg Subtype.val h)) (by
          rw [injective_cylinderToSphere (hsF.trans hue.symm)]; exact hcuff1 u)
  -- the cone from `F` to `c⁺` misses `P₁` and the cuffs
  have hdirs : ∀ w, polarRimMap Φ w ∈
      cylinderToSphere '' ((L.pathDrawing 0).U ∪ bd ClosedCylinder) →
      w = F ∨ w = z cp ∨ w = z (R.rot cp) := by
    intro w hw
    rw [image_union] at hw
    rcases hw with hw | hw
    · exact Or.inl (hFonly w hw)
    · rw [hrot]; exact Or.inr (innerCuff_dirs L hγ heI hst hΨ hrK₂ hw)
  have hWdisj := disjoint_wedgeSet_of_rot hst hγ hR hΨ hXC hcpv (hXU hFX) hFne hdirs
  have hWdich := hdich _ ((wedgeSet_subset_range hΨ F _).trans hrN₀)
    (isPreconnected_wedgeSet F _) hWdisj
  suffices hm : ∃ m ∈ wedgeSet Ψ F (angleTo F (z cp)), sphereSide D U₁ m by
    obtain ⟨m, hmW, hmQ⟩ := hm
    have hall : ∀ x ∈ wedgeSet Ψ F (angleTo F (z cp)), sphereSide D U₁ x := by
      rcases hWdich with h | h
      · exact h
      · exact absurd hmQ (h m hmW)
    intro x hx
    exact hall x (cornerSet_subset_wedgeSet hfin (hst.mem_rimDirs hγ hcpv) hx)
  -- the run of `c⁺` from `s₁`
  obtain ⟨δu, hδu, ρu, -, hρu0, hρumono, hρuG⟩ := hst.runsOut hγ hΨ hcpv
  -- a point `y` of the cuff edge near `s₁` whose lift is on side one
  have hcont2 : Continuous fun s : ℝ =>
      planeToCylinderCover ((1 : ℝ), 2 * Real.pi + 2 * Real.pi * s) :=
    continuous_planeToCylinderCover.comp (by fun_prop)
  have hq0 : planeToCylinderCover ((1 : ℝ), 2 * Real.pi + 2 * Real.pi * 0) ∈ U₁ := by
    have hp1 := (liftedLinkageCurve_props_raw hG.1 L 1).2.1
    have hp2 := (liftedLinkageCurve_props_raw hG.1 L 1).2.2.2.1
    have heq : ((1 : ℝ), 2 * Real.pi + 2 * Real.pi * 0) = liftedLinkageCurve hG.1 L 1 0 :=
      Prod.ext hp1.symm (by rw [hp2]; push_cast; ring)
    rw [heq]
    exact h₁ 0
  have hev1 : edgeCurve γ e ⁻¹' N₀ ∈ 𝓝 (0 : ℝ) :=
    (isEdgeCurve_edgeCurve hγ (heI 0)).cont.continuousAt.preimage_mem_nhds
      (hN₀.mem_nhds (by rw [he0]; exact h0N₀'))
  have hev2 : (fun s : ℝ => planeToCylinderCover ((1 : ℝ), 2 * Real.pi + 2 * Real.pi * s)) ⁻¹' U₁ ∈
      𝓝 (0 : ℝ) := hcont2.continuousAt.preimage_mem_nhds (hU₁.mem_nhds hq0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hev1 hev2)
  set t₀ := min (ε / 2) (min δu (1 / 2)) with ht₀_def
  have ht₀pos : 0 < t₀ := lt_min (half_pos hε) (lt_min hδu (by norm_num))
  have ht₀δ : t₀ ≤ δu := (min_le_right _ _).trans (min_le_left _ _)
  have ht₀h : t₀ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have ht₀ε : dist t₀ 0 < ε := by
    rw [dist_zero_right, Real.norm_of_nonneg ht₀pos.le]
    linarith [min_le_left (ε / 2) (min δu (1 / 2))]
  obtain ⟨hyN₀, hq₀U⟩ := hball (mem_ball.mpr ht₀ε)
  have ht₀I : t₀ ∈ Ioo (0 : ℝ) 1 := ⟨ht₀pos, by linarith⟩
  have ht₀C : t₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht₀I
  -- the edge chart at `y`
  obtain ⟨Φ₂, Ψ₂, F', B', δ₁', δ₂', hp₂, hsub₂, hΨ₂, hpos₂, hdirs₂, -, hout₂, hin₂⟩ :=
    exists_edge_chart_in hS hinf (heI 0) (isEdgeCurve_edgeCurve hγ (heI 0)) ht₀I hN₀ hyN₀
  have hfin₂ : (rimDirs (cylinderSphereDrawing H) Φ₂).Finite := by rw [hdirs₂]; exact toFinite _
  have hF'm : F' ∈ rimDirs (cylinderSphereDrawing H) Φ₂ := by rw [hdirs₂]; exact mem_insert _ _
  -- the corner after `F'` is in the inner cap
  have hcap : cornerSet (cylinderSphereDrawing H) Φ₂ Ψ₂ F' ⊆ toSph '' closedBall (0 : ℂ) (1 / 2) := by
    obtain ⟨ρ, hρ, hform⟩ := exists_cornerLabel hinf hγ hR hccw
    have hcl := inner_forward_corner_subset_closed_cap hG hFU hγ hρ hform 0 (heI 0) (hγI 0)
    obtain ⟨Φ', z', hst', hρcp⟩ := hform cp
    obtain ⟨Ψ', hΨ', hw'⟩ := hst'.pos
    have hpos' : 0 < wind (fun w : Circle => chartC Ψ' w) (chartC Ψ' 0) := by
      rw [wind_chartC]; exact hw'
    obtain ⟨δ', hrun'⟩ := hst'.runsOut hγ hΨ' rfl
    have hpu : IsPolar (cylinderSphereDrawing H) (dartCurve γ cp 0) Φ' := by
      rw [dartCurve_zero]; exact hst'.polar
    have hpm : IsPolar (cylinderSphereDrawing H) (dartCurve γ cp t₀) Φ₂ := by
      rw [hdc]; exact hp₂
    have hrunm : RunsOut Ψ₂ F' (dartCurve γ cp) t₀ δ₁' := by rw [hdc]; exact hout₂
    have heq := cornerRegion_start_eq_mid hS hinf (heI 0) (isEdgeCurve_dartCurve hγ cp) hpu hΨ'
      hpos' (hst'.rimDirs_finite hγ) (hst'.mem_rimDirs hγ rfl) hrun' ht₀I hpm hΨ₂ hpos₂ hfin₂
      hF'm hrunm
    intro x hx
    apply hcl
    apply subset_closure
    rw [hρcp, heq]
    exact image_cone_subset_cornerRegion hp₂ hΨ₂ hfin₂ F' hx
  -- a point of the open cylinder near `y` on side one
  have hy₀ : cylinderToSphere (cylinderCoverProjection
      (planeToCylinderCover ((1 : ℝ), 2 * Real.pi + 2 * Real.pi * t₀))) = edgeCurve γ e t₀ := by
    rw [cylinderCoverProjection_inner_arc t₀ ht₀C, hγe ht₀C]
  set Wc : Set CylinderCover := U₁ ∩
    (fun q => cylinderToSphere (cylinderCoverProjection q)) ⁻¹' interior (range Φ₂)
  have hWc : IsOpen Wc := hU₁.inter (isOpen_interior.preimage
    (continuous_cylinderToSphere.comp continuous_cylinderCoverProjection))
  have hq₀W : planeToCylinderCover ((1 : ℝ), 2 * Real.pi + 2 * Real.pi * t₀) ∈ Wc := by
    refine ⟨hq₀U, ?_⟩
    simp only [mem_preimage]
    rw [hy₀]
    exact hp₂.nhd
  obtain ⟨p, hpD, hpW, hpbd, -⟩ := exists_inner_point_near L hG hθ hD hBd hstrip
    (inner_arc_mem L hG hBd ht₀C) hWc hq₀W
  set x := radialCylinderProjection p
  have hxproj : cylinderCoverProjection (planeToCylinderCover p) = x := rfl
  have hQx : sphereSide D U₁ (cylinderToSphere x) :=
    ⟨x, rfl, planeToCylinderCover p, ⟨p, hpD, rfl⟩, hxproj, hpW.1⟩
  have hxΦ₂ : cylinderToSphere x ∈ range Φ₂ := by
    have := hpW.2
    simp only [mem_preimage, hxproj] at this
    exact interior_subset this
  have hxy : cylinderToSphere x ≠ edgeCurve γ e t₀ := by
    intro h
    rw [hγe ht₀C] at h
    exact hpbd (injective_cylinderToSphere h ▸ hcuff1 _)
  have heN : IsGammaNice (cylinderSphereDrawing H) e :=
    ⟨{e}, singleton_subset_iff.mpr (Or.inl (Or.inr (heI 0))), by simp⟩
  have hxU : cylinderToSphere x ∉ (cylinderSphereDrawing H).U := by
    intro hxU
    obtain ⟨t, ht, ht1, u, hu⟩ := exists_chart_polar hp₂ hΨ₂ hxΦ₂ hxy
    rw [hu] at hxU
    have hu' : u ∈ rimDirs (cylinderSphereDrawing H) Φ₂ :=
      (chart_ray_mem_iff hp₂ hΨ₂ (isGammaNice_U _) u ht ht1).mp hxU
    have hue : polarRimMap Φ₂ u ∈ e := by
      rw [hdirs₂] at hu'
      rcases hu' with rfl | hu'
      · have hδ := hout₂.1
        refine rim_mem_of_runsOut hp₂ hΨ₂ heN hout₂ (t := t₀ + min δ₁' ((1 - t₀) / 2))
          ⟨by linarith [lt_min hδ (by linarith [ht₀I.2] : (0 : ℝ) < (1 - t₀) / 2)],
            by linarith [min_le_left δ₁' ((1 - t₀) / 2)]⟩ ?_
        exact (isEdgeCurve_edgeCurve hγ (heI 0)).mem_edge
          ⟨by linarith [lt_min hδ (by linarith [ht₀I.2] : (0 : ℝ) < (1 - t₀) / 2)],
            by linarith [min_le_right δ₁' ((1 - t₀) / 2), ht₀I.2]⟩
      · rw [mem_singleton_iff.mp hu']
        have hδ := hin₂.1
        refine rim_mem_of_runsIn hp₂ hΨ₂ heN hin₂ (t := t₀ - min δ₂' (t₀ / 2))
          ⟨by linarith [min_le_left δ₂' (t₀ / 2)],
            by linarith [lt_min hδ (half_pos ht₀pos)]⟩ ?_
        exact (isEdgeCurve_edgeCurve hγ (heI 0)).mem_edge
          ⟨by linarith [min_le_right δ₂' (t₀ / 2)], by linarith [ht₀I.2, lt_min hδ (half_pos ht₀pos)]⟩
    have hxe := (chart_ray_mem_iff hp₂ hΨ₂ heN u ht ht1).mpr hue
    rw [← hu] at hxe
    obtain ⟨_, ⟨u', -, rfl⟩, hxe'⟩ := hxe
    exact hpbd (injective_cylinderToSphere hxe' ▸ hcuff1 u')
  obtain ⟨w, hw, hxw⟩ := exists_mem_cornerSet hp₂ hΨ₂ hfin₂ ⟨F', hF'm⟩ hxΦ₂ hxy hxU
  have hwB : w = B' := by
    rw [hdirs₂] at hw
    rcases hw with rfl | hw
    · exfalso
      obtain ⟨zc, hzc, hzx⟩ := hcap hxw
      have h1 := norm_eq_of_cylinderToSphere_eq hzx.symm
      have h2 : x.1.1 ≠ 1 := fun h => hpbd (by rw [bd_closedCylinder]; exact Or.inl h)
      have h3 : 1 ≤ x.1.1 := x.2.1.1
      have h4 := mem_closedBall_zero_iff.mp hzc
      have h5 : 1 < x.1.1 := lt_of_le_of_ne h3 (Ne.symm h2)
      linarith
    · exact mem_singleton_iff.mp hw
  rw [hwB] at hxw
  have hB'dich := hdich _ ((cornerSet_subset_range hΨ₂ B').trans hsub₂)
    (isPreconnected_cornerSet B') ((disjoint_cornerSet hp₂ hΨ₂ hfin₂ B').mono_right hXCU)
  have hB'Q : ∀ y ∈ cornerSet (cylinderSphereDrawing H) Φ₂ Ψ₂ B', sphereSide D U₁ y := by
    rcases hB'dich with h | h
    · exact h
    · exact absurd hQx (h _ hxw)
  -- the corner after `B'` meets the cone at `s₁`
  have hout : RunsOut Ψ₂ B' (dartCurve γ cn) (1 - t₀) δ₂' := by
    rw [hdcn]; exact hin₂.runsOut_one_sub
  have hc₂ : edgeCurve γ e t₀ = dartCurve γ cn (1 - t₀) := by
    rw [hdcn]; simp only [sub_sub_cancel]
  have hray : ∀ s ∈ Icc (1 - t₀) (1 - t₀ + t₀ / 2), 0 < ρu (1 - s) ∧ ρu (1 - s) < 1 ∧
      dartCurve γ cn s = toSph (chartC Ψ ((ρu (1 - s) : ℂ) * z cp)) := by
    intro s hs
    have hs' : 1 - s ∈ Icc (0 : ℝ) (0 + δu) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    obtain ⟨hlt, hGs⟩ := hρuG (1 - s) hs'
    have hpos' : 0 < ρu (1 - s) := by
      rw [← hρu0]
      exact hρumono ⟨le_rfl, by linarith⟩ hs' (by linarith [hs.2])
    refine ⟨hpos', hlt, ?_⟩
    rw [hdcn]
    simp only
    rw [← hdc]
    exact hGs
  have hanti : StrictAntiOn (fun s => ρu (1 - s)) (Icc (1 - t₀) (1 - t₀ + t₀ / 2)) := by
    intro s hs s' hs' hss'
    exact hρumono ⟨by linarith [hs'.2], by linarith [hs'.1]⟩
      ⟨by linarith [hs.2], by linarith [hs.1]⟩ (by linarith)
  obtain ⟨m, hm₂, hm₁⟩ := wedge_meet_of_in hst.polar hΨ hpos hfin hp₂ hΨ₂ hpos₂ hfin₂ (F₁ := F)
    (hst.mem_rimDirs hγ hcpv) (half_pos ht₀pos) hout hc₂ hray hanti
  exact ⟨m, hm₁, hB'Q m hm₂⟩

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw heI hγI in
/-- **The left side of `P₁` is side one.** Let every vertex of the capped drawing have a dart.
Then at each inner point of `P₁`, the left wedge of every path chart inside a set where the side
does not change is on side one. At the end of `P₁`, the corner before the arriving direction is on
side one if the side does not change on it. -/
theorem left_side_one
    (hV : ∀ v ∈ (cylinderSphereDrawing H).V, ∃ a : DrawingDart (cylinderSphereDrawing H),
      dartVertex γ a = v) :
    (∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) 1 → ∀ {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
        {Ψ : C(ClosedUnitDisc, EuclideanPlane)} {F B : Circle},
        IsPathChart (cylinderSphereDrawing H) (cylinderToSphere '' (L.pathDrawing 0).U)
          (spherePath L) t Φ Ψ F B →
        SideDich (cylinderToSphere '' (L.pathDrawing 0).U) (sphereSide D U₁) (range Φ) →
        ∀ x ∈ wedgeSet Ψ F (angleTo F B), sphereSide D U₁ x) ∧
      (∀ {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ : C(ClosedUnitDisc, EuclideanPlane)}
        {B B' : Circle} {δ : ℝ}, IsPolar (cylinderSphereDrawing H) (spherePath L 1) Φ →
        (∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) →
        0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) →
        (rimDirs (cylinderSphereDrawing H) Φ).Finite →
        B ∈ rimDirs (cylinderSphereDrawing H) Φ →
        B' * Circle.exp (gap (rimDirs (cylinderSphereDrawing H) Φ) B') = B →
        RunsIn Ψ B (spherePath L) 1 δ →
        ((∀ x ∈ cornerSet (cylinderSphereDrawing H) Φ Ψ B', sphereSide D U₁ x) ∨
          (∀ x ∈ cornerSet (cylinderSphereDrawing H) Φ Ψ B', ¬ sphereSide D U₁ x)) →
        CornerQ (cylinderSphereDrawing H) (sphereSide D U₁) Φ Ψ B') := by
  obtain ⟨P, hin, hst, hend⟩ := exists_wedgeQ_path (sphereSide D U₁) (isGammaNice_spherePath L hGH)
    (fun t ht => exists_side_pathChart L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hγ hccw hV ht)
  obtain ⟨Φ, Ψ, F, δ, hp, hΨ, hpos, hfin, hF, hrun, hQ⟩ :=
    exists_start_chart_sideOne L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw heI hγI
  have hP : P := (hst hp hΨ hpos hfin hF hrun (Or.inl hQ)).mp hQ
  exact ⟨fun ht _ _ _ _ hc hN => (hin ht hc hN).mpr hP,
    fun hp hΨ hpos hfin hB hB' hrun hd => (hend hp hΨ hpos hfin hB hB' hrun hd).mpr hP⟩

end Main

end GraphMinor.GM06
