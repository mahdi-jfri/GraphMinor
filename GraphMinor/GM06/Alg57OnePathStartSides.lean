module

public import GraphMinor.GM06.Alg57OnePathEndSides
public import GraphMinor.GM06.Alg57OnePathStart
import GraphMinor.GM06.Section5CappedBarrierNice
import GraphMinor.GM06.Alg511CuffEnumeration
import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Alg57OnePathComplete
import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Alg57CuffFace

/-!
# The sides of the rays at the start of the one path

At the start `s₁ = P₁(0)` the inner cuff is one loop edge with darts `c⁺` (`false`) and `c⁻`
(`true`), and `R.rot c⁺ = c⁻`. Let `b` be the dart of the first edge of `P₁`. In a small star at
`s₁` the directions of `b`, `c⁺`, `c⁻` cut the star into three parts: the wedge from `b` to `c⁺`,
the corner after `c⁺` (inside the inner cap, so outside the cylinder), and the wedge from `c⁻` to
`b`. The proof of `exists_start_chart_sideOne` shows that the first wedge is on side one; we repeat
it. A point on side two near `Γ₂(0)` then shows that the last wedge is not on side one. So the
rays at `s₁` are on side one exactly for the darts of the block `b, R.rot b, …` before `c⁺`
(`raySides_start`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology Metric Real GraphMinor.Surface GraphMinor.GM11 unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

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
/-- **The sides of the rays at the start of `P₁`.** With `b` the dart of the first edge of `P₁`
at `s₁`, the rays there are on side one exactly for the darts of the block `b, R.rot b, …` before
`c⁺`, the `false` dart of the inner cuff loop. -/
theorem raySides_start {b : DrawingDart (cylinderSphereDrawing H)}
    (hb : dartVertex γ b = spherePath L 0) (hbX : b.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U) :
    RaySides L D U₁ γ R 0 (fun d => ∃ i, (∀ j ≤ i, R.rot^[j] b ≠
      ⟨(cylinderToSphere '' (initialCuffGapCurve 1 0 '' Ioo 0 1), false), heI 0⟩) ∧
      R.rot^[i] b = d) := by
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

  have hm : ∃ m ∈ wedgeSet Ψ F (angleTo F (z cp)), sphereSide D U₁ m := by
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
  have hW1 : ∀ x ∈ wedgeSet Ψ F (angleTo F (z cp)), sphereSide D U₁ x := by
    obtain ⟨m, hmW, hmQ⟩ := hm
    rcases hWdich with h | h
    · exact h
    · exact absurd hmQ (h m hmW)
  -- the second dart `c⁻` of the cuff loop, and the order `b`, `c⁺`, `c⁻` of the directions
  have hcnv : dartVertex γ cn = spherePath L 0 := dartVertex_innerCuff L hG heI hγI true
  have hzb : z b = F := hFonly _ (hbX (hst.rim_mem_edge hγ hΨ hb))
  have hcne : polarRimMap Φ (z cn) ∈ e := by
    have h1 := hst.ray_mem_edge hγ hΨ hcnv one_pos le_rfl
    have h2 := discPt_mul ⟨1, zero_le_one, le_rfl⟩ (z cn)
    simp only at h2
    rw [toSph_chartC hΨ, h2] at h1
    exact h1
  have hFX' := hFX
  have hFne' : F ≠ z cn := by
    intro hFc
    rw [hFc, ← image_spherePath L] at hFX'
    obtain ⟨s, hs, hsF⟩ := hFX'
    obtain ⟨_, ⟨u, -, rfl⟩, hue⟩ := hcne
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, ← hst.polar.centre] at hsF
      exact polarDiscPoint_one_ne_centre _ (hst.polar.inj hsF).symm
    rcases eq_or_lt_of_le hs.2 with h1 | h1
    · rw [h1, spherePath_of_mem L ⟨zero_le_one, le_rfl⟩] at hsF
      obtain ⟨j, hj⟩ := L.curve_one_mem 0
      refine disjoint_left.mp hrK₂ (mem_range_self (polarDiscPoint 1 (z cn)))
        ⟨L.curve 0 1, ?_, hsF⟩
      rw [← hj]
      change (cylinderM2Point 1 j).1.1 = 2
      simp [cylinderM2Point, cylinderPoint]
    · rw [spherePath_of_mem L hs] at hsF
      exact curve_notMem_bd L hG (t := ⟨s, hs⟩) (fun h => h0.ne' (congrArg Subtype.val h))
        (fun h => h1.ne (congrArg Subtype.val h)) (by
          rw [injective_cylinderToSphere (hsF.trans hue.symm)]; exact hcuff1 u)
  have hcncp : z cn ≠ z cp := by
    intro h
    have := congrArg (fun d : DrawingDart (cylinderSphereDrawing H) => d.1.2)
      (hst.inj _ _ hcnv hcpv h)
    simp [cn, cp] at this
  have hbcp : b ≠ cp := fun h => hFne (by rw [← hzb, h])
  have hFD := hst.mem_rimDirs hγ hb
  rw [hzb] at hFD
  have hnext : z cp * Circle.exp (gap (rimDirs (cylinderSphereDrawing H) Φ) (z cp)) = z cn := by
    rw [← hrot]; exact hst.next_eq hγ hR hcpv
  have hgC := gap_pos hfin (z cp)
  have hgap : angleTo (z cp) (z cn) = gap (rimDirs (cylinderSphereDrawing H) Φ) (z cp) :=
    angleTo_eq ⟨hgC, gap_le_two_pi hfin _⟩ hnext.symm
  have hlast : angleTo (z cn) F ≤ angleTo (z cn) (z cp) := by
    have h := angleTo_le_of_next hfin hFD (by rw [hnext]; exact hFne') (by rw [hnext]; exact hcncp)
    rwa [hnext] at h
  -- past the corner after `c⁺`, the angles from `c⁻` are those from `c⁺` less the gap
  have hstep : ∀ u : Circle, u ≠ z cn →
      gap (rimDirs (cylinderSphereDrawing H) Φ) (z cp) ≤ angleTo (z cp) u →
      angleTo (z cp) u < angleTo (z cp) F → angleTo (z cn) u < angleTo (z cn) F := by
    intro u hun hgu hu
    have hlt : angleTo (z cp) (z cn) < angleTo (z cp) u := by
      rw [hgap]
      refine lt_of_le_of_ne hgu fun h => hun ?_
      rw [← mul_exp_angleTo (z cp) u, ← h, hnext]
    have hltF : angleTo (z cp) (z cn) < angleTo (z cp) F := hlt.trans hu
    rw [angleTo_sub hlt, angleTo_sub hltF]
    linarith
  -- the second wedge, from `c⁻` to `b`, misses `P₁` and the cuffs
  set W2 := wedgeSet Ψ (z cn) (angleTo (z cn) F)
  have hW2Z : Disjoint W2 (cylinderToSphere '' ((L.pathDrawing 0).U ∪ bd ClosedCylinder)) := by
    apply disjoint_wedgeSet hst.polar hΨ hXC
    intro θ' hθ' hmem
    have hθ2 : θ' ∈ Ioc 0 (2 * Real.pi) := ⟨hθ'.1, hθ'.2.le.trans (angleTo_le _ _)⟩
    rcases hdirs _ hmem with h | h | h
    · have := angleTo_eq hθ2 h.symm
      linarith [hθ'.2]
    · have := angleTo_eq hθ2 h.symm
      linarith [hθ'.2]
    · rw [hrot] at h
      have := angleTo_eq hθ2 h.symm
      rw [angleTo_self] at this
      linarith [hθ'.2, angleTo_le (z cn) F]
  have hdW2 := hdich W2 ((wedgeSet_subset_range hΨ _ _).trans hrN₀) (isPreconnected_wedgeSet _ _)
    hW2Z
  -- the corner after `c⁺` lies in the inner cap
  have hcap : ∀ y ∈ cornerSet (cylinderSphereDrawing H) Φ Ψ (z cp),
      y ∈ toSph '' closedBall (0 : ℂ) (1 / 2) := by
    obtain ⟨ρ₀, hρ₀, hform₀⟩ := exists_cornerLabel hinf hγ hR hccw
    have hcl := inner_forward_corner_subset_closed_cap hG hFU hγ hρ₀ hform₀ 0 (heI 0) (hγI 0)
    have hρcp := cornerLabel_eq_star hinf hγ hform₀ cp (by rw [hcpv]; exact hst)
    intro y hy
    exact hcl (subset_closure (hρcp ▸ image_cone_subset_cornerRegion hst.polar hΨ hfin _ hy))
  -- each direction off `P₁` and the cuffs lies in one of the three parts
  have htri : ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ u : Circle, u ≠ F → u ≠ z cp → u ≠ z cn →
      toSph (chartC Ψ ((r : ℂ) * u)) ∈ wedgeSet Ψ F (angleTo F (z cp)) ∨
        toSph (chartC Ψ ((r : ℂ) * u)) ∈ W2 ∨
        toSph (chartC Ψ ((r : ℂ) * u)) ∈ cornerSet (cylinderSphereDrawing H) Φ Ψ (z cp) := by
    intro r hr hr1 u huF huC huN
    by_cases h1 : angleTo F u < angleTo F (z cp)
    · exact Or.inl (mem_wedgeSet_of_lt hr hr1 h1)
    rcases right_of_not_left hFne (fun h => h.elim huF h1) with h | h
    · exact absurd h huC
    by_cases h2 : angleTo (z cp) u < gap (rimDirs (cylinderSphereDrawing H) Φ) (z cp)
    · exact Or.inr (Or.inr (mem_wedgeSet_of_lt hr hr1 h2))
    exact Or.inr (Or.inl (mem_wedgeSet_of_lt hr hr1 (hstep u huN (not_lt.mp h2) h)))
  have hxc : spherePath L 0 = cylinderToSphere (L.curve 0 0) :=
    spherePath_of_mem L ⟨le_rfl, zero_le_one⟩
  have hWo : ∀ U : Set CylinderCover, IsOpen U → IsOpen (U ∩
      (fun q => cylinderToSphere (cylinderCoverProjection q)) ⁻¹' interior (range Φ)) :=
    fun U hU' => hU'.inter (isOpen_interior.preimage
      (continuous_cylinderToSphere.comp continuous_cylinderCoverProjection))
  have hΓW : ∀ m : ℤ, ∀ U : Set CylinderCover, coverLift L hG m 0 ∈ U → coverLift L hG m 0 ∈ U ∩
      (fun q => cylinderToSphere (cylinderCoverProjection q)) ⁻¹' interior (range Φ) := by
    intro m U hmU
    refine ⟨hmU, ?_⟩
    simp only [mem_preimage]
    rw [proj_coverLift, ← hxc]
    exact hst.polar.nhd
  set Z := cylinderToSphere '' ((L.pathDrawing 0).U ∪ bd ClosedCylinder)
  have heZ : e ⊆ Z := by
    rintro _ ⟨_, ⟨u, -, rfl⟩, rfl⟩
    exact ⟨_, Or.inr (hcuff1 u), rfl⟩
  have hFZ : polarRimMap Φ F ∈ Z := image_mono subset_union_left hFX
  have hCZ : polarRimMap Φ (z cp) ∈ Z := heZ hcpe
  have hNZ : polarRimMap Φ (z cn) ∈ Z := heZ hcne
  -- the second wedge is off side one, by a point on side two near `Γ₂(0)`
  have hW2not : ∀ y ∈ W2, ¬ sphereSide D U₁ y := by
    rcases hdW2 with h | h
    swap
    · exact h
    exfalso
    obtain ⟨p, hpD, hpW, hpb, hpP⟩ := exists_inner_point_near_lift L hG hθ hD hBd hstrip
      (Or.inr rfl) 0 (hWo U₂ hU₂) (hΓW 2 U₂ (h₂ 0))
    have hr2 : OnSide D U₂ (radialCylinderProjection p) :=
      ⟨planeToCylinderCover p, ⟨p, hpD, rfl⟩, rfl, hpW.1⟩
    have hyΦ : cylinderToSphere (radialCylinderProjection p) ∈ range Φ := interior_subset hpW.2
    have hyZ : cylinderToSphere (radialCylinderProjection p) ∉ Z := by
      rintro ⟨r', hr', he'⟩
      rw [injective_cylinderToSphere he'] at hr'
      rcases hr' with h' | h'
      exacts [hpP h', hpb h']
    have hyx : cylinderToSphere (radialCylinderProjection p) ≠ spherePath L 0 := by
      intro h'
      rw [spherePath_zero L] at h'
      exact hpb (injective_cylinderToSphere h' ▸ by
        rw [bd_closedCylinder]; left; simp [cylinderM1Point, cylinderPoint, cylinderCuff1])
    obtain ⟨t', ht', ht1', u, hu⟩ := exists_chart_polar hst.polar hΨ hyΦ hyx
    have hne : ∀ w, polarRimMap Φ w ∈ Z → u ≠ w := by
      rintro w hwZ rfl
      exact hyZ (by rw [hu]; exact (chart_ray_mem_iff hst.polar hΨ hXC u ht' ht1').mpr hwZ)
    have hside1 : ∀ y, y = cylinderToSphere (radialCylinderProjection p) →
        ¬ sphereSide D U₁ y := by
      rintro y rfl ⟨r', he', hr'1⟩
      rw [injective_cylinderToSphere he'] at hr'1
      exact not_onSide_two_of_onSide_one L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hpP hr'1 hr2
    rcases htri t' ht' ht1' u (hne _ hFZ) (hne _ hCZ) (hne _ hNZ) with h' | h' | h'
    · exact hside1 _ rfl (hu ▸ hW1 _ h')
    · exact hside1 _ rfl (hu ▸ h _ h')
    · obtain ⟨zc, hzc, hzx⟩ := hcap _ h'
      rw [← hu] at hzx
      have h1 := norm_eq_of_cylinderToSphere_eq hzx.symm
      have h2 : (radialCylinderProjection p).1.1 ≠ 1 := fun h =>
        hpb (by rw [bd_closedCylinder]; exact Or.inl h)
      have h3 : 1 ≤ (radialCylinderProjection p).1.1 := (radialCylinderProjection p).2.1.1
      have h4 := mem_closedBall_zero_iff.mp hzc
      have h5 : 1 < (radialCylinderProjection p).1.1 := lt_of_le_of_ne h3 (Ne.symm h2)
      linarith
  -- the rays of the darts along edges off `P₁`
  refine ⟨Φ, Ψ, z, hxc ▸ hst, hΨ, fun d hd f hf hfP hdf r hr hr1 => ?_⟩
  rw [← hxc] at hd
  have hfZ : ∀ c : DrawingDart (cylinderSphereDrawing H), c.1.1 ⊆ Z → d ≠ c := by
    rintro c hcZ rfl
    obtain ⟨y, hy⟩ := hf.2.2.1.nonempty
    have hdisj := deleted_edge_disjoint_subdrawing (L.isSubdrawing 0).1 hf hfP
    obtain ⟨y', hy', he'⟩ := hcZ (hdf ▸ mem_image_of_mem cylinderToSphere hy)
    rw [injective_cylinderToSphere he'] at hy'
    rcases hy' with hyP | hyb
    · exact disjoint_left.mp hdisj hy hyP
    · exact (hf.2.1 hy).2 (hG.2.1 ⟨hyb, (hf.2.1 hy).1⟩)
  have hdF : z d ≠ F := fun h =>
    hfZ b (hbX.trans (image_mono subset_union_left)) (hst.inj _ _ hd hb (h.trans hzb.symm))
  have hdC : z d ≠ z cp := fun h => hfZ cp heZ (hst.inj _ _ hd hcpv h)
  have hdN : z d ≠ z cn := fun h => hfZ cn heZ (hst.inj _ _ hd hcnv h)
  have hiff := hst.arc_iff_block hγ hR hcpv hb hd hbcp
  rw [hzb] at hiff
  constructor
  · intro hs
    rcases hiff.mpr hs with h | h
    · exact absurd h hdF
    · exact hW1 _ (mem_wedgeSet_of_lt hr hr1 h)
  · intro hs
    rcases right_of_not_left hFne (fun h => hs (hiff.mp h)) with h | h
    · exact absurd h hdC
    · exact hW2not _ (mem_wedgeSet_of_lt hr hr1
        (hstep _ hdN (gap_le_angleTo hfin _ (hst.mem_rimDirs hγ hd)) h))

end GraphMinor.GM06
