module

public import GraphMinor.GM06.Alg57OnePathStart
import GraphMinor.GM06.Section5CoverRegion
import GraphMinor.GM06.Section5CutSheetComponent
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5CappedRegions
import GraphMinor.GM06.Section5OpenCutSheet

/-!
# The lifted incidence at inner points of the one path

For `k = 1`, let `R̃₁` be the lifted region (`cylinderCoverRegion 1 G 0`) and `R₁` the region of
the capped drawing on the sphere that it covers. At an inner point `x = P₁(t)` take a small path
chart. Its directions split into the left arc `[F, B)` and the right arc `[B, F)`. We show
(`lifted_incidence_chart`):

* `Γ₁(t)` is in the closure of `R̃₁` exactly when the corner after some direction of the left arc
  is `R₁`;
* `Γ₂(t)` is in the closure of `R̃₁` exactly when the corner after some direction of the right arc
  is `R₁`.

The reason. The left corners are on side one (`left_side_one`) and the right corners are not
(`right_wedge_not_sideOne`). Points of `R̃₁` near `Γ₁(t)` are on side one, so their images lie in
a left corner. Conversely, points of a left corner that is `R₁`, close to `x`, have lifts in `D` on
side one; these lifts are in `R̃₁` (`lift_mem_coverRegion`) and close to `Γ₁(t)`
(`exists_nbhd_lift_mem_one`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

section Lift

variable (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})

include hθ hD hBd hstrip in
/-- **Lifts of points of `R₁` in the cut disc lie in `R̃₁`.** The sheet of lifts in `D` off `P₁` is
continuous, so it maps the connected region `R₁` into one component, the one of `(1, 3π)`. -/
theorem lift_mem_coverRegion {x : ClosedCylinder} (hx : x ∈ cylinderRegion 1 G 0)
    {q : CylinderCover} (hqD : q ∈ planeToCylinderCover '' D) (hq : cylinderCoverProjection q = x) :
    q ∈ cylinderCoverRegion 1 G 0 := by
  obtain ⟨s, -, hproj, hrange⟩ := exists_open_sheet_on_single_strip L hG hθ hD hBd hstrip
  have hRP : cylinderRegion 1 G 0 ⊆ (L.pathDrawing 0).Uᶜ := fun y hy hyP =>
    (connectedComponentIn_subset _ _ hy).2 ((L.isSubdrawing 0).2 hyP)
  set T : Set ↥((L.pathDrawing 0).Uᶜ) := Subtype.val ⁻¹' cylinderRegion 1 G 0
  have hTS : Subtype.val '' T = cylinderRegion 1 G 0 := by
    rw [Subtype.image_preimage_coe]
    exact inter_eq_right.mpr hRP
  have hT : IsPreconnected T := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, hTS]
    exact isPreconnected_connectedComponentIn
  have hsT : IsPreconnected (s '' T) := hT.image s s.continuous.continuousOn
  -- the base point of `R̃₁` is the lift in `D` of the base point of `R₁`
  have hN1 : cylinderN1Point 1 0 ∈ cylinderRegion 1 G 0 :=
    mem_connectedComponentIn ⟨mem_univ _, cylinderN1Point_not_mem_U hG 0⟩
  set b : CylinderCover := (⟨1, by norm_num⟩,
    (2 * (((0 : Fin 1).val + 1 : ℕ) : ℝ) + 1) * Real.pi / ((1 : ℕ) : ℝ))
  have hbD : b ∈ planeToCylinderCover '' D := by
    refine ⟨_, inner_arc_mem L hG hBd (u := 1 / 2) ⟨by norm_num, by norm_num⟩, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [planeToCylinderCover, b]
    · simp only [planeToCylinderCover, b, Fin.isValue, Fin.val_zero, zero_add, Nat.cast_one]
      ring
  have hbN1 : cylinderCoverProjection b = cylinderN1Point 1 0 := by
    apply Subtype.ext
    apply Prod.ext
    · simp [cylinderCoverProjection, cylinderN1Point, cylinderPoint, b]
    · simp [cylinderCoverProjection, cylinderN1Point, cylinderPoint, b]
  have hmem : ∀ y : CylinderCover, y ∈ planeToCylinderCover '' D →
      cylinderCoverProjection y ∈ cylinderRegion 1 G 0 → y ∈ s '' T := by
    intro y hyD hyR
    have hy : y ∈ range s := by
      rw [hrange]
      exact ⟨hyD, hRP hyR⟩
    obtain ⟨y', rfl⟩ := hy
    refine ⟨y', ?_, rfl⟩
    change y'.1 ∈ cylinderRegion 1 G 0
    rw [← hproj]
    exact hyR
  have hb : b ∈ s '' T := hmem b hbD (hbN1 ▸ hN1)
  have hsub : s '' T ⊆ cylinderCoverProjection ⁻¹' (univ \ G.U) := by
    rintro _ ⟨y, hy, rfl⟩
    change cylinderCoverProjection (s y) ∈ univ \ G.U
    rw [hproj]
    exact connectedComponentIn_subset _ _ hy
  unfold cylinderCoverRegion
  exact hsT.subset_connectedComponentIn hb hsub (hmem q hqD (hq ▸ hx))

include hθ hD hBd hstrip in
/-- **Both lifts of the start of `P₁` are incident with `R̃₁`.** The inner cuff edge lifts to the
arc of `∂D` from `Γ₁(0)` to `Γ₂(0)`, and its inner points lie in `R̃₁`. -/
theorem coverLift_zero_mem_closure {m : ℤ} (hm : m = 1 ∨ m = 2) :
    coverLift L hG m 0 ∈ closure (cylinderCoverRegion 1 G 0) := by
  set g : ℝ → CylinderCover := fun u =>
    planeToCylinderCover ((1 : ℝ), 2 * Real.pi + 2 * Real.pi * u)
  have hg : Continuous g := continuous_planeToCylinderCover.comp (by fun_prop)
  have hsub : g '' Ioo 0 1 ⊆ cylinderCoverRegion 1 G 0 := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hu
    refine lift_mem_coverRegion L hG hθ hD hBd hstrip ?_ ⟨_, inner_arc_mem L hG hBd hu', rfl⟩
      (cylinderCoverProjection_inner_arc u hu')
    exact (initialCuffGapCurve_props hG 0).2.2.2.2 ⟨⟨u, hu'⟩, ⟨hu.1, hu.2⟩, rfl⟩
  have hcl : ∀ u ∈ Icc (0 : ℝ) 1, g u ∈ closure (cylinderCoverRegion 1 G 0) := fun u hu =>
    closure_mono hsub (hg.continuousWithinAt.mem_closure_image
      (by rw [closure_Ioo zero_ne_one]; exact hu))
  have hprops := liftedLinkageCurve_props_raw hG.1 L m
  have hval : coverLift L hG m 0 = g (m - 1) := by
    simp only [coverLift, g]
    congr 1
    apply Prod.ext
    · exact hprops.2.1
    · rw [hprops.2.2.2.1]
      push_cast
      ring
  rw [hval]
  rcases hm with rfl | rfl
  · exact hcl _ ⟨by norm_num, by norm_num⟩
  · exact hcl _ ⟨by norm_num, by norm_num⟩

end Lift

section Generic

variable {Γ : Drawing (OnePoint EuclideanPlane)} {X : Set (OnePoint EuclideanPlane)}
  {f : ℝ → OnePoint EuclideanPlane} {t : ℝ} {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
  {Ψ : C(ClosedUnitDisc, EuclideanPlane)} {F B : Circle}

/-- The rays of the two directions of a path chart lie in the path. -/
theorem IsPathChart.rim_mem (hc : IsPathChart Γ X f t Φ Ψ F B) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hX : IsGammaNice Γ X) (hfX : ∀ s ∈ Icc (0 : ℝ) 1, f s ∈ X) :
    polarRimMap Φ F ∈ X ∧ polarRimMap Φ B ∈ X := by
  obtain ⟨δo, hout⟩ := hc.out
  obtain ⟨δi, hin⟩ := hc.inn
  have ho := hout.1
  have hi := hin.1
  have h1 : 0 < (1 - t) / 2 := by linarith [ht.2]
  have h2 : 0 < t / 2 := by linarith [ht.1]
  refine ⟨rim_mem_of_runsOut hc.polar hc.hΨ hX hout (t := t + min δo ((1 - t) / 2))
    ⟨by linarith [lt_min ho h1], by linarith [min_le_left δo ((1 - t) / 2)]⟩
    (hfX _ ⟨by linarith [lt_min ho h1, ht.1], by linarith [min_le_right δo ((1 - t) / 2)]⟩),
    rim_mem_of_runsIn hc.polar hc.hΨ hX hin (t := t - min δi (t / 2))
    ⟨by linarith [min_le_left δi (t / 2)], by linarith [lt_min hi h2]⟩
    (hfX _ ⟨by linarith [min_le_right δi (t / 2)], by linarith [lt_min hi h2, ht.2]⟩)⟩

end Generic

section Incidence

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
  (hV : ∀ v ∈ (cylinderSphereDrawing H).V, ∃ a : DrawingDart (cylinderSphereDrawing H),
    dartVertex γ a = v)

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw heI hγI hV in
/-- **The right side of `P₁` is not side one.** At each inner point of `P₁`, the right wedge of
every path chart inside a set where the side does not change is off side one. Otherwise the
whole chart off `P₁` would be on side one, but there are points on side two close to `Γ₂(t)`. -/
theorem right_wedge_not_sideOne {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ : C(ClosedUnitDisc, EuclideanPlane)}
    {F B : Circle}
    (hc : IsPathChart (cylinderSphereDrawing H) (cylinderToSphere '' (L.pathDrawing 0).U)
      (spherePath L) t Φ Ψ F B)
    (hN : SideDich (cylinderToSphere '' (L.pathDrawing 0).U) (sphereSide D U₁) (range Φ)) :
    ∀ x ∈ wedgeSet Ψ B (angleTo B F), ¬ sphereSide D U₁ x := by
  have hX := isGammaNice_spherePath L hGH
  have hfX : ∀ s ∈ Icc (0 : ℝ) 1, spherePath L s ∈ cylinderToSphere '' (L.pathDrawing 0).U :=
    fun s hs => (image_spherePath L) ▸ ⟨s, hs, rfl⟩
  obtain ⟨hFX, hBX⟩ := hc.rim_mem ht hX hfX
  have hleft := (left_side_one L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw heI
    hγI hV).1 ht hc hN
  have hdisj : Disjoint (wedgeSet Ψ B (angleTo B F)) (cylinderToSphere '' (L.pathDrawing 0).U) := by
    apply disjoint_wedgeSet hc.polar hc.hΨ hX
    intro θ hθ hmem
    have hθ2 : θ ∈ Ioc 0 (2 * Real.pi) := ⟨hθ.1, hθ.2.le.trans (angleTo_le B F)⟩
    rcases hc.dirs _ hmem with h1 | h1
    · have := angleTo_eq hθ2 h1.symm
      linarith [hθ.2]
    · have := angleTo_eq hθ2 h1.symm
      rw [angleTo_self] at this
      linarith [hθ.2, angleTo_le B F]
  rcases hN _ (wedgeSet_subset_range hc.hΨ B _) (isPreconnected_wedgeSet B _) hdisj with hall | hall
  swap
  · exact hall
  exfalso
  set tt : unitInterval := ⟨t, Ioo_subset_Icc_self ht⟩
  set W : Set CylinderCover := U₂ ∩
    (fun q => cylinderToSphere (cylinderCoverProjection q)) ⁻¹' interior (range Φ)
  have hW : IsOpen W := hU₂.inter (isOpen_interior.preimage
    (continuous_cylinderToSphere.comp continuous_cylinderCoverProjection))
  have hΓW : coverLift L hG 2 tt ∈ W := by
    refine ⟨h₂ tt, ?_⟩
    simp only [mem_preimage]
    rw [proj_coverLift, ← spherePath_of_mem L (Ioo_subset_Icc_self ht)]
    exact hc.polar.nhd
  obtain ⟨p, hpD, hpW, -, hpP⟩ :=
    exists_inner_point_near_lift L hG hθ hD hBd hstrip (Or.inr rfl) tt hW hΓW
  set x := radialCylinderProjection p
  have hx2 : OnSide D U₂ x := ⟨planeToCylinderCover p, ⟨p, hpD, rfl⟩, rfl, hpW.1⟩
  have hyΦ : cylinderToSphere x ∈ range Φ := interior_subset hpW.2
  have hyX : cylinderToSphere x ∉ cylinderToSphere '' (L.pathDrawing 0).U := by
    rintro ⟨x', hx', he⟩
    exact hpP (injective_cylinderToSphere he ▸ hx')
  have hyc : cylinderToSphere x ≠ spherePath L t := fun h =>
    hyX (h ▸ hfX t (Ioo_subset_Icc_self ht))
  obtain ⟨r, hr, hr1, u, hu⟩ := exists_chart_polar hc.polar hc.hΨ hyΦ hyc
  have huF : u ≠ F := by
    rintro rfl
    exact hyX (by rw [hu]; exact (chart_ray_mem_iff hc.polar hc.hΨ hX u hr hr1).mpr hFX)
  have huB : u ≠ B := by
    rintro rfl
    exact hyX (by rw [hu]; exact (chart_ray_mem_iff hc.polar hc.hΨ hX u hr hr1).mpr hBX)
  have hyQ : sphereSide D U₁ (cylinderToSphere x) := by
    rw [hu]
    by_cases hl : angleTo F u < angleTo F B
    · exact hleft _ (mem_wedgeSet_of_lt hr hr1 hl)
    · rcases right_of_not_left hc.ne (by rintro (h | h); exacts [huF h, hl h]) with h | h
      · exact absurd h huB
      · exact hall _ (mem_wedgeSet_of_lt hr hr1 h)
  obtain ⟨x', hx'e, hx'1⟩ := hyQ
  rw [injective_cylinderToSphere hx'e] at hx'1
  exact not_onSide_two_of_onSide_one L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hpP hx'1 hx2

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw heI hγI hV in
/-- **The lifted incidence at inner points of `P₁`, in a chart.** Near an inner point `x = P₁(t)`
every path chart has this property. The lift `Γ₁(t)` is in the closure of `R̃₁` exactly when the
corner after some direction of the left arc `[F, B)` is the region `R₁`, and `Γ₂(t)` is in the
closure of `R̃₁` exactly when the corner after some direction of the right arc `[B, F)` is `R₁`. -/
theorem lifted_incidence_chart {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ O : Set (OnePoint EuclideanPlane), IsOpen O ∧ spherePath L t ∈ O ∧
      ∀ {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ : C(ClosedUnitDisc, EuclideanPlane)}
        {F B : Circle},
        IsPathChart (cylinderSphereDrawing H) (cylinderToSphere '' (L.pathDrawing 0).U)
          (spherePath L) t Φ Ψ F B → range Φ ⊆ O →
        (coverLift L hG 1 ⟨t, Ioo_subset_Icc_self ht⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
          ∃ w ∈ rimDirs (cylinderSphereDrawing H) Φ, (w = F ∨ angleTo F w < angleTo F B) ∧
            cornerRegion (cylinderSphereDrawing H) Φ w =
              cylinderToSphere '' (cylinderRegion 1 G 0 \ bd ClosedCylinder)) ∧
        (coverLift L hG 2 ⟨t, Ioo_subset_Icc_self ht⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
          ∃ w ∈ rimDirs (cylinderSphereDrawing H) Φ, (w = B ∨ angleTo B w < angleTo B F) ∧
            cornerRegion (cylinderSphereDrawing H) Φ w =
              cylinderToSphere '' (cylinderRegion 1 G 0 \ bd ClosedCylinder)) := by
  set tt : unitInterval := ⟨t, Ioo_subset_Icc_self ht⟩
  have h0 : tt ≠ 0 := fun h => ht.1.ne' (congrArg Subtype.val h)
  have h1 : tt ≠ 1 := fun h => ht.2.ne (congrArg Subtype.val h)
  have hxt : spherePath L t = cylinderToSphere (L.curve 0 tt) :=
    spherePath_of_mem L (Ioo_subset_Icc_self ht)
  obtain ⟨N, hN, hxN, hdich, hor⟩ :=
    sphere_sideDich' L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ h0 h1
  refine ⟨N, hN, hxt ▸ hxN, fun {Φ Ψ F B} hc hsub => ?_⟩
  have hND := hdich.mono hsub
  have hleft := (left_side_one L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw heI
    hγI hV).1 ht hc hND
  have hright := right_wedge_not_sideOne L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR
    hccw heI hγI hV ht hc hND
  set R₁ := cylinderToSphere '' (cylinderRegion 1 G 0 \ bd ClosedCylinder)
  have hreg : R₁ ∈ (cylinderSphereDrawing H).R :=
    image_region_sdiff_boundary_mem_sphere_regions hFU (cylinderRegion_mem_regions hG 0)
  have hRG : ∀ x ∈ cylinderRegion 1 G 0, x ∉ G.U := fun x hx =>
    GM11.region_subset (cylinderRegion_mem_regions hG 0) hx
  have hcU : spherePath L t ∈ (cylinderSphereDrawing H).U :=
    spherePath_subset_U L hGH ((image_spherePath L) ▸ ⟨t, Ioo_subset_Icc_self ht, rfl⟩)
  have hR₁U : ∀ y ∈ R₁, y ∉ (cylinderSphereDrawing H).U := fun y hy hyU =>
    GM11.region_subset hreg hy hyU
  -- A point of `R̃₁` near a lift of `x`, off the cuffs and over the chart, lies in a corner
  -- whose region is `R₁`.
  have hcorner : ∀ q ∈ cylinderCoverRegion 1 G 0,
      cylinderCoverProjection q ∉ bd ClosedCylinder →
      cylinderToSphere (cylinderCoverProjection q) ∈ range Φ →
      ∃ w ∈ rimDirs (cylinderSphereDrawing H) Φ,
        cylinderToSphere (cylinderCoverProjection q) ∈ cornerSet (cylinderSphereDrawing H) Φ Ψ w ∧
        cornerRegion (cylinderSphereDrawing H) Φ w = R₁ := by
    intro q hq hqb hqΦ
    have hxR := image_cylinderCoverRegion_subset_region 1 G 0 ⟨q, hq, rfl⟩
    have hyR : cylinderToSphere (cylinderCoverProjection q) ∈ R₁ := ⟨_, ⟨hxR, hqb⟩, rfl⟩
    have hyU := hR₁U _ hyR
    obtain ⟨w, hw, hyw⟩ := exists_mem_cornerSet hc.polar hc.hΨ hc.fin ⟨F, hc.F_mem⟩ hqΦ
      (fun h => hyU (h ▸ hcU)) hyU
    exact ⟨w, hw, hyw, GM11.region_eq_of_mem (cornerRegion_mem hc.polar hc.hΨ hc.fin w) hreg
      (image_cone_subset_cornerRegion hc.polar hc.hΨ hc.fin w hyw) hyR⟩
  -- The open set of lifts over the chart, off the cuffs, on a given side.
  have hWo : ∀ U : Set CylinderCover, IsOpen U → IsOpen (U ∩
      (fun q => cylinderToSphere (cylinderCoverProjection q)) ⁻¹' interior (range Φ) ∩
      cylinderCoverProjection ⁻¹' (bd ClosedCylinder)ᶜ) := fun U hU' =>
    (hU'.inter (isOpen_interior.preimage
      (continuous_cylinderToSphere.comp continuous_cylinderCoverProjection))).inter
      ((isClosed_bd ClosedCylinder).isOpen_compl.preimage continuous_cylinderCoverProjection)
  have hΓW : ∀ m : ℤ, ∀ U : Set CylinderCover, coverLift L hG m tt ∈ U → coverLift L hG m tt ∈ U ∩
      (fun q => cylinderToSphere (cylinderCoverProjection q)) ⁻¹' interior (range Φ) ∩
      cylinderCoverProjection ⁻¹' (bd ClosedCylinder)ᶜ := by
    intro m U hmU
    refine ⟨⟨hmU, ?_⟩, ?_⟩
    · simp only [mem_preimage]
      rw [proj_coverLift, ← hxt]
      exact hc.polar.nhd
    · simp only [mem_preimage, mem_compl_iff]
      rw [proj_coverLift]
      exact curve_notMem_bd L hG h0 h1
  -- Open sets of the cylinder around `P₁(t)` come from open sets of the sphere.
  have hopen : ∀ M : Set ClosedCylinder, IsOpen M → L.curve 0 tt ∈ M →
      ∃ V : Set (OnePoint EuclideanPlane), IsOpen V ∧ spherePath L t ∈ V ∧
        cylinderToSphere ⁻¹' V = M := by
    intro M hM hxM
    obtain ⟨V, hV, hVM⟩ := isClosedEmbedding_cylinderToSphere.isInducing.isOpen_iff.mp hM
    refine ⟨V, hV, ?_, hVM⟩
    rw [hxt]
    change L.curve 0 tt ∈ cylinderToSphere ⁻¹' V
    rw [hVM]; exact hxM
  constructor
  · constructor
    · intro hcl
      obtain ⟨q, ⟨⟨hqU, hqΦ⟩, hqb⟩, hq⟩ :=
        _root_.mem_closure_iff.mp hcl _ (hWo U₁ hU₁) (hΓW 1 U₁ (h₁ tt))
      obtain ⟨w, hw, hyw, hcr⟩ := hcorner q hq hqb (interior_subset hqΦ)
      refine ⟨w, hw, ?_, hcr⟩
      by_contra hl
      exact hright _ (cornerSet_subset_wedgeSet_of_left hc.fin hc.F_mem (right_of_not_left hc.ne hl)
        hyw) ⟨_, rfl, q, closure_cylinderCoverRegion_subset_single_strip L hG hθ hD hBd hstrip
          (subset_closure hq), rfl, hqU⟩
    · rintro ⟨w, -, hl, hcr⟩
      rw [_root_.mem_closure_iff]
      intro W hW hΓ
      obtain ⟨M, hM, hxM, hlift⟩ := exists_nbhd_lift_mem_one L hG hθ hD hBd hstrip hU₂ h₂ hU tt hW hΓ
      obtain ⟨V, hV, hcV, hVM⟩ := hopen M hM hxM
      obtain ⟨y, hyC, hyV⟩ := cornerSet_meets_nhds hc.polar hc.hΨ hc.fin w hV hcV
      have hyR : y ∈ R₁ := hcr ▸ image_cone_subset_cornerRegion hc.polar hc.hΨ hc.fin w hyC
      obtain ⟨x, ⟨hxR, -⟩, rfl⟩ := hyR
      obtain ⟨x', hx'e, q, hqD, hqx, hqU⟩ :=
        hleft _ (cornerSet_subset_wedgeSet_of_left hc.fin hc.B_mem hl hyC)
      rw [injective_cylinderToSphere hx'e] at hqx
      have hxM' : x ∈ M := by rw [← hVM]; exact hyV
      exact ⟨q, hlift q hqD (hqx ▸ hxM') hqU,
        lift_mem_coverRegion L hG hθ hD hBd hstrip hxR hqD hqx⟩
  · constructor
    · intro hcl
      obtain ⟨q, ⟨⟨hqU, hqΦ⟩, hqb⟩, hq⟩ :=
        _root_.mem_closure_iff.mp hcl _ (hWo U₂ hU₂) (hΓW 2 U₂ (h₂ tt))
      obtain ⟨w, hw, hyw, hcr⟩ := hcorner q hq hqb (interior_subset hqΦ)
      refine ⟨w, hw, ?_, hcr⟩
      by_contra hr
      obtain ⟨x', hx'e, hx'1⟩ :=
        hleft _ (cornerSet_subset_wedgeSet_of_left hc.fin hc.B_mem (right_of_not_left hc.ne.symm hr)
          hyw)
      rw [injective_cylinderToSphere hx'e] at hx'1
      have hxR := image_cylinderCoverRegion_subset_region 1 G 0 ⟨q, hq, rfl⟩
      exact not_onSide_two_of_onSide_one L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂
        (fun h => hRG _ hxR ((L.isSubdrawing 0).2 h)) hx'1
        ⟨q, closure_cylinderCoverRegion_subset_single_strip L hG hθ hD hBd hstrip
          (subset_closure hq), rfl, hqU⟩
    · rintro ⟨w, -, hr, hcr⟩
      rw [_root_.mem_closure_iff]
      intro W hW hΓ
      obtain ⟨M, hM, hxM, hlift⟩ := exists_nbhd_lift_mem_two L hG hθ hD hBd hstrip hU₁ h₁ hU tt hW hΓ
      obtain ⟨V, hV, hcV, hVM⟩ := hopen M hM hxM
      obtain ⟨y, hyC, hyV⟩ := cornerSet_meets_nhds hc.polar hc.hΨ hc.fin w hV hcV
      have hyR : y ∈ R₁ := hcr ▸ image_cone_subset_cornerRegion hc.polar hc.hΨ hc.fin w hyC
      have hyX : y ∉ cylinderToSphere '' (L.pathDrawing 0).U := fun h =>
        hR₁U y hyR (spherePath_subset_U L hGH h)
      have hy1 := hright _ (cornerSet_subset_wedgeSet_of_left hc.fin hc.F_mem hr hyC)
      have hy2 := (hor y (hsub (cornerSet_subset_range hc.hΨ w hyC)) hyX).resolve_left hy1
      obtain ⟨x, ⟨hxR, -⟩, rfl⟩ := hyR
      obtain ⟨x', hx'e, q, hqD, hqx, hqU⟩ := hy2
      rw [injective_cylinderToSphere hx'e] at hqx
      have hxM' : x ∈ M := by rw [← hVM]; exact hyV
      exact ⟨q, hlift q hqD (hqx ▸ hxM') hqU,
        lift_mem_coverRegion L hG hθ hD hBd hstrip hxR hqD hqx⟩

end Incidence

end GraphMinor.GM06
