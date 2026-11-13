module

public import GraphMinor.GM06.Alg57FaceCorner
public import GraphMinor.GM06.Alg57ExpChart
public import GraphMinor.GM06.Section5CappedRegions
public import GraphMinor.GM06.Section5RegionPoint
public import GraphMinor.GM06.Section5BoundaryGap

/-!
# The face on the left of the reverse inner cuff dart

Lemma 11 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`) selects the face orbit `Fᵢ` of
the reverse inner cuff dart `c̄ᵢ`, and uses that its region is the region `Rᵢ` of the cylinder. Here
we prove this for the drawing `G⁺` of the cylinder with both cuffs, in the sphere
(`face_reverse_inner_gap`): the region of the orbit of `c̄ᵢ` is the image of `Rᵢ` off the cuffs.

This is where the orientation of the plane enters. We read the corner on the left of `c̄ᵢ` in
the explicit exponential chart at the midpoint `(1, (2i+1)π/k)` of the inner gap
(`Alg57ExpChart`). The dart `c̄ᵢ` runs clockwise along the inner cuff, so its left is the outside
of the inner cuff circle, which is the cylinder.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology Real GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A point of the cylinder in the complex coordinates of the plane. -/
theorem cylinderToSphere_cylinderPoint (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) (θ : ℝ) :
    cylinderToSphere (cylinderPoint r hr θ) =
      toSph (((r / 2 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  change ((cylToPlane (cylinderPoint r hr θ) : EuclideanPlane) : OnePoint EuclideanPlane) =
    ((complexPlane (((r / 2 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) : EuclideanPlane) :
      OnePoint EuclideanPlane)
  congr 1
  rw [← Complex.real_smul, map_smul]
  rw [cylToPlane_apply]
  simp [cylinderPoint, Circle.coe_exp]

/-- Equal points in the cylinder picture and the complex picture have the same norm. -/
theorem norm_eq_of_cylinderToSphere_eq {p : ClosedCylinder} {z : ℂ}
    (h : cylinderToSphere p = toSph z) : ‖z‖ = p.1.1 / 2 := by
  have h1 : cylToPlane p = complexPlane z := OnePoint.coe_injective h
  rw [← norm_cylToPlane, h1, LinearIsometryEquiv.norm_map]

/-- The norm of `q · exp (l w)`. -/
theorem norm_expMap (q : ℂ) (l : ℝ) (w : ℂ) : ‖expMap q l w‖ = ‖q‖ * Real.exp (l * w.re) := by
  rw [expMap, norm_mul, Complex.norm_exp]
  simp

section Gap

variable {k : ℕ} (i : Fin k)

/-- The angle of the midpoint of the `i`th inner gap. -/
noncomputable def gapMidAngle (k : ℕ) (i : Fin k) : ℝ := (2 * ((i.1 + 1 : ℕ) : ℝ) + 1) * π / k

/-- The midpoint of the `i`th inner gap, as a complex number of norm `1/2`. -/
noncomputable def gapMid (k : ℕ) (i : Fin k) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) * Complex.exp ((gapMidAngle k i : ℂ) * Complex.I)

theorem gapMid_ne_zero : gapMid k i ≠ 0 := by
  unfold gapMid
  exact mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)

theorem norm_gapMid : ‖gapMid k i‖ = 1 / 2 := by
  rw [gapMid, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by norm_num)]

theorem toSph_gapMid : toSph (gapMid k i) = cylinderToSphere (cylinderN1Point k i) := by
  rw [cylinderN1Point, cylinderToSphere_cylinderPoint, gapMid, gapMidAngle]

/-- The points `q · exp w` near the gap midpoint `q` miss the graph `G`. -/
theorem exists_ball_gapMid_notMem {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) :
    ∃ η > 0, ∀ w : ℂ, ‖w‖ < η →
      toSph (gapMid k i * Complex.exp w) ∉ cylinderToSphere '' G.U := by
  have hS : IsClosed (cylinderToSphere '' G.U) :=
    isClosedEmbedding_cylinderToSphere.isClosedMap _ G.isClosed_U
  have hq : toSph (gapMid k i) ∉ cylinderToSphere '' G.U := by
    rw [toSph_gapMid]
    rintro ⟨p, hp, hpq⟩
    rw [injective_cylinderToSphere hpq] at hp
    exact cylinderN1Point_not_mem_U hG i hp
  let f : ℂ → OnePoint EuclideanPlane := fun w => toSph (gapMid k i * Complex.exp w)
  have hf : Continuous f := isOpenEmbedding_toSph.continuous.comp (by fun_prop)
  have h0 : (0 : ℂ) ∈ f ⁻¹' (cylinderToSphere '' G.U)ᶜ := by
    simp only [mem_preimage, mem_compl_iff, f, Complex.exp_zero, mul_one]
    exact hq
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp (hS.isOpen_compl.preimage hf) 0 h0
  exact ⟨η, hη, fun w hw => hball (mem_ball_zero_iff.mpr hw)⟩

/-- A point of the inner cuff in the complex coordinates. -/
theorem gapMid_mul_exp_I (s : ℝ) :
    gapMid k i * Complex.exp ((s : ℂ) * Complex.I) =
      ((1 / 2 : ℝ) : ℂ) * Complex.exp (((gapMidAngle k i + s : ℝ) : ℂ) * Complex.I) := by
  rw [gapMid, mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

/-- A point of the `i`th inner gap curve in the complex coordinates. -/
theorem cylinderToSphere_initialCuffGapCurve (u : I) :
    cylinderToSphere (initialCuffGapCurve k i u) = toSph (((1 / 2 : ℝ) : ℂ) *
      Complex.exp (((2 * (((i.1 + 1 : ℕ) : ℝ) + (u : ℝ)) * π / k : ℝ) : ℂ) * Complex.I)) := by
  show cylinderToSphere (cylinderPoint 1 (by norm_num)
    (2 * (((i.1 + 1 : ℕ) : ℝ) + (u : ℝ)) * π / k)) = _
  rw [cylinderToSphere_cylinderPoint]

/-- **The exponential chart at the midpoint of an inner gap.** For small `l`, the drawing `G⁺`
meets the chart only along the imaginary axis, and there it is in the gap edge. Also the points
`q · exp w` with `‖w‖ ≤ l` miss `G`. -/
theorem exists_gap_expChart {G F : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) :
    ∃ l : ℝ, 0 < l ∧ l < 1 ∧ l < π / k ∧ l < Real.log 2 ∧
      (∀ w : ℂ, ‖w‖ ≤ l → toSph (gapMid k i * Complex.exp w) ∉ cylinderToSphere '' G.U) ∧
      (∀ w : ℂ, ‖w‖ ≤ 1 → toSph (expMap (gapMid k i) l w) ∈ (cylinderSphereDrawing F).U →
        w.re = 0) ∧
      (∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 0 → w.re = 0 → toSph (expMap (gapMid k i) l w) ∈
        cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) := by
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr hG.1
  obtain ⟨η, hη, hball⟩ := exists_ball_gapMid_notMem i hG
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set l := min (min (η / 2) (1 / 2)) (min (π / (2 * k)) (Real.log 2 / 2)) with hl
  have hl1 : l ≤ η / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hl2 : l ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hl3 : l ≤ π / (2 * k) := (min_le_right _ _).trans (min_le_left _ _)
  have hl4 : l ≤ Real.log 2 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hl0 : 0 < l := lt_min (lt_min (half_pos hη) (by norm_num))
    (lt_min (div_pos Real.pi_pos (by positivity)) (half_pos hlog2))
  have hlπ : l < π / k := by
    have : π / (2 * k) < π / k := by
      rw [div_lt_div_iff₀ (by positivity) hk]; nlinarith [Real.pi_pos]
    linarith
  refine ⟨l, hl0, by linarith, hlπ, by linarith, fun w hw => hball w (by linarith), ?_, ?_⟩
  · intro w hw hmem
    rw [cylinderSphereDrawing_U, hFU] at hmem
    obtain ⟨p, hp, hpe⟩ := hmem
    have hlw : ‖(l : ℂ) * w‖ ≤ l := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hl0.le]
      nlinarith [norm_nonneg w]
    rcases hp with hpG | hpbd
    · exact absurd ⟨p, hpG, hpe⟩ (hball _ (by linarith))
    · have hn := norm_eq_of_cylinderToSphere_eq hpe
      rw [norm_expMap, norm_gapMid] at hn
      have hre1 : w.re ≤ 1 := (Complex.re_le_norm w).trans hw
      rw [bd_closedCylinder] at hpbd
      rcases hpbd with h1 | h2
      · have h1' : p.1.1 = 1 := h1
        rw [h1'] at hn
        have he1 : Real.exp (l * w.re) = 1 := by linarith
        have := Real.exp_eq_one_iff (l * w.re) |>.mp he1
        exact (mul_eq_zero.mp this).resolve_left hl0.ne'
      · have h2' : p.1.1 = 2 := h2
        rw [h2'] at hn
        have he2 : Real.exp (l * w.re) = 2 := by linarith
        have hlog := congrArg Real.log he2
        rw [Real.log_exp] at hlog
        have : l * w.re ≤ l := by nlinarith
        linarith
  · intro w hw hw0 hre
    have hwI : w = ((w.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hre]
    have him : |w.im| ≤ 1 := (Complex.abs_im_le_norm w).trans hw
    have hls : |l * w.im| ≤ l := by
      rw [abs_mul, abs_of_pos hl0]; nlinarith [abs_nonneg w.im]
    set u : ℝ := 1 / 2 + l * w.im * k / (2 * π) with hu
    have hπ := Real.pi_pos
    have hbound : |l * w.im * k / (2 * π)| < 1 / 2 := by
      rw [abs_div, abs_mul, abs_of_pos hk, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
        div_lt_iff₀ (by positivity)]
      have : l * k < π := by rw [lt_div_iff₀ hk] at hlπ; linarith
      nlinarith [abs_nonneg (l * w.im)]
    have hu0 : 0 < u := by rw [hu]; linarith [neg_abs_le (l * w.im * k / (2 * π))]
    have hu1 : u < 1 := by rw [hu]; linarith [le_abs_self (l * w.im * k / (2 * π))]
    let v : I := ⟨u, Set.mem_Icc.mpr ⟨hu0.le, hu1.le⟩⟩
    have hv : (v : ℝ) = u := rfl
    have hang : 2 * (((i.1 + 1 : ℕ) : ℝ) + (v : ℝ)) * π / k = gapMidAngle k i + l * w.im := by
      rw [hv, gapMidAngle, hu]
      field_simp
      ring
    refine ⟨initialCuffGapCurve k i v, ⟨v, ⟨hu0, hu1⟩, rfl⟩, ?_⟩
    rw [cylinderToSphere_initialCuffGapCurve, expMap, hwI,
      show (l : ℂ) * (((w.im : ℝ) : ℂ) * Complex.I) = (((l * w.im) : ℝ) : ℂ) * Complex.I by
        push_cast; ring, gapMid_mul_exp_I, hang]

/-- The point at radius `exp l` above the gap midpoint lies in `Rᵢ` off the cuffs, when the
radial segment up to it misses `G`. -/
theorem exp_point_mem_region {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    {l : ℝ} (hl0 : 0 < l) (hl2 : l < Real.log 2)
    (hnear : ∀ w : ℂ, ‖w‖ ≤ l → toSph (gapMid k i * Complex.exp w) ∉ cylinderToSphere '' G.U) :
    toSph (expMap (gapMid k i) l 1) ∈
      cylinderToSphere '' (cylinderRegion k G i \ bd ClosedCylinder) := by
  have hmem : ∀ s : Icc (0 : ℝ) l, Real.exp s.1 ∈ Icc (1 : ℝ) 2 := fun s =>
    ⟨Real.one_le_exp s.2.1, by
      have := Real.exp_le_exp.mpr (s.2.2.trans hl2.le)
      rwa [Real.exp_log (by norm_num)] at this⟩
  let g : Icc (0 : ℝ) l → ClosedCylinder := fun s =>
    cylinderPoint (Real.exp s.1) (hmem s) (gapMidAngle k i)
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    exact (Real.continuous_exp.comp continuous_subtype_val).prodMk continuous_const
  have hgs : ∀ s : Icc (0 : ℝ) l,
      cylinderToSphere (g s) = toSph (gapMid k i * Complex.exp (s.1 : ℂ)) := by
    intro s
    rw [cylinderToSphere_cylinderPoint, gapMid, Complex.ofReal_div, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have : PreconnectedSpace (Icc (0 : ℝ) l) := Subtype.preconnectedSpace isPreconnected_Icc
  have hconn : IsPreconnected (range g) := isPreconnected_range hg
  let s0 : Icc (0 : ℝ) l := ⟨0, le_rfl, hl0.le⟩
  let s1 : Icc (0 : ℝ) l := ⟨l, hl0.le, le_rfl⟩
  have hg0 : g s0 = cylinderN1Point k i := by
    apply Subtype.ext
    simp [g, s0, cylinderPoint, cylinderN1Point, gapMidAngle]
  have hsub : range g ⊆ univ \ G.U := by
    rintro _ ⟨s, rfl⟩
    refine ⟨mem_univ _, fun hU => hnear (s.1 : ℂ) ?_ ⟨g s, hU, hgs s⟩⟩
    rw [Complex.norm_real, Real.norm_of_nonneg s.2.1]
    exact s.2.2
  have hin : g s1 ∈ cylinderRegion k G i := by
    have := hconn.subset_connectedComponentIn ⟨s0, rfl⟩ hsub ⟨s1, rfl⟩
    rwa [hg0] at this
  have hnotbd : g s1 ∉ bd ClosedCylinder := by
    rw [bd_closedCylinder]
    have h1 : 1 < Real.exp l := Real.one_lt_exp_iff.mpr hl0
    have h2 : Real.exp l < 2 := by
      have := Real.exp_lt_exp.mpr hl2
      rwa [Real.exp_log (by norm_num)] at this
    rintro (h | h)
    · have h' : Real.exp l = 1 := h
      linarith
    · have h' : Real.exp l = 2 := h
      linarith
  refine ⟨g s1, ⟨hin, hnotbd⟩, ?_⟩
  rw [hgs s1, expMap, mul_one]

/-- **The face of the reverse inner cuff dart is `Rᵢ`.** Let `L` match the face orbits of a
rotation of the drawing `G⁺` in the sphere with its regions, so that the region of the orbit of a
dart is the corner on its left in any chart along its edge (as `sphere_faceOrbits_ccw_corner`
gives). Then the region of the orbit of the reverse `i`th inner gap dart `c̄ᵢ` is the image of
the cylinder region `Rᵢ` off the cuffs. -/
theorem face_reverse_inner_gap {G F : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    (hFU : F.U = G.U ∪ bd ClosedCylinder)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {R : DartRotation (DrawingDart (cylinderSphereDrawing F))}
    (he : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈ (cylinderSphereDrawing F).E)
    (hγe : ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
      cylinderToSphere (initialCuffGapCurve k i t))
    (L : R.Faces → (cylinderSphereDrawing F).R)
    (hL : ∀ (d : DrawingDart (cylinderSphereDrawing F)) (a : ℝ), a ∈ Ioo (0 : ℝ) 1 →
      ∀ (Φm : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (Ψm : C(ClosedUnitDisc, EuclideanPlane)),
      IsPolar (cylinderSphereDrawing F) (dartCurve γ d a) Φm →
      (∀ x, Φm x = (Ψm x : OnePoint EuclideanPlane)) →
      0 < wind (fun w : Circle => chartC Ψm w) (chartC Ψm 0) →
      (rimDirs (cylinderSphereDrawing F) Φm).Finite →
      ∀ (Wm : Circle), Wm ∈ rimDirs (cylinderSphereDrawing F) Φm → ∀ (δ : ℝ),
      RunsOut Ψm Wm (dartCurve γ d) a δ →
      (L (R.faceOf d)).1 = cornerRegion (cylinderSphereDrawing F) Φm Wm) :
    (L (R.faceOf ⟨(cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1), true), he⟩)).1 =
      cylinderToSphere '' (cylinderRegion k G i \ bd ClosedCylinder) := by
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr hG.1
  have hπ := Real.pi_pos
  obtain ⟨l, hl0, hl1, hlπ, hl2, hnear, hU, hE⟩ := exists_gap_expChart i hG hFU
  set e := cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) with he_def
  set d : DrawingDart (cylinderSphereDrawing F) := ⟨(e, true), he⟩ with hd
  have hdc : ∀ t (ht : t ∈ Icc (0 : ℝ) 1), dartCurve γ d t =
      cylinderToSphere (initialCuffGapCurve k i ⟨1 - t, Set.mem_Icc.mpr
        ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩) := by
    intro t ht
    have h1 : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp only [dartCurve, d, if_true]
    rw [edgeCurve_of_mem γ e h1, hγe]
  have hmid : dartCurve γ d (1 / 2) = toSph (gapMid k i) := by
    rw [hdc _ ⟨by norm_num, by norm_num⟩, cylinderToSphere_initialCuffGapCurve, gapMid]
    congr 4
    simp only [gapMidAngle]
    field_simp
    ring
  have hpolar := expChart_isPolar (gapMid_ne_zero i) hl0 hl1 he hU hE
  rw [← hmid] at hpolar
  set δ : ℝ := min (1 / 2) (l * k / (4 * π)) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ l * k / (4 * π) := min_le_right _ _
  have hμδ : 2 * π / k * δ < l := by
    calc 2 * π / k * δ ≤ 2 * π / k * (l * k / (4 * π)) := by gcongr
      _ = l / 2 := by field_simp; ring
      _ < l := half_lt_self hl0
  have hruns : RunsOut (expChartΨ (gapMid k i) l) (Circle.exp (-(π / 2))) (dartCurve γ d)
      (1 / 2) δ := by
    refine runsOut_expChart_neg hl0 hδ0 (by positivity) hμδ fun t ht => ?_
    rw [hdc t ⟨by linarith [ht.1], by linarith [ht.2]⟩, cylinderToSphere_initialCuffGapCurve,
      show -(((2 * π / k * (t - 1 / 2) : ℝ)) : ℂ) * Complex.I =
        (((-(2 * π / k * (t - 1 / 2))) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      gapMid_mul_exp_I]
    congr 4
    simp only [gapMidAngle]
    field_simp
    ring
  have hfin : (rimDirs (cylinderSphereDrawing F) (expChart (gapMid k i) l)).Finite := by
    rw [rimDirs_expChart he hU hE]; exact toFinite _
  have hW : Circle.exp (-(π / 2)) ∈ rimDirs (cylinderSphereDrawing F) (expChart (gapMid k i) l) := by
    rw [rimDirs_expChart he hU hE]; exact mem_insert _ _
  rw [hL d (1 / 2) ⟨by norm_num, by norm_num⟩ _ _ hpolar (expChart_eq _ l)
    (wind_expChartΨ_pos (gapMid_ne_zero i) hl0 hl1) hfin _ hW δ hruns,
    cornerRegion_expChart_neg he hU hE]
  have hR' := image_region_sdiff_boundary_mem_sphere_regions hFU (cylinderRegion_mem_regions hG i)
  have hx := exp_point_mem_region i hG hl0 hl2 hnear
  have hxU : toSph (expMap (gapMid k i) l 1) ∉ (cylinderSphereDrawing F).U :=
    region_subset hR' hx
  exact region_eq_of_mem ((mem_R_iff _).mpr ⟨_, hxU, rfl⟩) hR'
    (mem_connectedComponentIn ⟨mem_univ _, hxU⟩) hx

end Gap

end GraphMinor.GM06
