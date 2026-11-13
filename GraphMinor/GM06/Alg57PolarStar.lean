module

public import GraphMinor.GM06.Alg57ChartStar
public import GraphMinor.GM06.Alg57InputRep
public import GraphMinor.GM06.Section5PolarShrink
public import GraphMinor.GM11.Regions
public import GraphMinor.GM11.NiceStatements
import GraphMinor.Surface.InvarianceOfDomain

/-!
# Polar charts of a drawing in the sphere, read in `ℂ`

Lemma 1 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`) says that near a vertex the
drawing is a star of straight spokes. In the library this is a polar chart `Φ` (`IsPolar`):
each ray of the chart lies in one atom of the drawing. We read a polar chart of a drawing in
the sphere `OnePoint EuclideanPlane` that misses the point at infinity as a map `χ : ℂ → ℂ`
(`chartC`), so that the results on sectors in `ℂ` apply.

The rim directions in `U(Γ)` form the star `rimDirs`. When it is finite, the corner after a
direction `w` of the star lies in one region `cornerRegion` (`image_cone_subset_cornerRegion`).
A region whose closure meets a ray of the star is one of the two corners next to that ray
(`region_eq_corner_of_ray`), and a region whose closure contains the centre is a corner
(`exists_corner_of_closure_centre`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-! ### The plane in the sphere, and the closed disc in `ℂ` -/

/-- The point of the sphere at a complex number. -/
noncomputable def toSph (z : ℂ) : OnePoint EuclideanPlane :=
  ((complexPlane z : EuclideanPlane) : OnePoint EuclideanPlane)

theorem isOpenEmbedding_toSph : IsOpenEmbedding toSph :=
  OnePoint.isOpenEmbedding_coe.comp complexPlane.toHomeomorph.isOpenEmbedding

theorem continuous_toSph : Continuous toSph := isOpenEmbedding_toSph.continuous

theorem toSph_injective : Function.Injective toSph := isOpenEmbedding_toSph.injective

/-- The radial retraction of `ℂ` onto the closed unit disc. -/
noncomputable def ballClamp (z : ℂ) : ℂ := (((max 1 ‖z‖)⁻¹ : ℝ) : ℂ) * z

theorem continuous_ballClamp : Continuous ballClamp := by
  unfold ballClamp
  have : Continuous fun z : ℂ => (max 1 ‖z‖)⁻¹ :=
    (continuous_const.max continuous_norm).inv₀ fun z => by positivity
  fun_prop

theorem norm_ballClamp_le (z : ℂ) : ‖ballClamp z‖ ≤ 1 := by
  unfold ballClamp
  have hm : 0 < max 1 ‖z‖ := lt_max_of_lt_left one_pos
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hm.le),
    inv_mul_le_iff₀ hm, mul_one]
  exact le_max_right _ _

theorem ballClamp_of_norm_le {z : ℂ} (h : ‖z‖ ≤ 1) : ballClamp z = z := by
  unfold ballClamp
  rw [max_eq_left h, inv_one, Complex.ofReal_one, one_mul]

/-- The point of the closed unit disc at a complex number, retracted onto the disc. -/
noncomputable def discPt (z : ℂ) : ClosedUnitDisc :=
  ⟨planeOf (ballClamp z), by
    simp only [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact norm_ballClamp_le z⟩

theorem continuous_discPt : Continuous discPt :=
  (planeOf.continuous.comp continuous_ballClamp).subtype_mk _

theorem discPt_mul (t : I) (w : Circle) : discPt ((t : ℂ) * w) = polarDiscPoint t w := by
  apply Subtype.ext
  change planeOf (ballClamp ((t : ℂ) * w)) = planeOf ((t : ℂ) * w)
  rw [ballClamp_of_norm_le]
  rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg t.2.1]
  exact t.2.2

theorem discPt_zero : discPt 0 = polarCentre := by
  apply Subtype.ext
  change planeOf (ballClamp 0) = 0
  rw [ballClamp_of_norm_le (by simp)]
  simp

theorem discPt_injOn : InjOn discPt (closedBall 0 1) := by
  intro x hx y hy h
  have h' := congrArg Subtype.val h
  change planeOf (ballClamp x) = planeOf (ballClamp y) at h'
  rwa [ballClamp_of_norm_le (mem_closedBall_zero_iff.mp hx),
    ballClamp_of_norm_le (mem_closedBall_zero_iff.mp hy), planeOf.injective.eq_iff] at h'

theorem exists_discPt_eq (x : ClosedUnitDisc) : ∃ z ∈ closedBall (0 : ℂ) 1, discPt z = x := by
  have hx : ‖planeOf.symm x.1‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.mp x.2
  refine ⟨planeOf.symm x.1, mem_closedBall_zero_iff.mpr hx, ?_⟩
  apply Subtype.ext
  change planeOf (ballClamp _) = _
  rw [ballClamp_of_norm_le hx, LinearIsometryEquiv.apply_symm_apply]

/-! ### The chart in `ℂ` -/

/-- The map `ℂ → ℂ` that reads a chart of the plane on the closed unit disc of `ℂ`. -/
noncomputable def chartC (Ψ : C(ClosedUnitDisc, EuclideanPlane)) (z : ℂ) : ℂ :=
  complexPlane.symm (Ψ (discPt z))

section Chart

variable {Ψ : C(ClosedUnitDisc, EuclideanPlane)} {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}

theorem continuous_chartC : Continuous (chartC Ψ) :=
  complexPlane.symm.continuous.comp (Ψ.continuous.comp continuous_discPt)

theorem toSph_chartC (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (z : ℂ) :
    toSph (chartC Ψ z) = Φ (discPt z) := by
  rw [hΨ]
  simp [toSph, chartC]

theorem chartC_injOn (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    (hi : Function.Injective Φ) : InjOn (chartC Ψ) (closedBall 0 1) := by
  intro x hx y hy h
  apply discPt_injOn hx hy
  apply hi
  rw [← toSph_chartC hΨ, ← toSph_chartC hΨ, h]

theorem wind_chartC (Ψ : C(ClosedUnitDisc, EuclideanPlane)) :
    wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) =
      wind (fun w => complexPlane.symm (Ψ (polarDiscPoint 1 w)))
        (complexPlane.symm (Ψ polarCentre)) := by
  have h1 : (fun w : Circle => chartC Ψ w) =
      fun w => complexPlane.symm (Ψ (polarDiscPoint 1 w)) := by
    funext w
    have := discPt_mul 1 w
    simp only [Set.Icc.coe_one, Complex.ofReal_one, one_mul] at this
    simp only [chartC, this]
  rw [h1, chartC, discPt_zero]

/-- The image under the chart of an open subset of the open unit disc is open in the sphere. -/
theorem isOpen_toSph_image (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    (hi : Function.Injective Φ) {Q : Set ℂ} (hQ : IsOpen Q) (hQb : Q ⊆ ball 0 1) :
    IsOpen (toSph '' (chartC Ψ '' Q)) :=
  isOpenEmbedding_toSph.isOpenMap _ (isOpen_image_of_injOn hQ continuous_chartC.continuousOn
    ((chartC_injOn hΨ hi).mono (hQb.trans ball_subset_closedBall)))

end Chart

/-! ### Rays of a polar chart -/

section Polar

variable {Γ : Drawing (OnePoint EuclideanPlane)} {c : OnePoint EuclideanPlane}
  {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ : C(ClosedUnitDisc, EuclideanPlane)}

theorem isGammaNice_U (Γ : Drawing (OnePoint EuclideanPlane)) : IsGammaNice Γ Γ.U := by
  apply isGammaNice_of_sat
  rintro a ((⟨v, hv, rfl⟩ | ha) | ha) _
  · exact singleton_subset_iff.mpr (Γ.V_subset_U hv)
  · exact fun x hx => (ha.2.1 hx).1
  · rintro x -
    obtain ⟨y, hya, hyU⟩ := ‹(a ∩ Γ.U).Nonempty›
    exact absurd hyU (region_subset ha hya)

theorem isGammaNice_region {r : Set (OnePoint EuclideanPlane)} (hr : r ∈ Γ.R) :
    IsGammaNice Γ r :=
  ⟨{r}, singleton_subset_iff.mpr (Or.inr hr), by simp⟩

/-- The directions of a polar chart whose rays lie in `U(Γ)`. -/
def rimDirs (Γ : Drawing (OnePoint EuclideanPlane)) (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) :
    Set Circle :=
  {w | polarRimMap Φ w ∈ Γ.U}

/-- A point of a ray of a polar chart lies in a nice set exactly when the rim point does. -/
theorem polar_ray_mem_iff (hp : IsPolar Γ c Φ) {Z : Set (OnePoint EuclideanPlane)}
    (hZ : IsGammaNice Γ Z) (w : Circle) {t : I} (ht : 0 < t) :
    Φ (polarDiscPoint t w) ∈ Z ↔ polarRimMap Φ w ∈ Z := by
  have := polar_ray_mem_nice_iff hp hZ (polarDiscPoint_one_ne_centre w) t ht
  rw [discScale_polarDiscPoint_one] at this
  exact this.symm

/-- A point of the chart in `ℂ` at radius `t ∈ (0, 1]` lies in a nice set exactly when the rim
point of its direction does. -/
theorem chart_ray_mem_iff (hp : IsPolar Γ c Φ) (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    {Z : Set (OnePoint EuclideanPlane)} (hZ : IsGammaNice Γ Z) (w : Circle) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) :
    toSph (chartC Ψ ((t : ℂ) * w)) ∈ Z ↔ polarRimMap Φ w ∈ Z := by
  rw [toSph_chartC hΨ]
  have := discPt_mul ⟨t, ht.le, ht1⟩ w
  simp only at this
  rw [this]
  exact polar_ray_mem_iff hp hZ w (t := ⟨t, ht.le, ht1⟩) ht

/-- The centre of the chart in `ℂ`. -/
theorem toSph_chartC_zero (hp : IsPolar Γ c Φ) (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) :
    toSph (chartC Ψ 0) = c := by
  rw [toSph_chartC hΨ, discPt_zero, hp.centre]

/-- The region of the corner after a direction `w` of the star of a polar chart. -/
noncomputable def cornerRegion (Γ : Drawing (OnePoint EuclideanPlane))
    (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (w : Circle) : Set (OnePoint EuclideanPlane) :=
  connectedComponentIn (univ \ Γ.U)
    (polarRimMap Φ (w * Circle.exp (gap (rimDirs Γ Φ) w / 2)))

variable (hp : IsPolar Γ c Φ) (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
  (hD : (rimDirs Γ Φ).Finite)
include hp hΨ hD

/-- The directions inside a corner are not in `U(Γ)`. -/
theorem rim_notMem_U_of_lt_gap (w : Circle) {θ : ℝ} (h0 : 0 < θ)
    (hθ : θ < gap (rimDirs Γ Φ) w) : polarRimMap Φ (w * Circle.exp θ) ∉ Γ.U :=
  not_mem_of_lt_gap hD w h0 hθ

theorem cornerRegion_mem (w : Circle) : cornerRegion Γ Φ w ∈ Γ.R :=
  (mem_R_iff Γ).mpr ⟨_, rim_notMem_U_of_lt_gap hp hΨ hD w (half_pos (gap_pos hD w))
    (half_lt_self (gap_pos hD w)), rfl⟩

/-- **The corner after a direction lies in one region.** -/
theorem image_cone_subset_cornerRegion (w : Circle) :
    toSph '' (chartC Ψ '' cone w (gap (rimDirs Γ Φ) w) 1) ⊆ cornerRegion Γ Φ w := by
  have hg := gap_pos hD w
  have hreg := cornerRegion_mem hp hΨ hD w
  have hoff : ∀ y ∈ cone w (gap (rimDirs Γ Φ) w) 1, toSph (chartC Ψ y) ∉ Γ.U := by
    rintro _ ⟨t, ht, ht1, θ, hθ, hθg, rfl⟩
    rw [← Circle.coe_mul, chart_ray_mem_iff hp hΨ (isGammaNice_U Γ) _ ht ht1]
    exact rim_notMem_U_of_lt_gap hp hΨ hD w hθ hθg
  have hbase : (1 : ℂ) * ((w * Circle.exp (gap (rimDirs Γ Φ) w / 2) : Circle) : ℂ) ∈
      cone w (gap (rimDirs Γ Φ) w) 1 :=
    ⟨1, one_pos, le_rfl, _, half_pos hg, half_lt_self hg, by push_cast; ring⟩
  have hbase' : toSph (chartC Ψ ((1 : ℂ) * ((w * Circle.exp (gap (rimDirs Γ Φ) w / 2) :
      Circle) : ℂ))) ∈ cornerRegion Γ Φ w := by
    have hrim := (chart_ray_mem_iff hp hΨ (isGammaNice_region hreg)
      (w * Circle.exp (gap (rimDirs Γ Φ) w / 2)) one_pos le_rfl)
    simp only [Complex.ofReal_one] at hrim
    rw [hrim]
    exact mem_connectedComponentIn ⟨mem_univ _, rim_notMem_U_of_lt_gap hp hΨ hD w
      (half_pos hg) (half_lt_self hg)⟩
  rw [← image_comp]
  refine subset_region hreg (((isPreconnected_cone _ _ _).image _
    (continuous_toSph.comp continuous_chartC).continuousOn)) ?_ ⟨_, hbase, rfl⟩ hbase'
  rw [Set.disjoint_left]
  rintro _ ⟨y, hy, rfl⟩
  exact hoff y hy

/-- A thin counterclockwise sector beside a direction lies in the corner after it. -/
theorem image_osecP_subset_cornerRegion (w : Circle) {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < Real.pi / 2) (hεg : ε < gap (rimDirs Γ Φ) w) :
    toSph '' (chartC Ψ '' osecP w ε 1) ⊆ cornerRegion Γ Φ w :=
  (image_mono (image_mono (osecP_subset_cone hε hε' hεg))).trans
    (image_cone_subset_cornerRegion hp hΨ hD w)

/-- A thin clockwise sector beside the end of a corner lies in that corner. -/
theorem image_osecM_subset_cornerRegion (w : Circle) {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < Real.pi / 2) (hεg : ε < gap (rimDirs Γ Φ) w) :
    toSph '' (chartC Ψ '' osecM (w * Circle.exp (gap (rimDirs Γ Φ) w)) ε 1) ⊆
      cornerRegion Γ Φ w :=
  (image_mono (image_mono (osecM_subset_cone hε hε' hεg))).trans
    (image_cone_subset_cornerRegion hp hΨ hD w)

/-- The centre lies in the closure of every corner. -/
theorem centre_mem_closure_cornerRegion (w : Circle) : c ∈ closure (cornerRegion Γ Φ w) := by
  have hg := gap_pos hD w
  set u : Circle := w * Circle.exp (gap (rimDirs Γ Φ) w / 2)
  have hlim : Filter.Tendsto (fun s : ℝ => toSph (chartC Ψ ((s : ℂ) * u))) (𝓝[>] 0)
      (𝓝 (toSph (chartC Ψ 0))) := by
    have hc : Continuous fun s : ℝ => toSph (chartC Ψ ((s : ℂ) * u)) :=
      continuous_toSph.comp (continuous_chartC.comp (by fun_prop))
    have := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  rw [toSph_chartC_zero hp hΨ] at hlim
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  exact image_cone_subset_cornerRegion hp hΨ hD w
    ⟨_, ⟨_, ⟨s, hs.1, hs.2.le, _, half_pos hg, half_lt_self hg, rfl⟩, rfl⟩, rfl⟩

/-- A point of a ray of the star lies in the closure of the corner after the ray. -/
theorem ray_mem_closure_cornerRegion (w : Circle) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    toSph (chartC Ψ ((t : ℂ) * w)) ∈ closure (cornerRegion Γ Φ w) := by
  have hg := gap_pos hD w
  set ε : ℝ := min (gap (rimDirs Γ Φ) w / 2) (Real.pi / 4)
  have hε : 0 < ε := lt_min (half_pos hg) (by positivity)
  have hε' : ε < Real.pi / 2 := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  have hεg : ε < gap (rimDirs Γ Φ) w := (min_le_left _ _).trans_lt (half_lt_self hg)
  have hmem : (t : ℂ) * w ∈ closure (osecP w ε 1) :=
    sector_subset_closure_openSector (mem_osecP_coord hε hε' one_pos)
      (ray_mem_secP hε hε' ht ht1)
  have hcont : Continuous fun y => toSph (chartC Ψ y) := continuous_toSph.comp continuous_chartC
  have := map_mem_closure hcont hmem (fun y hy => (image_osecP_subset_cornerRegion hp hΨ hD w
    hε hε' hεg) ⟨_, ⟨y, hy, rfl⟩, rfl⟩)
  exact this

/-- **A region beside a ray is a corner next to it.** Let `w` be a direction of the star, and
let `w'` be the direction before it, so that the corner after `w'` ends at `w`. A region whose
closure meets the ray of `w` is the corner after `w` or the corner after `w'`. -/
theorem region_eq_corner_of_ray {w w' : Circle} (hw : w ∈ rimDirs Γ Φ)
    (hprev : w' * Circle.exp (gap (rimDirs Γ Φ) w') = w) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {r : Set (OnePoint EuclideanPlane)} (hr : r ∈ Γ.R)
    (hcl : toSph (chartC Ψ ((t : ℂ) * w)) ∈ closure r) :
    r = cornerRegion Γ Φ w ∨ r = cornerRegion Γ Φ w' := by
  have hg := gap_pos hD w
  have hg' := gap_pos hD w'
  set ε : ℝ := min (min (gap (rimDirs Γ Φ) w) (gap (rimDirs Γ Φ) w')) (Real.pi / 2) / 2
  have hm : 0 < min (min (gap (rimDirs Γ Φ) w) (gap (rimDirs Γ Φ) w')) (Real.pi / 2) :=
    lt_min (lt_min hg hg') (by positivity)
  have hε : 0 < ε := half_pos hm
  have hε' : ε < Real.pi / 2 :=
    (half_lt_self hm).trans_le (min_le_right _ _)
  have hεg : ε < gap (rimDirs Γ Φ) w :=
    (half_lt_self hm).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hεg' : ε < gap (rimDirs Γ Φ) w' :=
    (half_lt_self hm).trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hopen := isOpen_toSph_image hΨ hp.inj (isOpen_openSector _ _ _)
    (fun y hy => mem_ball_zero_iff.mpr (hy : y ∈ dsec w ε 1).1)
  have hin : toSph (chartC Ψ ((t : ℂ) * w)) ∈ toSph '' (chartC Ψ '' dsec w ε 1) :=
    ⟨_, ⟨_, ray_mem_dsec hε hε' ht ht1, rfl⟩, rfl⟩
  obtain ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, hyr⟩ := mem_closure_iff.mp hcl _ hopen hin
  rcases dsec_cases hε hε' hy with h | h | ⟨hpos, hyeq⟩
  · left
    exact region_eq_of_mem hr (cornerRegion_mem hp hΨ hD w) hyr
      (image_osecP_subset_cornerRegion hp hΨ hD w hε hε' hεg ⟨_, ⟨y, h, rfl⟩, rfl⟩)
  · right
    rw [← hprev] at h
    exact region_eq_of_mem hr (cornerRegion_mem hp hΨ hD w') hyr
      (image_osecM_subset_cornerRegion hp hΨ hD w' hε hε' hεg' ⟨_, ⟨y, h, rfl⟩, rfl⟩)
  · exfalso
    have hlt : along w y ≤ 1 := by
      have h1 := hy.1
      have h2 := norm_eq_along_across w y
      nlinarith [sq_nonneg (across w y), norm_nonneg y]
    rw [hyeq, chart_ray_mem_iff hp hΨ (isGammaNice_region hr) _ hpos hlt] at hyr
    exact region_subset hr hyr hw

/-- **A region at the centre is a corner.** -/
theorem exists_corner_of_closure_centre (hcU : c ∈ Γ.U) (hne : (rimDirs Γ Φ).Nonempty)
    {r : Set (OnePoint EuclideanPlane)} (hr : r ∈ Γ.R) (hcl : c ∈ closure r) :
    ∃ w ∈ rimDirs Γ Φ, r = cornerRegion Γ Φ w := by
  obtain ⟨x, hxi, hxr⟩ := mem_closure_iff.mp hcl _ isOpen_interior hp.nhd
  obtain ⟨x', rfl⟩ := interior_subset hxi
  obtain ⟨y, hyb, rfl⟩ := exists_discPt_eq x'
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [discPt_zero, hp.centre] at hxr
    exact region_subset hr hxr hcU
  have hyn : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hyb
  have hyeq := eq_norm_mul_unitOf hy0
  have hxr' : toSph (chartC Ψ y) ∈ r := by rw [toSph_chartC hΨ]; exact hxr
  have hdir : unitOf y hy0 ∉ rimDirs Γ Φ := by
    intro hmem
    have hU : toSph (chartC Ψ ((‖y‖ : ℂ) * unitOf y hy0)) ∈ Γ.U :=
      (chart_ray_mem_iff hp hΨ (isGammaNice_U Γ) _ (norm_pos_iff.mpr hy0) hyn).mpr hmem
    rw [← hyeq] at hU
    exact region_subset hr hxr' hU
  obtain ⟨w, hw, θ, hθ, hθg, hwθ⟩ := exists_corner_of_notMem hD hne hdir
  refine ⟨w, hw, region_eq_of_mem hr (cornerRegion_mem hp hΨ hD w) hxr' ?_⟩
  exact image_cone_subset_cornerRegion hp hΨ hD w
    ⟨_, ⟨y, mem_cone_of_unitOf hy0 hyn hθ hθg hwθ, rfl⟩, rfl⟩

end Polar

end GraphMinor.GM06
