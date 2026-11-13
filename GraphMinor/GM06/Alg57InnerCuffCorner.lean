module

public import GraphMinor.GM06.Alg57CuffCapRegions
import GraphMinor.GM06.Alg57EdgeCorner
import GraphMinor.GM06.Alg57RegionIncidence

/-!
# The cap corner after a positive inner cuff dart

The positive inner cuff dart has the attached inner disc on its
left. For the cuff-adjacency step of VI (5.7), page 133, we read its
corner in the positive exponential chart at the middle of its gap.
The forward direction is `i`, and the corner after it contains a
point of norm less than one half. The whole corner region, and
then its closure, stay on that side of the cuff circle. This is a
local statement and does not require a connected whole drawing.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology Real GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The corner chosen at the start of a dart is the same corner
read in any positive chart at an interior point of that dart. -/
theorem cornerLabel_eq_mid
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {R : DartRotation (DrawingDart Γ)} {ρ : DrawingDart Γ → Set (OnePoint EuclideanPlane)}
    (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ Γ.U) (hγ : EdgePar Γ γ)
    (hform : ∀ d, ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane))
      (z : DrawingDart Γ → Circle), IsCcwStar Γ γ R (dartVertex γ d) Φ z ∧
        ρ d = cornerRegion Γ Φ (z d))
    (d : DrawingDart Γ) (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1)
    (Φm : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (Ψm : C(ClosedUnitDisc, EuclideanPlane))
    (hpm : IsPolar Γ (dartCurve γ d a) Φm)
    (hΨm : ∀ x, Φm x = (Ψm x : OnePoint EuclideanPlane))
    (hposm : 0 < wind (fun w : Circle => chartC Ψm w) (chartC Ψm 0))
    (hDm : (rimDirs Γ Φm).Finite) (Wm : Circle) (hWm : Wm ∈ rimDirs Γ Φm)
    (δm : ℝ) (hrunm : RunsOut Ψm Wm (dartCurve γ d) a δm) :
    ρ d = cornerRegion Γ Φm Wm := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩).1
  obtain ⟨Φ, z, hst, hρd⟩ := hform d
  rw [hρd]
  obtain ⟨Ψ, hΨ, hw⟩ := hst.pos
  have hpos : 0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) := by
    rw [wind_chartC]; exact hw
  obtain ⟨δu, hrunu⟩ := hst.runsOut hγ hΨ rfl
  have hpu : IsPolar Γ (dartCurve γ d 0) Φ := by rw [dartCurve_zero]; exact hst.polar
  exact cornerRegion_start_eq_mid hS hinf d.property (isEdgeCurve_dartCurve hγ d)
    hpu hΨ hpos (hst.rimDirs_finite hγ) (hst.mem_rimDirs hγ rfl) hrunu
    ha hpm hΨm hposm hDm hWm hrunm

/-- A curve moving counterclockwise along a round circle runs out
along the positive imaginary direction of its exponential chart. -/
theorem runsOut_expChart_pos {q : ℂ} {l : ℝ} (hl : 0 < l)
    {G : ℝ → OnePoint EuclideanPlane} {a δ μ : ℝ}
    (hδ : 0 < δ) (hμ : 0 < μ) (hμδ : μ * δ < l)
    (hG : ∀ t ∈ Icc a (a + δ),
      G t = toSph (q * Complex.exp ((((μ * (t - a) : ℝ)) : ℂ) * Complex.I))) :
    RunsOut (expChartΨ q l) (Circle.exp (π / 2)) G a δ := by
  have hmI : ((Circle.exp (π / 2) : Circle) : ℂ) = Complex.I := by
    rw [Circle.coe_exp]
    apply Complex.ext
    · rw [Complex.exp_ofReal_mul_I_re]; simp
    · rw [Complex.exp_ofReal_mul_I_im]; simp
  refine ⟨hδ, fun t => μ * (t - a) / l, by fun_prop, by simp, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · intro s _ t _ hst
    have hh : μ * (s - a) < μ * (t - a) := by nlinarith
    exact div_lt_div_of_pos_right hh hl
  · rw [div_lt_one hl]
    nlinarith [ht.2]
  · have hρ0 : 0 ≤ μ * (t - a) / l := div_nonneg (by nlinarith [ht.1]) hl.le
    have hρ1 : μ * (t - a) / l ≤ 1 := by rw [div_le_one hl]; nlinarith [ht.2]
    rw [hG t ht, chartC_expChartΨ q l (by
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ0]
      exact hρ1), expMap, hmI]
    have hl' : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl.ne'
    congr 3
    push_cast
    field_simp

/-- The corner on the left of a positive inner gap dart has its
closure in the attached inner cap. The corner labels are those
constructed from positive stars by `exists_cornerLabel`. -/
theorem inner_forward_corner_subset_closed_cap
    {k : ℕ} {G F : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    (hFU : F.U = G.U ∪ bd ClosedCylinder)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {R : DartRotation (DrawingDart (cylinderSphereDrawing F))}
    {ρ : DrawingDart (cylinderSphereDrawing F) → Set (OnePoint EuclideanPlane)}
    (hγ : EdgePar (cylinderSphereDrawing F) γ)
    (hρ : IsCornerLabel (cylinderSphereDrawing F) γ R ρ)
    (hform : ∀ d, ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane))
      (z : DrawingDart (cylinderSphereDrawing F) → Circle),
      IsCcwStar (cylinderSphereDrawing F) γ R (dartVertex γ d) Φ z ∧
        ρ d = cornerRegion (cylinderSphereDrawing F) Φ (z d))
    (i : Fin k)
    (he : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈ (cylinderSphereDrawing F).E)
    (hγe : ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
      cylinderToSphere (initialCuffGapCurve k i t)) :
    closure (ρ ⟨(cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1), false), he⟩) ⊆
      toSph '' closedBall (0 : ℂ) (1 / 2) := by
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr hG.1
  have hπ := Real.pi_pos
  obtain ⟨l, hl0, hl1, hlπ, hl2, hnear, hU, hE⟩ := exists_gap_expChart i hG hFU
  set e := cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)
  set d : DrawingDart (cylinderSphereDrawing F) := ⟨(e, false), he⟩
  have hdc : ∀ t (ht : t ∈ Icc (0 : ℝ) 1), dartCurve γ d t =
      cylinderToSphere (initialCuffGapCurve k i ⟨t, ht⟩) := by
    intro t ht
    simp only [dartCurve, d, Bool.false_eq_true, ↓reduceIte]
    rw [edgeCurve_of_mem γ e ht, hγe]
  have hmid : dartCurve γ d (1 / 2) = toSph (gapMid k i) := by
    rw [hdc _ ⟨by norm_num, by norm_num⟩, cylinderToSphere_initialCuffGapCurve, gapMid]
    congr 4
    simp only [gapMidAngle]
    field_simp
  have hpolar := expChart_isPolar (gapMid_ne_zero i) hl0 hl1 he hU hE
  rw [← hmid] at hpolar
  set δ : ℝ := min (1 / 2) (l * k / (4 * π))
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ l * k / (4 * π) := min_le_right _ _
  have hμδ : 2 * π / k * δ < l := by
    calc 2 * π / k * δ ≤ 2 * π / k * (l * k / (4 * π)) := by gcongr
      _ = l / 2 := by field_simp; ring
      _ < l := half_lt_self hl0
  have hruns : RunsOut (expChartΨ (gapMid k i) l) (Circle.exp (π / 2))
      (dartCurve γ d) (1 / 2) δ := by
    refine runsOut_expChart_pos hl0 hδ0 (by positivity) hμδ fun t ht => ?_
    rw [hdc t ⟨by linarith [ht.1], by linarith [ht.2]⟩,
      cylinderToSphere_initialCuffGapCurve, gapMid_mul_exp_I]
    congr 4
    simp only [gapMidAngle]
    push_cast
    field_simp
    ring
  have hfin : (rimDirs (cylinderSphereDrawing F) (expChart (gapMid k i) l)).Finite := by
    rw [rimDirs_expChart he hU hE]
    exact toFinite _
  have hW : Circle.exp (π / 2) ∈ rimDirs (cylinderSphereDrawing F) (expChart (gapMid k i) l) := by
    rw [rimDirs_expChart he hU hE]
    exact mem_insert_of_mem _ (mem_singleton _)
  have hcorner := cornerLabel_eq_mid (infty_notMem_cylinderSphereDrawing_U F) hγ hform d
    (1 / 2) ⟨by norm_num, by norm_num⟩ _ _ hpolar (expChart_eq _ l)
    (wind_expChartΨ_pos (gapMid_ne_zero i) hl0 hl1) hfin _ hW δ hruns
  rw [cornerRegion_expChart_pos he hU hE] at hcorner
  have hnorm : ‖expMap (gapMid k i) l (-1)‖ < 1 / 2 := by
    rw [norm_expMap, norm_gapMid]
    have hexp : Real.exp (-l) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hl0)
    simpa using (mul_lt_mul_of_pos_left hexp (by norm_num : (0 : ℝ) < 1 / 2))
  have hoff : toSph (expMap (gapMid k i) l (-1)) ∉ (cylinderSphereDrawing F).U := by
    rw [cylinderSphereDrawing_U]
    rintro ⟨p, _, heq⟩
    have hn := norm_eq_of_cylinderToSphere_eq heq
    have hp := p.property.1.1
    linarith
  have hpoint : toSph (expMap (gapMid k i) l (-1)) ∈ ρ d := by
    rw [hcorner]
    exact mem_connectedComponentIn ⟨mem_univ _, hoff⟩
  exact closure_region_subset_inner_round_disc (1 / 2)
    (round_cuff_mem_cylinderSphereDrawing hFU (Or.inl rfl)) (hρ.region d) hnorm hpoint

end GraphMinor.GM06
