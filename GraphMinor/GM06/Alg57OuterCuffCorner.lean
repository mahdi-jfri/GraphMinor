module

public import GraphMinor.GM06.Alg57InnerCuffCorner
import GraphMinor.GM06.Alg57RegionIncidence

/-!
# The cap corner after a reverse outer cuff dart

For the outer-cuff adjacency in VI (5.7), page 133, the exponential
chart at an outer gap reads the exterior cap as the corner on the
left of the reverse gap dart. Its closure misses the open unit disc.
The actual increasing angular parametrization fixes the side.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology Real GraphMinor.Surface GraphMinor.GM11 unitInterval
section Gap
variable {k : ℕ} (i : Fin k)

/-- The midpoint of an outer gap in the complex picture. -/
noncomputable def outerGapMid (k : ℕ) (i : Fin k) : ℂ :=
  Complex.exp ((gapMidAngle k i : ℂ) * Complex.I)

theorem outerGapMid_ne_zero : outerGapMid k i ≠ 0 := Complex.exp_ne_zero _

theorem norm_outerGapMid : ‖outerGapMid k i‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem toSph_outerGapMid : toSph (outerGapMid k i) = cylinderToSphere (cylinderN2Point k i) := by
  rw [cylinderN2Point, cylinderToSphere_cylinderPoint, outerGapMid, gapMidAngle]
  norm_num

/-- The points `q · exp w` near the gap midpoint `q` miss the graph `G`. -/
theorem exists_ball_outerGapMid_notMem {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) :
    ∃ η > 0, ∀ w : ℂ, ‖w‖ < η →
      toSph (outerGapMid k i * Complex.exp w) ∉ cylinderToSphere '' G.U := by
  have hS : IsClosed (cylinderToSphere '' G.U) :=
    isClosedEmbedding_cylinderToSphere.isClosedMap _ G.isClosed_U
  have hq : toSph (outerGapMid k i) ∉ cylinderToSphere '' G.U := by
    rw [toSph_outerGapMid]
    rintro ⟨p, hp, hpq⟩
    rw [injective_cylinderToSphere hpq] at hp
    exact cylinderN2Point_not_mem_U hG i hp
  let f : ℂ → OnePoint EuclideanPlane := fun w => toSph (outerGapMid k i * Complex.exp w)
  have hf : Continuous f := isOpenEmbedding_toSph.continuous.comp (by fun_prop)
  have h0 : (0 : ℂ) ∈ f ⁻¹' (cylinderToSphere '' G.U)ᶜ := by
    simp only [mem_preimage, mem_compl_iff, f, Complex.exp_zero, mul_one]
    exact hq
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp (hS.isOpen_compl.preimage hf) 0 h0
  exact ⟨η, hη, fun w hw => hball (mem_ball_zero_iff.mpr hw)⟩

/-- A point of the outer cuff in the complex coordinates. -/
theorem outerGapMid_mul_exp_I (s : ℝ) :
    outerGapMid k i * Complex.exp ((s : ℂ) * Complex.I) =
      Complex.exp (((gapMidAngle k i + s : ℝ) : ℂ) * Complex.I) := by
  rw [outerGapMid, ← Complex.exp_add]
  push_cast
  ring_nf

/-- A point of the `i`th outer gap curve in the complex coordinates. -/
theorem cylinderToSphere_alg511OuterCuffGapCurve (u : I) :
    cylinderToSphere (alg511OuterCuffGapCurve k i u) = toSph
      (Complex.exp (((2 * (((i.1 + 1 : ℕ) : ℝ) + (u : ℝ)) * π / k : ℝ) : ℂ) * Complex.I)) := by
  have hp : alg511OuterCuffGapCurve k i u = cylinderPoint 2 (by norm_num)
      (2 * (((i.1 + 1 : ℕ) : ℝ) + (u : ℝ)) * π / k) := by
    apply Subtype.ext
    apply Prod.ext
    · norm_num [alg511OuterCuffGapCurve, alg511CuffSwap, initialCuffGapCurve, cylinderPoint]
    · rfl
  rw [hp, cylinderToSphere_cylinderPoint]
  norm_num

/-- **The exponential chart at the midpoint of an outer gap.** For small `l`, the drawing `G⁺`
meets the chart only along the imaginary axis, and there it is in the gap edge. Also the points
`q · exp w` with `‖w‖ ≤ l` miss `G`. -/
theorem exists_outer_gap_expChart {G F : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) :
    ∃ l : ℝ, 0 < l ∧ l < 1 ∧ l < π / k ∧ l < Real.log 2 ∧
      (∀ w : ℂ, ‖w‖ ≤ l → toSph (outerGapMid k i * Complex.exp w) ∉ cylinderToSphere '' G.U) ∧
      (∀ w : ℂ, ‖w‖ ≤ 1 → toSph (expMap (outerGapMid k i) l w) ∈ (cylinderSphereDrawing F).U →
        w.re = 0) ∧
      (∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 0 → w.re = 0 → toSph (expMap (outerGapMid k i) l w) ∈
        cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1)) := by
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr hG.1
  obtain ⟨η, hη, hball⟩ := exists_ball_outerGapMid_notMem i hG
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
      rw [norm_expMap, norm_outerGapMid, one_mul] at hn
      have hre0 : -1 ≤ w.re := by
        have hh := (Complex.abs_re_le_norm w).trans hw
        linarith [neg_abs_le w.re]
      rw [bd_closedCylinder] at hpbd
      rcases hpbd with h1 | h2
      · have h1' : p.1.1 = 1 := h1
        rw [h1'] at hn
        have he1 : Real.exp (l * w.re) = (2 : ℝ)⁻¹ := by linarith
        have hlog := congrArg Real.log he1
        rw [Real.log_exp, Real.log_inv] at hlog
        have hh : -l ≤ l * w.re := by nlinarith
        linarith
      · have h2' : p.1.1 = 2 := h2
        rw [h2'] at hn
        have he2 : Real.exp (l * w.re) = 1 := by linarith
        have hh := Real.exp_eq_one_iff (l * w.re) |>.mp he2
        exact (mul_eq_zero.mp hh).resolve_left hl0.ne'
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
    refine ⟨alg511OuterCuffGapCurve k i v, ⟨v, ⟨hu0, hu1⟩, rfl⟩, ?_⟩
    rw [cylinderToSphere_alg511OuterCuffGapCurve, expMap, hwI,
      show (l : ℂ) * (((w.im : ℝ) : ℂ) * Complex.I) = (((l * w.im) : ℝ) : ℂ) * Complex.I by
        push_cast; ring, outerGapMid_mul_exp_I, hang]

/-- The corner on the left of a reverse outer gap dart has its
closure in the exterior cap. The corner labels are those
constructed from positive stars by `exists_cornerLabel`. -/
theorem outer_reverse_corner_subset_closed_cap
    {G F : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
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
    (he : cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1) ∈ (cylinderSphereDrawing F).E)
    (hγe : ∀ t, γ (cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1)) t =
      cylinderToSphere (alg511OuterCuffGapCurve k i t)) :
    closure (ρ ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1), true), he⟩) ⊆
      (toSph '' ball (0 : ℂ) 1)ᶜ := by
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr hG.1
  have hπ := Real.pi_pos
  obtain ⟨l, hl0, hl1, hlπ, hl2, hnear, hU, hE⟩ := exists_outer_gap_expChart i hG hFU
  set e := cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1) with he_def
  set d : DrawingDart (cylinderSphereDrawing F) := ⟨(e, true), he⟩ with hd
  have hdc : ∀ t (ht : t ∈ Icc (0 : ℝ) 1), dartCurve γ d t =
      cylinderToSphere (alg511OuterCuffGapCurve k i ⟨1 - t, Set.mem_Icc.mpr
        ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩) := by
    intro t ht
    have h1 : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp only [dartCurve, d, ite_true]
    rw [edgeCurve_of_mem γ e h1, hγe]
  have hmid : dartCurve γ d (1 / 2) = toSph (outerGapMid k i) := by
    rw [hdc _ ⟨by norm_num, by norm_num⟩, cylinderToSphere_alg511OuterCuffGapCurve, outerGapMid]
    congr 4
    simp only [gapMidAngle]
    field_simp
    all_goals ring
  have hpolar := expChart_isPolar (outerGapMid_ne_zero i) hl0 hl1 he hU hE
  rw [← hmid] at hpolar
  set δ : ℝ := min (1 / 2) (l * k / (4 * π)) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ l * k / (4 * π) := min_le_right _ _
  have hμδ : 2 * π / k * δ < l := by
    calc 2 * π / k * δ ≤ 2 * π / k * (l * k / (4 * π)) := by gcongr
      _ = l / 2 := by field_simp; ring
      _ < l := half_lt_self hl0
  have hruns : RunsOut (expChartΨ (outerGapMid k i) l) (Circle.exp (-(π / 2))) (dartCurve γ d)
      (1 / 2) δ := by
    refine runsOut_expChart_neg hl0 hδ0 (by positivity) hμδ fun t ht => ?_
    rw [hdc t ⟨by linarith [ht.1], by linarith [ht.2]⟩, cylinderToSphere_alg511OuterCuffGapCurve,
      show -(((2 * π / k * (t - 1 / 2) : ℝ)) : ℂ) * Complex.I =
        (((-(2 * π / k * (t - 1 / 2))) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      outerGapMid_mul_exp_I]
    congr 4
    simp only [gapMidAngle]
    field_simp
    ring
  have hfin : (rimDirs (cylinderSphereDrawing F) (expChart (outerGapMid k i) l)).Finite := by
    rw [rimDirs_expChart he hU hE]; exact toFinite _
  have hW : Circle.exp (-(π / 2)) ∈ rimDirs (cylinderSphereDrawing F) (expChart (outerGapMid k i) l) := by
    rw [rimDirs_expChart he hU hE]; exact mem_insert _ _
  have hcorner := cornerLabel_eq_mid (infty_notMem_cylinderSphereDrawing_U F) hγ hform d
    (1 / 2) ⟨by norm_num, by norm_num⟩ _ _ hpolar (expChart_eq _ l)
    (wind_expChartΨ_pos (outerGapMid_ne_zero i) hl0 hl1) hfin _ hW δ hruns
  rw [cornerRegion_expChart_neg he hU hE] at hcorner
  have hnorm : 1 < ‖expMap (outerGapMid k i) l 1‖ := by
    rw [norm_expMap, norm_outerGapMid, one_mul]
    simpa using Real.one_lt_exp_iff.mpr hl0
  have hoff : toSph (expMap (outerGapMid k i) l 1) ∉ (cylinderSphereDrawing F).U := by
    rw [cylinderSphereDrawing_U]
    rintro ⟨p, _, heq⟩
    have hn := norm_eq_of_cylinderToSphere_eq heq
    have hp := p.property.1.2
    linarith
  have hpoint : toSph (expMap (outerGapMid k i) l 1) ∈ ρ d := by
    rw [hcorner]
    exact mem_connectedComponentIn ⟨mem_univ _, hoff⟩
  exact closure_region_subset_outer_round_disc 1
    (round_cuff_mem_cylinderSphereDrawing hFU (Or.inr rfl)) (hρ.region d) hnorm hpoint

end Gap
end GraphMinor.GM06
