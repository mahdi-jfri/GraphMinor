module

public import GraphMinor.GM06.Alg57PathSide
public import GraphMinor.GM06.Alg57VertexStar

/-!
# Facts about charts, corners and wedges

Small facts used at the two ends of the one path.

* `angleTo_swap`: the angles from `x` to `y` and from `y` to `x` add up to `2π`.
* `exists_mem_cornerSet`: a point of a chart that is not its centre and not in `U(Γ)` lies in the
  corner after some direction.
* `RunsIn.runsOut_one_sub`: a curve that runs in along a ray, read backwards, runs out along it.
* `rim_mem_of_runsOut`, `rim_mem_of_runsIn`: a curve that runs along a ray inside a nice set puts
  the rim point of the ray in that set.
* `disjoint_wedgeSet_of_rot`: the cone from a direction `F` counterclockwise to the direction of a
  dart `c` misses a nice set whose only directions are `F`, `c` and the dart after `c`.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The angles from `x` to `y` and back add up to a full turn. -/
theorem angleTo_swap {x y : Circle} (h : x ≠ y) : angleTo y x = 2 * Real.pi - angleTo x y := by
  have ha := angleTo_mem x y
  have hlt : angleTo x y < 2 * Real.pi := by
    refine lt_of_le_of_ne ha.2 fun h2 => h ?_
    rw [← mul_exp_angleTo x y, h2, Circle.exp_two_pi, mul_one]
  apply angleTo_eq ⟨by linarith, by linarith [ha.1]⟩
  symm
  calc y * Circle.exp (2 * Real.pi - angleTo x y)
      = x * Circle.exp (angleTo x y) * Circle.exp (2 * Real.pi - angleTo x y) := by
        rw [mul_exp_angleTo]
    _ = x := by rw [mul_assoc, ← Circle.exp_add, add_sub_cancel, Circle.exp_two_pi, mul_one]

section Chart

variable {Γ : Drawing (OnePoint EuclideanPlane)} {c : OnePoint EuclideanPlane}
  {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ : C(ClosedUnitDisc, EuclideanPlane)}

/-- Each point of a chart other than its centre is at some radius in `(0, 1]` along some
direction. -/
theorem exists_chart_polar (hp : IsPolar Γ c Φ) (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    {y : OnePoint EuclideanPlane} (hy : y ∈ range Φ) (hyc : y ≠ c) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ∃ u : Circle, y = toSph (chartC Ψ ((t : ℂ) * u)) := by
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨z, hz, rfl⟩ := exists_discPt_eq x
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hyc (by rw [discPt_zero, hp.centre])
  refine ⟨‖z‖, norm_pos_iff.mpr hz0, mem_closedBall_zero_iff.mp hz, Circle.exp (Complex.arg z), ?_⟩
  rw [toSph_chartC hΨ, Circle.coe_exp, Complex.norm_mul_exp_arg_mul_I]

/-- **Points of a chart off `U(Γ)` lie in corners.** -/
theorem exists_mem_cornerSet (hp : IsPolar Γ c Φ) (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    (hD : (rimDirs Γ Φ).Finite) (hne : (rimDirs Γ Φ).Nonempty) {y : OnePoint EuclideanPlane}
    (hy : y ∈ range Φ) (hyc : y ≠ c) (hyU : y ∉ Γ.U) :
    ∃ w ∈ rimDirs Γ Φ, y ∈ cornerSet Γ Φ Ψ w := by
  obtain ⟨t, ht, ht1, u, rfl⟩ := exists_chart_polar hp hΨ hy hyc
  have hu : u ∉ rimDirs Γ Φ := fun hu =>
    hyU ((chart_ray_mem_iff hp hΨ (isGammaNice_U Γ) u ht ht1).mpr hu)
  obtain ⟨w, hw, θ, hθ, hθg, rfl⟩ := exists_corner_of_notMem hD hne hu
  exact ⟨w, hw, _, ⟨_, ⟨t, ht, ht1, θ, hθ, hθg, rfl⟩, rfl⟩, rfl⟩

/-- **A curve along a ray puts the rim point of the ray in a nice set.** -/
theorem rim_mem_of_runsOut (hp : IsPolar Γ c Φ) (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    {Z : Set (OnePoint EuclideanPlane)} (hZ : IsGammaNice Γ Z) {W : Circle}
    {G : ℝ → OnePoint EuclideanPlane} {a δ : ℝ} (hrun : RunsOut Ψ W G a δ) {t : ℝ}
    (ht : t ∈ Ioc a (a + δ)) (hGt : G t ∈ Z) : polarRimMap Φ W ∈ Z := by
  obtain ⟨-, ρ, -, hρ0, hmono, hρG⟩ := hrun
  have hpos : 0 < ρ t := by
    rw [← hρ0]
    exact hmono ⟨le_rfl, by linarith [ht.1, ht.2]⟩ ⟨ht.1.le, ht.2⟩ ht.1
  obtain ⟨h1, hG⟩ := hρG t ⟨ht.1.le, ht.2⟩
  rw [hG] at hGt
  exact (chart_ray_mem_iff hp hΨ hZ W hpos h1.le).mp hGt

theorem rim_mem_of_runsIn (hp : IsPolar Γ c Φ) (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    {Z : Set (OnePoint EuclideanPlane)} (hZ : IsGammaNice Γ Z) {W : Circle}
    {G : ℝ → OnePoint EuclideanPlane} {b δ : ℝ} (hrun : RunsIn Ψ W G b δ) {t : ℝ}
    (ht : t ∈ Ico (b - δ) b) (hGt : G t ∈ Z) : polarRimMap Φ W ∈ Z := by
  obtain ⟨-, ρ, -, hρ0, hanti, hρG⟩ := hrun
  have hpos : 0 < ρ t := by
    rw [← hρ0]
    exact hanti ⟨ht.1, ht.2.le⟩ ⟨by linarith [ht.1, ht.2], le_rfl⟩ ht.2
  obtain ⟨h1, hG⟩ := hρG t ⟨ht.1, ht.2.le⟩
  rw [hG] at hGt
  exact (chart_ray_mem_iff hp hΨ hZ W hpos h1.le).mp hGt

end Chart

/-- A curve that runs in along a ray, read backwards from time `1`, runs out along it. -/
theorem RunsIn.runsOut_one_sub {Ψ : C(ClosedUnitDisc, EuclideanPlane)} {W : Circle}
    {G : ℝ → OnePoint EuclideanPlane} {b δ : ℝ} (h : RunsIn Ψ W G b δ) :
    RunsOut Ψ W (fun s => G (1 - s)) (1 - b) δ := by
  obtain ⟨hδ, ρ, hρc, hρ0, hanti, hρG⟩ := h
  have hmaps : MapsTo (fun s : ℝ => 1 - s) (Icc (1 - b) (1 - b + δ)) (Icc (b - δ) b) :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  refine ⟨hδ, fun s => ρ (1 - s), hρc.comp (continuousOn_const.sub continuousOn_id) hmaps,
    by simpa using hρ0, ?_, fun s hs => hρG (1 - s) (hmaps hs)⟩
  intro s hs s' hs' hss'
  exact hanti (hmaps hs') (hmaps hs) (by linarith)

/-- A direction that is not in the arc `[F, B)` is in the arc `[B, F)`. -/
theorem right_of_not_left {F B w : Circle} (hFB : F ≠ B)
    (hw : ¬ (w = F ∨ angleTo F w < angleTo F B)) : w = B ∨ angleTo B w < angleTo B F := by
  push Not at hw
  obtain ⟨hwF, hge⟩ := hw
  by_cases hwB : w = B
  · exact Or.inl hwB
  right
  have hα := angleTo_mem F B
  have hψ := angleTo_mem F w
  have hψ2 : angleTo F w < 2 * Real.pi := by
    refine lt_of_le_of_ne hψ.2 fun h => hwF ?_
    rw [← mul_exp_angleTo F w, h, Circle.exp_two_pi, mul_one]
  have hgt : angleTo F B < angleTo F w := by
    refine lt_of_le_of_ne hge fun h => hwB ?_
    rw [← mul_exp_angleTo F w, ← h, mul_exp_angleTo]
  have h1 : angleTo B w = angleTo F w - angleTo F B := by
    apply angleTo_eq ⟨by linarith, by linarith [hα.1]⟩
    have key : F * Circle.exp (angleTo F B) * Circle.exp (angleTo F w - angleTo F B) = w := by
      rw [mul_assoc, ← Circle.exp_add, add_sub_cancel, mul_exp_angleTo]
    rw [mul_exp_angleTo] at key
    exact key.symm
  rw [h1, angleTo_swap hFB]
  linarith

section ChartWedge

variable {Γ : Drawing (OnePoint EuclideanPlane)} {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
  {Ψ : C(ClosedUnitDisc, EuclideanPlane)}

/-- A point of a chart along a direction strictly inside the arc from `F` through angle `α` lies
in the cone from `F` through `α`. -/
theorem mem_wedgeSet_of_lt {F u : Circle} {α t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hu : angleTo F u < α) :
    toSph (chartC Ψ ((t : ℂ) * u)) ∈ wedgeSet Ψ F α :=
  ⟨_, ⟨_, ⟨t, ht, ht1, angleTo F u, angleTo_pos F u, hu, by rw [← Circle.coe_mul, mul_exp_angleTo]⟩,
    rfl⟩, rfl⟩

/-- **The corner after a direction of the arc `[F, B)` lies in the cone from `F` to `B`.** -/
theorem cornerSet_subset_wedgeSet_of_left (hD : (rimDirs Γ Φ).Finite) {F B w : Circle}
    (hB : B ∈ rimDirs Γ Φ) (hw : w = F ∨ angleTo F w < angleTo F B) :
    cornerSet Γ Φ Ψ w ⊆ wedgeSet Ψ F (angleTo F B) := by
  rcases hw with rfl | hlt
  · exact cornerSet_subset_wedgeSet hD hB
  have hψ := angleTo_mem F w
  have hα := angleTo_mem F B
  have hwB : angleTo w B = angleTo F B - angleTo F w := by
    apply angleTo_eq ⟨by linarith, by linarith [hψ.1, hα.2]⟩
    have key : F * Circle.exp (angleTo F w) * Circle.exp (angleTo F B - angleTo F w) = B := by
      rw [mul_assoc, ← Circle.exp_add, add_sub_cancel, mul_exp_angleTo]
    rw [mul_exp_angleTo] at key
    exact key.symm
  have hg := gap_le_angleTo hD w hB
  rintro _ ⟨_, ⟨y, ⟨r, hr, hr1, φ, hφ, hφg, rfl⟩, rfl⟩, rfl⟩
  have heq : w * Circle.exp φ = F * Circle.exp (angleTo F w + φ) := by
    rw [Circle.exp_add, ← mul_assoc, mul_exp_angleTo]
  refine ⟨_, ⟨_, ⟨r, hr, hr1, angleTo F w + φ, by linarith [hψ.1], by linarith, ?_⟩, rfl⟩, rfl⟩
  rw [← Circle.coe_mul, ← Circle.coe_mul, heq]

/-- **Corners come close to the centre.** Every open set around the centre of a chart meets the
corner after each direction. -/
theorem cornerSet_meets_nhds {c : OnePoint EuclideanPlane} (hp : IsPolar Γ c Φ)
    (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (hD : (rimDirs Γ Φ).Finite) (w : Circle)
    {V : Set (OnePoint EuclideanPlane)} (hV : IsOpen V) (hcV : c ∈ V) :
    (cornerSet Γ Φ Ψ w ∩ V).Nonempty := by
  set g := gap (rimDirs Γ Φ) w
  have hg := gap_pos hD w
  set u : Circle := w * Circle.exp (g / 2)
  have hcont : Continuous fun r : ℝ => toSph (chartC Ψ ((r : ℂ) * u)) :=
    continuous_toSph.comp (continuous_chartC.comp (by fun_prop))
  have h0 : (fun r : ℝ => toSph (chartC Ψ ((r : ℂ) * u))) 0 = c := by
    simp only [Complex.ofReal_zero, zero_mul]
    exact toSph_chartC_zero hp hΨ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hcont.continuousAt.preimage_mem_nhds (hV.mem_nhds (h0 ▸ hcV)))
  set r := min (ε / 2) 1
  have hr : 0 < r := lt_min (half_pos hε) one_pos
  have hrε : r ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_of_nonneg hr.le]
    linarith [min_le_left (ε / 2) 1]
  refine ⟨_, ⟨_, ⟨_, ⟨r, hr, min_le_right _ _, g / 2, half_pos hg, half_lt_self hg, ?_⟩, rfl⟩,
    rfl⟩, hball hrε⟩
  rw [Circle.coe_mul]

end ChartWedge

section Star

variable {Γ : Drawing (OnePoint EuclideanPlane)}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart Γ)} {v : OnePoint EuclideanPlane}
  {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ : C(ClosedUnitDisc, EuclideanPlane)}
  {z : DrawingDart Γ → Circle}

/-- **The cone up to a dart misses the next dart.** In a counterclockwise star at `v`, let `c` be
a dart at `v` and `F ≠ z c` a direction. Let `Z` be a nice set whose directions are among `F`,
`z c` and the direction of the dart `R.rot c` after `c`. Then the open cone from `F`
counterclockwise to `z c` misses `Z`. -/
theorem disjoint_wedgeSet_of_rot (h : IsCcwStar Γ γ R v Φ z) (hγ : EdgePar Γ γ)
    (hR : IsDrawingRotation Γ γ R) (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    {Z : Set (OnePoint EuclideanPlane)} (hZ : IsGammaNice Γ Z) {c : DrawingDart Γ}
    (hc : dartVertex γ c = v) {F : Circle} (hF : F ∈ rimDirs Γ Φ) (hFc : F ≠ z c)
    (hdirs : ∀ w, polarRimMap Φ w ∈ Z → w = F ∨ w = z c ∨ w = z (R.rot c)) :
    Disjoint (wedgeSet Ψ F (angleTo F (z c))) Z := by
  have hD := h.rimDirs_finite hγ
  have hα := angleTo_mem F (z c)
  apply disjoint_wedgeSet h.polar hΨ hZ
  intro θ hθ hmem
  have hθ2 : θ ∈ Ioc 0 (2 * Real.pi) := ⟨hθ.1, hθ.2.le.trans hα.2⟩
  rcases hdirs _ hmem with h1 | h1 | h1
  · have := angleTo_eq hθ2 h1.symm
    rw [angleTo_self] at this
    linarith [hθ.2, hα.2]
  · have := angleTo_eq hθ2 h1.symm
    linarith [hθ.2]
  · -- the next direction after `z c` would lie strictly between `F` and `z c`
    rw [← h.next_eq hγ hR hc] at h1
    set g := gap (rimDirs Γ Φ) (z c)
    have hg := gap_pos hD (z c)
    have hgβ : g ≤ angleTo (z c) F := gap_le_angleTo hD _ hF
    have hβ := angleTo_swap hFc
    have hsum : 0 < angleTo (z c) F + θ ∧ angleTo (z c) F + θ ≤ 2 * Real.pi := by
      constructor <;> linarith [hθ.1, hθ.2, angleTo_pos (z c) F]
    have heq : z c * Circle.exp g = z c * Circle.exp (angleTo (z c) F + θ) := by
      rw [← h1, Circle.exp_add, ← mul_assoc, mul_exp_angleTo]
    have h2 := angleTo_eq hsum heq
    have h3 := angleTo_eq ⟨hg, gap_le_two_pi hD _⟩ (rfl : z c * Circle.exp g = z c * Circle.exp g)
    linarith [hθ.1]

end Star

end GraphMinor.GM06
