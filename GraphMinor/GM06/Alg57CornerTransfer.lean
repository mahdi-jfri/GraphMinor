module

public import GraphMinor.GM06.Alg57PolarStar

/-!
# Moving a corner along an edge

Step 1 of the proof of Lemma 3 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`) follows
the half-band on the left of an edge from one end to the other. We follow it through positive polar
charts at points of the edge. Here we compare two such charts.

A curve `G : ℝ → S` *runs out along* the ray of direction `W` of a chart from time `a` if, for
`t` just after `a`, the point `G t` is on that ray at a radius that grows with `t`
(`RunsOut`). It *runs in* along the ray up to time `b` if, for `t` just before `b`, the point
`G t` is on the ray at a radius that shrinks to `0` (`RunsIn`).

Let the second chart be centred on the ray `W₁` of the first, and let `G` run out along its ray
`W₂`, while `G` lies on the ray `W₁` of the first chart. If the radius in the first chart grows,
the corner after `W₂` is the corner after `W₁` (`cornerRegion_eq_of_out`). If it shrinks, the
corner after `W₂` is the corner before `W₁` (`cornerRegion_eq_of_in`). Both follow from
`RayOverlap.sector_transfer_out` and `RayOverlap.sector_transfer_in`.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The curve `G` runs out along the ray of direction `W` of the chart `Ψ` from time `a`, for a
time `δ`. -/
def RunsOut (Ψ : C(ClosedUnitDisc, EuclideanPlane)) (W : Circle)
    (G : ℝ → OnePoint EuclideanPlane) (a δ : ℝ) : Prop :=
  0 < δ ∧ ∃ ρ : ℝ → ℝ, ContinuousOn ρ (Icc a (a + δ)) ∧ ρ a = 0 ∧
    StrictMonoOn ρ (Icc a (a + δ)) ∧
    ∀ t ∈ Icc a (a + δ), ρ t < 1 ∧ G t = toSph (chartC Ψ ((ρ t : ℂ) * W))

/-- The curve `G` runs in along the ray of direction `W` of the chart `Ψ` up to time `b`, for a
time `δ`. -/
def RunsIn (Ψ : C(ClosedUnitDisc, EuclideanPlane)) (W : Circle)
    (G : ℝ → OnePoint EuclideanPlane) (b δ : ℝ) : Prop :=
  0 < δ ∧ ∃ ρ : ℝ → ℝ, ContinuousOn ρ (Icc (b - δ) b) ∧ ρ b = 0 ∧
    StrictAntiOn ρ (Icc (b - δ) b) ∧
    ∀ t ∈ Icc (b - δ) b, ρ t < 1 ∧ G t = toSph (chartC Ψ ((ρ t : ℂ) * W))

section Transfer

variable {Γ : Drawing (OnePoint EuclideanPlane)} {c₁ c₂ : OnePoint EuclideanPlane}
  {Φ₁ Φ₂ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ₁ Ψ₂ : C(ClosedUnitDisc, EuclideanPlane)}
  {G : ℝ → OnePoint EuclideanPlane}

/-- A small closed disc about the centre of a chart lies in a given open set about it. -/
theorem exists_closedBall_image_subset {χ : ℂ → ℂ} (hχ : Continuous χ) {O : Set ℂ}
    (hO : IsOpen O) (h0 : χ 0 ∈ O) : ∃ R, 0 < R ∧ R ≤ 1 ∧ χ '' closedBall 0 R ⊆ O := by
  obtain ⟨R₀, hR₀, hball⟩ := Metric.isOpen_iff.mp (hO.preimage hχ) 0 h0
  refine ⟨min (R₀ / 2) 1, lt_min (half_pos hR₀) one_pos, min_le_right _ _, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  apply hball
  rw [mem_ball_zero_iff]
  rw [mem_closedBall_zero_iff] at hy
  linarith [min_le_left (R₀ / 2) 1]

/-- Three increasing times just after `a` at which a radius that starts at `0` is at most
`R`. -/
theorem exists_three_times {ρ : ℝ → ℝ} {a δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hc : ContinuousOn ρ (Icc a (a + δ))) (h0 : ρ a = 0) :
    ∃ t₁ t₂ t₃, a < t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ ≤ a + δ ∧ ρ t₃ ≤ R := by
  have hcont : ContinuousWithinAt ρ (Icc a (a + δ)) a :=
    hc a ⟨le_rfl, by linarith⟩
  obtain ⟨η, hη, hηb⟩ := Metric.continuousWithinAt_iff.mp hcont R hR
  set t₃ := a + min (η / 2) δ
  have hm : 0 < min (η / 2) δ := lt_min (half_pos hη) hδ
  refine ⟨a + min (η / 2) δ / 3, a + 2 * (min (η / 2) δ / 3), t₃, by linarith, by linarith,
    by linarith, by linarith [min_le_right (η / 2) δ], ?_⟩
  have hmem : t₃ ∈ Icc a (a + δ) := ⟨by linarith, by linarith [min_le_right (η / 2) δ]⟩
  have hd : dist t₃ a < η := by
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith [min_le_left (η / 2) δ]
  have := hηb hmem hd
  rw [h0, Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans this.le

/-- The common setting of the two transfer lemmas: two positive polar charts, a direction `W₁`
of the first star, the centre of the second chart on the ray `W₁`, and `G` running out along the
ray `W₂` of the second chart while it stays on the ray `W₁`. -/
theorem cornerRegion_transfer_aux
    (hp₁ : IsPolar Γ c₁ Φ₁) (hΨ₁ : ∀ x, Φ₁ x = (Ψ₁ x : OnePoint EuclideanPlane))
    (hpos₁ : 0 < wind (fun w : Circle => chartC Ψ₁ w) (chartC Ψ₁ 0))
    (hD₁ : (rimDirs Γ Φ₁).Finite)
    (hp₂ : IsPolar Γ c₂ Φ₂) (hΨ₂ : ∀ x, Φ₂ x = (Ψ₂ x : OnePoint EuclideanPlane))
    (hpos₂ : 0 < wind (fun w : Circle => chartC Ψ₂ w) (chartC Ψ₂ 0))
    (hD₂ : (rimDirs Γ Φ₂).Finite)
    {W₁ W₁' W₂ : Circle} (hW₁ : W₁ ∈ rimDirs Γ Φ₁) {a δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hout : RunsOut Ψ₂ W₂ G a δ₂) (hc₂ : c₂ = G a) {ρ₁ : ℝ → ℝ}
    (hray : ∀ t ∈ Icc a (a + δ₁), 0 < ρ₁ t ∧ ρ₁ t < 1 ∧
      G t = toSph (chartC Ψ₁ ((ρ₁ t : ℂ) * W₁))) :
    ∃ ε₁ ε₂ R s₁ s₂ s₃ t₁ t₂ t₃,
      RayOverlap (chartC Ψ₁) (chartC Ψ₂) W₁ W₂ ε₁ ε₂ R (toSph ⁻¹' Γ.U) ∧
      ε₁ < gap (rimDirs Γ Φ₁) W₁ ∧ ε₁ < gap (rimDirs Γ Φ₁) W₁' ∧
      ε₂ < gap (rimDirs Γ Φ₂) W₂ ∧
      0 < s₁ ∧ s₁ < s₂ ∧ s₂ < s₃ ∧ s₃ ≤ R ∧ a < t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ ≤ a + δ₁ ∧
      chartC Ψ₂ ((s₁ : ℂ) * W₂) = chartC Ψ₁ ((ρ₁ t₁ : ℂ) * W₁) ∧
      chartC Ψ₂ ((s₂ : ℂ) * W₂) = chartC Ψ₁ ((ρ₁ t₂ : ℂ) * W₁) ∧
      chartC Ψ₂ ((s₃ : ℂ) * W₂) = chartC Ψ₁ ((ρ₁ t₃ : ℂ) * W₁) := by
  obtain ⟨hδ₂, ρ₂, hρc, hρ0, hρm, hρG⟩ := hout
  have hg₁ := gap_pos hD₁ W₁
  have hg₁' := gap_pos hD₁ W₁'
  have hg₂ := gap_pos hD₂ W₂
  set ε₁ : ℝ := min (min (gap (rimDirs Γ Φ₁) W₁) (gap (rimDirs Γ Φ₁) W₁')) (Real.pi / 2) / 2
  have hm₁ : 0 < min (min (gap (rimDirs Γ Φ₁) W₁) (gap (rimDirs Γ Φ₁) W₁')) (Real.pi / 2) :=
    lt_min (lt_min hg₁ hg₁') (by positivity)
  have hε₁ : 0 < ε₁ := half_pos hm₁
  have hε₁' : ε₁ < Real.pi / 2 := (half_lt_self hm₁).trans_le (min_le_right _ _)
  have hε₁g : ε₁ < gap (rimDirs Γ Φ₁) W₁ :=
    (half_lt_self hm₁).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε₁g' : ε₁ < gap (rimDirs Γ Φ₁) W₁' :=
    (half_lt_self hm₁).trans_le ((min_le_left _ _).trans (min_le_right _ _))
  set ε₂ : ℝ := min (gap (rimDirs Γ Φ₂) W₂) (Real.pi / 2) / 2
  have hm₂ : 0 < min (gap (rimDirs Γ Φ₂) W₂) (Real.pi / 2) := lt_min hg₂ (by positivity)
  have hε₂ : 0 < ε₂ := half_pos hm₂
  have hε₂' : ε₂ < Real.pi / 2 := (half_lt_self hm₂).trans_le (min_le_right _ _)
  have hε₂g : ε₂ < gap (rimDirs Γ Φ₂) W₂ := (half_lt_self hm₂).trans_le (min_le_left _ _)
  -- the centre of the second chart on the ray of the first
  have ha := hray a ⟨le_rfl, by linarith⟩
  have hcentre : chartC Ψ₂ 0 = chartC Ψ₁ ((ρ₁ a : ℂ) * W₁) := by
    apply toSph_injective
    rw [toSph_chartC_zero hp₂ hΨ₂, hc₂, ha.2.2]
  have hopen : IsOpen (chartC Ψ₁ '' dsec W₁ ε₁ 1) :=
    isOpen_image_of_injOn (isOpen_openSector _ _ _) continuous_chartC.continuousOn
      ((chartC_injOn hΨ₁ hp₁.inj).mono fun y hy =>
        mem_closedBall_zero_iff.mpr (hy : y ∈ dsec W₁ ε₁ 1).1.le)
  obtain ⟨R, hR, hR1, hball⟩ := exists_closedBall_image_subset continuous_chartC hopen
    (by rw [hcentre]; exact ⟨_, ray_mem_dsec hε₁ hε₁' ha.1 ha.2.1, rfl⟩)
  -- three times
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hsub : Icc a (a + min δ₁ δ₂) ⊆ Icc a (a + δ₂) :=
    Icc_subset_Icc le_rfl (by linarith [min_le_right δ₁ δ₂])
  obtain ⟨t₁, t₂, t₃, h1, h12, h23, h3, hR3⟩ :=
    exists_three_times hδ hR (hρc.mono hsub) hρ0
  have hmem : ∀ t, a ≤ t → t ≤ t₃ → t ∈ Icc a (a + δ₂) := fun t h h' =>
    ⟨h, by linarith [min_le_right δ₁ δ₂]⟩
  have hmem₁ : ∀ t, a ≤ t → t ≤ t₃ → t ∈ Icc a (a + δ₁) := fun t h h' =>
    ⟨h, by linarith [min_le_left δ₁ δ₂]⟩
  have hs₁ : 0 < ρ₂ t₁ := by
    rw [← hρ0]; exact hρm (hmem a le_rfl (by linarith)) (hmem t₁ h1.le (by linarith)) h1
  have hs₁₂ : ρ₂ t₁ < ρ₂ t₂ := hρm (hmem _ h1.le (by linarith)) (hmem _ (by linarith)
    (by linarith)) h12
  have hs₂₃ : ρ₂ t₂ < ρ₂ t₃ := hρm (hmem _ (by linarith) (by linarith)) (hmem _ (by linarith)
    le_rfl) h23
  have heq : ∀ t, a ≤ t → t ≤ t₃ →
      chartC Ψ₂ ((ρ₂ t : ℂ) * W₂) = chartC Ψ₁ ((ρ₁ t : ℂ) * W₁) := fun t h h' => by
    apply toSph_injective
    rw [← (hρG t (hmem t h h')).2, (hray t (hmem₁ t h h')).2.2]
  refine ⟨ε₁, ε₂, R, ρ₂ t₁, ρ₂ t₂, ρ₂ t₃, t₁, t₂, t₃, ⟨continuous_chartC, chartC_injOn hΨ₁ hp₁.inj,
    hpos₁, continuous_chartC, chartC_injOn hΨ₂ hp₂.inj, hpos₂, hε₁, hε₁', hε₂, hε₂', hR, hR1,
    hball, ?_, ?_⟩, hε₁g, hε₁g', hε₂g, hs₁, hs₁₂, hs₂₃, hR3, h1, h12, h23,
    by linarith [min_le_left δ₁ δ₂], heq _ h1.le (by linarith), heq _ (by linarith) (by linarith),
    heq _ (by linarith) le_rfl⟩
  · intro t ht ht1
    exact (chart_ray_mem_iff hp₁ hΨ₁ (isGammaNice_U Γ) W₁ ht ht1.le).mpr hW₁
  · rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hyU
    have hy' : y ∈ osecP W₂ ε₂ 1 := openSector_mono hR1 hy
    have := image_osecP_subset_cornerRegion hp₂ hΨ₂ hD₂ W₂ hε₂ hε₂' hε₂g ⟨_, ⟨y, hy', rfl⟩, rfl⟩
    exact region_subset (cornerRegion_mem hp₂ hΨ₂ hD₂ W₂) this hyU

/-- **A corner carried outward along a ray.** If the second chart runs out along the ray `W₁`
of the first chart, outward, its corner after `W₂` is the corner after `W₁`. -/
theorem cornerRegion_eq_of_out
    (hp₁ : IsPolar Γ c₁ Φ₁) (hΨ₁ : ∀ x, Φ₁ x = (Ψ₁ x : OnePoint EuclideanPlane))
    (hpos₁ : 0 < wind (fun w : Circle => chartC Ψ₁ w) (chartC Ψ₁ 0))
    (hD₁ : (rimDirs Γ Φ₁).Finite)
    (hp₂ : IsPolar Γ c₂ Φ₂) (hΨ₂ : ∀ x, Φ₂ x = (Ψ₂ x : OnePoint EuclideanPlane))
    (hpos₂ : 0 < wind (fun w : Circle => chartC Ψ₂ w) (chartC Ψ₂ 0))
    (hD₂ : (rimDirs Γ Φ₂).Finite)
    {W₁ W₂ : Circle} (hW₁ : W₁ ∈ rimDirs Γ Φ₁) {a δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hout : RunsOut Ψ₂ W₂ G a δ₂) (hc₂ : c₂ = G a) {ρ₁ : ℝ → ℝ}
    (hray : ∀ t ∈ Icc a (a + δ₁), 0 < ρ₁ t ∧ ρ₁ t < 1 ∧
      G t = toSph (chartC Ψ₁ ((ρ₁ t : ℂ) * W₁)))
    (hmono : StrictMonoOn ρ₁ (Icc a (a + δ₁))) :
    cornerRegion Γ Φ₂ W₂ = cornerRegion Γ Φ₁ W₁ := by
  obtain ⟨ε₁, ε₂, R, s₁, s₂, s₃, t₁, t₂, t₃, hov, hε₁g, -, hε₂g, hs₁, hs₁₂, hs₂₃, hs₃, h1, h12,
    h23, h3, he₁, he₂, he₃⟩ :=
    cornerRegion_transfer_aux (W₁' := W₁) hp₁ hΨ₁ hpos₁ hD₁ hp₂ hΨ₂ hpos₂ hD₂ hW₁ hδ₁ hout hc₂
      hray
  have hm : ∀ t, a ≤ t → t ≤ t₃ → t ∈ Icc a (a + δ₁) := fun t h h' => ⟨h, by linarith⟩
  have hτ := hray t₁ (hm _ h1.le (by linarith))
  have hτ₃ := hray t₃ (hm _ (by linarith) le_rfl)
  have hsub := hov.sector_transfer_out hs₁ hs₁₂ hs₂₃ hs₃ hτ.1
    (hmono (hm _ h1.le (by linarith)) (hm _ (by linarith) (by linarith)) h12)
    (hmono (hm _ (by linarith) (by linarith)) (hm _ (by linarith) le_rfl) h23) hτ₃.2.1.le
    he₁ he₂ he₃
  have hR := hov.R₂_pos
  obtain ⟨y, hy⟩ : (osecP W₂ ε₂ R).Nonempty :=
    ⟨_, mem_osecP_coord hov.ε₂_pos hov.ε₂_lt hR⟩
  obtain ⟨y', hy', hyy⟩ := hsub ⟨y, hy, rfl⟩
  have h₂ := image_osecP_subset_cornerRegion hp₂ hΨ₂ hD₂ W₂ hov.ε₂_pos hov.ε₂_lt hε₂g
    ⟨_, ⟨y, openSector_mono hov.R₂_le hy, rfl⟩, rfl⟩
  have h₁ := image_osecP_subset_cornerRegion hp₁ hΨ₁ hD₁ W₁ hov.ε₁_pos hov.ε₁_lt hε₁g
    ⟨_, ⟨y', hy', rfl⟩, rfl⟩
  rw [hyy] at h₁
  exact region_eq_of_mem (cornerRegion_mem hp₂ hΨ₂ hD₂ W₂) (cornerRegion_mem hp₁ hΨ₁ hD₁ W₁)
    h₂ h₁

/-- **A corner carried inward along a ray.** If the second chart runs out along the ray `W₁` of
the first chart, inward, its corner after `W₂` is the corner before `W₁`, which is the corner
after the direction `W₁'` of the star before `W₁`. -/
theorem cornerRegion_eq_of_in
    (hp₁ : IsPolar Γ c₁ Φ₁) (hΨ₁ : ∀ x, Φ₁ x = (Ψ₁ x : OnePoint EuclideanPlane))
    (hpos₁ : 0 < wind (fun w : Circle => chartC Ψ₁ w) (chartC Ψ₁ 0))
    (hD₁ : (rimDirs Γ Φ₁).Finite)
    (hp₂ : IsPolar Γ c₂ Φ₂) (hΨ₂ : ∀ x, Φ₂ x = (Ψ₂ x : OnePoint EuclideanPlane))
    (hpos₂ : 0 < wind (fun w : Circle => chartC Ψ₂ w) (chartC Ψ₂ 0))
    (hD₂ : (rimDirs Γ Φ₂).Finite)
    {W₁ W₁' W₂ : Circle} (hW₁ : W₁ ∈ rimDirs Γ Φ₁)
    (hprev : W₁' * Circle.exp (gap (rimDirs Γ Φ₁) W₁') = W₁) {a δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hout : RunsOut Ψ₂ W₂ G a δ₂) (hc₂ : c₂ = G a) {ρ₁ : ℝ → ℝ}
    (hray : ∀ t ∈ Icc a (a + δ₁), 0 < ρ₁ t ∧ ρ₁ t < 1 ∧
      G t = toSph (chartC Ψ₁ ((ρ₁ t : ℂ) * W₁)))
    (hanti : StrictAntiOn ρ₁ (Icc a (a + δ₁))) :
    cornerRegion Γ Φ₂ W₂ = cornerRegion Γ Φ₁ W₁' := by
  obtain ⟨ε₁, ε₂, R, s₁, s₂, s₃, t₁, t₂, t₃, hov, -, hε₁g', hε₂g, hs₁, hs₁₂, hs₂₃, hs₃, h1, h12,
    h23, h3, he₁, he₂, he₃⟩ :=
    cornerRegion_transfer_aux (W₁' := W₁') hp₁ hΨ₁ hpos₁ hD₁ hp₂ hΨ₂ hpos₂ hD₂ hW₁ hδ₁ hout hc₂
      hray
  have hm : ∀ t, a ≤ t → t ≤ t₃ → t ∈ Icc a (a + δ₁) := fun t h h' => ⟨h, by linarith⟩
  have hτ := hray t₁ (hm _ h1.le (by linarith))
  have hτ₃ := hray t₃ (hm _ (by linarith) le_rfl)
  have hsub := hov.sector_transfer_in hs₁ hs₁₂ hs₂₃ hs₃ hτ₃.1
    (hanti (hm _ (by linarith) (by linarith)) (hm _ (by linarith) le_rfl) h23)
    (hanti (hm _ h1.le (by linarith)) (hm _ (by linarith) (by linarith)) h12) hτ.2.1.le
    he₁ he₂ he₃
  have hR := hov.R₂_pos
  obtain ⟨y, hy⟩ : (osecP W₂ ε₂ R).Nonempty :=
    ⟨_, mem_osecP_coord hov.ε₂_pos hov.ε₂_lt hR⟩
  obtain ⟨y', hy', hyy⟩ := hsub ⟨y, hy, rfl⟩
  have h₂ := image_osecP_subset_cornerRegion hp₂ hΨ₂ hD₂ W₂ hov.ε₂_pos hov.ε₂_lt hε₂g
    ⟨_, ⟨y, openSector_mono hov.R₂_le hy, rfl⟩, rfl⟩
  rw [← hprev] at hy'
  have h₁ := image_osecM_subset_cornerRegion hp₁ hΨ₁ hD₁ W₁' hov.ε₁_pos hov.ε₁_lt hε₁g'
    ⟨_, ⟨y', hy', rfl⟩, rfl⟩
  rw [hyy] at h₁
  exact region_eq_of_mem (cornerRegion_mem hp₂ hΨ₂ hD₂ W₂) (cornerRegion_mem hp₁ hΨ₁ hD₁ W₁')
    h₂ h₁

end Transfer

end GraphMinor.GM06
