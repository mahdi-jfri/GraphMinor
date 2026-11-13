module

public import GraphMinor.GM06.Alg57CornerTransfer

/-!
# Curves running along a ray of a polar chart

To follow an edge through charts we need the edge to run along a ray of each chart, with a
radius that moves monotonically. This file proves that this happens as soon as the edge lies on
one ray near the centre (`runsOut_of_on_ray`): the radius is continuous, because a polar chart is
an embedding, and it is injective, because the edge is, so it is strictly monotone.

`chart_point_polar` writes a point of a polar chart other than its centre in polar form, and
`RunsOut.runsIn` turns a curve around.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

variable {Γ : Drawing (OnePoint EuclideanPlane)} {c : OnePoint EuclideanPlane}
  {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {Ψ : C(ClosedUnitDisc, EuclideanPlane)}

/-- A point of a polar chart other than its centre, in polar form. -/
theorem chart_point_polar (hp : IsPolar Γ c Φ) (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    {y : OnePoint EuclideanPlane} (hy : y ∈ range Φ) (hyc : y ≠ c) :
    ∃ r : ℝ, ∃ w : Circle, 0 < r ∧ r ≤ 1 ∧ y = toSph (chartC Ψ ((r : ℂ) * w)) := by
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨z, hz, rfl⟩ := exists_discPt_eq x
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [discPt_zero, hp.centre] at hyc
    exact hyc rfl
  refine ⟨‖z‖, unitOf z hz0, norm_pos_iff.mpr hz0, mem_closedBall_zero_iff.mp hz, ?_⟩
  rw [toSph_chartC hΨ, ← eq_norm_mul_unitOf hz0]

/-- **Running out along a ray.** If an injective curve leaves the centre of a polar chart along
one ray, it runs out along that ray. -/
theorem runsOut_of_on_ray (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    {G : ℝ → OnePoint EuclideanPlane} (hG : Continuous G) {a δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hp : IsPolar Γ (G a) Φ) (hinj : InjOn G (Icc a (a + δ₀))) {W : Circle}
    (hon : ∀ t ∈ Ioc a (a + δ₀), ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      G t = toSph (chartC Ψ ((r : ℂ) * W))) :
    RunsOut Ψ W G a (δ₀ / 2) := by
  classical
  have hemb : IsEmbedding Φ := (Φ.continuous.isClosedEmbedding hp.inj).isEmbedding
  let j : OnePoint EuclideanPlane → ClosedUnitDisc := fun y =>
    if h : y ∈ range Φ then h.choose else polarCentre
  have hj : ∀ y ∈ range Φ, Φ (j y) = y := fun y hy => by
    simp only [j, dite_eq_left_iff, dif_pos hy]; exact hy.choose_spec
  have hrange : ∀ t ∈ Icc a (a + δ₀), G t ∈ range Φ := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, ← hp.centre]; exact mem_range_self _
    · obtain ⟨r, -, -, hr⟩ := hon t ⟨h, ht.2⟩
      rw [hr, toSph_chartC hΨ]; exact mem_range_self _
  have hk : ContinuousOn (fun t => j (G t)) (Icc a (a + δ₀)) := by
    rw [hemb.isInducing.continuousOn_iff]
    exact hG.continuousOn.congr fun t ht => hj _ (hrange t ht)
  let ρ : ℝ → ℝ := fun t => ‖(j (G t)).1‖
  have hρc : ContinuousOn ρ (Icc a (a + δ₀)) :=
    continuous_norm.comp_continuousOn (continuous_subtype_val.comp_continuousOn hk)
  have hρa : ρ a = 0 := by
    have : j (G a) = polarCentre := hp.inj (by rw [hj _ (hrange a ⟨le_rfl, by linarith⟩),
      hp.centre])
    simp only [ρ, this, polarCentre, norm_zero]
  have hρt : ∀ t ∈ Ioc a (a + δ₀), ∀ r : ℝ, 0 < r → r ≤ 1 →
      G t = toSph (chartC Ψ ((r : ℂ) * W)) → ρ t = r := by
    intro t ht r hr hr1 hGt
    have h1 : j (G t) = discPt ((r : ℂ) * W) := hp.inj (by
      rw [hj _ (hrange t ⟨ht.1.le, ht.2⟩), hGt, toSph_chartC hΨ])
    simp only [ρ, h1]
    change ‖planeOf (ballClamp ((r : ℂ) * W))‖ = r
    rw [ballClamp_of_norm_le (by
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
      exact hr1), LinearIsometryEquiv.norm_map, norm_mul, Circle.norm_coe, mul_one,
      Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hGρ : ∀ t ∈ Icc a (a + δ₀), G t = toSph (chartC Ψ ((ρ t : ℂ) * W)) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      rw [hρa, Complex.ofReal_zero, zero_mul, toSph_chartC_zero hp hΨ]
    · obtain ⟨r, hr, hr1, hGt⟩ := hon t ⟨h, ht.2⟩
      rw [hρt t ⟨h, ht.2⟩ r hr hr1 hGt]
      exact hGt
  have hρinj : InjOn ρ (Icc a (a + δ₀)) := by
    intro t ht t' ht' h
    apply hinj ht ht'
    rw [hGρ t ht, hGρ t' ht', h]
  have hρ0 : ∀ t ∈ Icc a (a + δ₀), 0 ≤ ρ t := fun t _ => norm_nonneg _
  have hle : ρ a ≤ ρ (a + δ₀) := by
    rw [hρa]
    exact hρ0 _ ⟨by linarith, le_rfl⟩
  have hmono : StrictMonoOn ρ (Icc a (a + δ₀)) :=
    ContinuousOn.strictMonoOn_of_injOn_Icc (by linarith) hle hρc hρinj
  have hρ1 : ρ (a + δ₀) ≤ 1 := by
    obtain ⟨r, hr, hr1, hGt⟩ := hon (a + δ₀) ⟨by linarith, le_rfl⟩
    rw [hρt _ ⟨by linarith, le_rfl⟩ r hr hr1 hGt]
    exact hr1
  have hsub : Icc a (a + δ₀ / 2) ⊆ Icc a (a + δ₀) := Icc_subset_Icc le_rfl (by linarith)
  refine ⟨half_pos hδ₀, ρ, hρc.mono hsub, hρa, hmono.mono hsub, fun t ht => ⟨?_, hGρ t (hsub ht)⟩⟩
  calc ρ t ≤ ρ (a + δ₀ / 2) := hmono.monotoneOn (hsub ht) ⟨by linarith, by linarith⟩ ht.2
    _ < ρ (a + δ₀) := hmono ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    _ ≤ 1 := hρ1

/-- A curve that runs out along a ray, read backwards, runs in along it. -/
theorem RunsOut.runsIn {W : Circle} {G : ℝ → OnePoint EuclideanPlane} {b δ : ℝ}
    (h : RunsOut Ψ W (fun t => G (-t)) (-b) δ) : RunsIn Ψ W G b δ := by
  obtain ⟨hδ, ρ, hρc, hρ0, hmono, hρG⟩ := h
  have hmaps : MapsTo (fun s : ℝ => -s) (Icc (b - δ) b) (Icc (-b) (-b + δ)) :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  refine ⟨hδ, fun s => ρ (-s), hρc.comp continuousOn_neg hmaps, by simpa using hρ0, ?_, ?_⟩
  · intro s hs s' hs' hss'
    exact hmono (hmaps hs') (hmaps hs) (by linarith)
  · intro s hs
    have := hρG (-s) (hmaps hs)
    simp only [neg_neg] at this
    exact this

end GraphMinor.GM06
