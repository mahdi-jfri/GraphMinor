module

public import GraphMinor.GM11.LocalCone
import GraphMinor.GM11.PaintingCells
import GraphMinor.Surface.InvarianceOfDomain

/-!
# Polar charts inside a prescribed neighbourhood

The local side interpretation in VI (5.7), page 133, works inside a
single inverse chart of the angular cover. Shrink a polar chart by a
positive radial factor to place it in any prescribed open neighbourhood
of its centre. Scaling preserves the drawing atoms on radial segments.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- A polar chart on a closed surface can be restricted to an arbitrarily small open neighbourhood. -/
theorem exists_small_polar_chart_with_factor {S : Type u} [TopologicalSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    {O : Set S} (hO : IsOpen O) (hs : s ∈ O) :
    ∃ c : I, (0 : ℝ) < c ∧ ∃ Ψ : C(ClosedUnitDisc, S),
      IsPolar Γ s Ψ ∧ range Ψ ⊆ O ∧ ∀ x, Ψ x = Φ (discScale c x) := by
  let : T2Space S := hS.2.1
  have hpre : IsOpen (Φ ⁻¹' O) := hO.preimage Φ.continuous
  have hcpre : polarCentre ∈ Φ ⁻¹' O := by
    change Φ polarCentre ∈ O
    rw [hp.centre]
    exact hs
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hpre polarCentre hcpre
  have hsmall : 0 < min (ε / 2) (1 / 2 : ℝ) := lt_min (half_pos hε) (by norm_num)
  let c : I := ⟨min (ε / 2) (1 / 2 : ℝ), hsmall.le,
    (min_le_right _ _).trans (by norm_num)⟩
  have hc : (0 : ℝ) < c := hsmall
  have hcε : (c : ℝ) < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  let κ : ClosedUnitDisc → ClosedUnitDisc := discScale c
  have hκc : Continuous κ := continuous_discScale.comp (continuous_const.prodMk continuous_id)
  have hκi : Function.Injective κ := by
    intro x y hxy
    apply Subtype.ext
    have hh := congrArg Subtype.val hxy
    exact smul_right_injective _ hc.ne' hh
  have hκ0 : κ polarCentre = polarCentre := Subtype.ext (by simp [κ, discScale, polarCentre])
  have hκnorm (x : ClosedUnitDisc) : ‖(κ x).1‖ ≤ (c : ℝ) := by
    change ‖(c : ℝ) • x.1‖ ≤ (c : ℝ)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg c.2.1]
    have hx : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx c.2.1
  let Ψ : C(ClosedUnitDisc, S) := ⟨fun x => Φ (κ x), Φ.continuous.comp hκc⟩
  have hΨi : Function.Injective Ψ := hp.inj.comp hκi
  have hΨ0 : Ψ polarCentre = s := by
    change Φ (κ polarCentre) = s
    rw [hκ0, hp.centre]
  have hΨnhd : s ∈ interior (range Ψ) := by
    have hemb : IsEmbedding Ψ := (Ψ.continuous.isClosedEmbedding hΨi).isEmbedding
    let e : ClosedUnitDisc ≃ₜ range Ψ := hemb.toHomeomorph
    have hD : IsClosedDisc (range Ψ) := ⟨e⟩
    rw [interior_eq_sdiff_discBd hS hD, disc_boundary (range Ψ) e]
    refine ⟨⟨_, hΨ0⟩, ?_⟩
    rintro ⟨y, hy, hye⟩
    have hy0 : y = polarCentre := by
      apply hΨi
      rw [hΨ0]
      exact hye
    have hn : ‖y.1‖ = 1 := mem_sphere_zero_iff_norm.mp hy
    rw [hy0] at hn
    simpa [polarCentre] using hn
  have hcomm (r : I) (x : ClosedUnitDisc) : κ (discScale r x) = discScale r (κ x) := by
    apply Subtype.ext
    change (c : ℝ) • ((r : ℝ) • x.1) = (r : ℝ) • ((c : ℝ) • x.1)
    simp only [smul_smul, mul_comm]
  refine ⟨c, hc, Ψ, ⟨hΨi, hΨ0, hΨnhd, ?_⟩, ?_, fun _ => rfl⟩
  · intro x hx r hr
    have hkx : κ x ≠ polarCentre := fun h => hx (hκi (h.trans hκ0.symm))
    obtain ⟨a, ha, hxA, hrA⟩ := hp.ray (κ x) hkx r hr
    refine ⟨a, ha, hxA, ?_⟩
    change Φ (κ (discScale r x)) ∈ a
    rw [hcomm]
    exact hrA
  · rintro _ ⟨x, rfl⟩
    apply hball
    change dist (κ x).1 (0 : EuclideanPlane) < ε
    rw [dist_zero_right]
    exact (hκnorm x).trans_lt hcε

/-- A polar chart on a closed surface can be restricted to an arbitrarily small open neighbourhood. -/
theorem exists_small_polar_chart {S : Type u} [TopologicalSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    {O : Set S} (hO : IsOpen O) (hs : s ∈ O) :
    ∃ Ψ : C(ClosedUnitDisc, S), IsPolar Γ s Ψ ∧ range Ψ ⊆ O := by
  obtain ⟨c, hc, Ψ, hΨ, hΨO, hscale⟩ := exists_small_polar_chart_with_factor hS hp hO hs
  exact ⟨Ψ, hΨ, hΨO⟩

end GraphMinor.GM06
