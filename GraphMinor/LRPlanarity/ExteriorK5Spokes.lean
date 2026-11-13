module

public import GraphMinor.Surface.DiscPolygon
import Mathlib.Analysis.Convex.Segment

/-!
# Radial spokes for the exterior complete-graph construction

Part IV, Section 7c of the planarity note uses the images of radial segments
under a disc homeomorphism. Distinct unit radii meet only at the origin.
Each radius meets the unit circle only at its end. A disc chart transfers
both properties to the given disc.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Metric

private theorem mem_radius {p x : ℂ} (hx : x ∈ segment ℝ 0 p) :
    ∃ t : ℝ, t ∈ Icc 0 1 ∧ x = t • p := by
  rw [segment_eq_image] at hx
  obtain ⟨t, ht, hx⟩ := hx
  exact ⟨t, ht, by simpa using hx.symm⟩

private theorem radius_subset {p : ℂ} (hp : ‖p‖ = 1) :
    segment ℝ 0 p ⊆ closedBall (0 : ℂ) 1 := by
  apply (convex_closedBall (0 : ℂ) 1).segment_subset
  · simp
  · exact mem_closedBall_zero_iff.mpr hp.le

/-- Two different unit radii have just their center in common. This supplies
spoke disjointness in Part IV, Section 7c. -/
theorem unit_radii_inter {p q : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : p ≠ q) : segment ℝ 0 p ∩ segment ℝ 0 q = {0} := by
  ext x
  constructor
  · rintro ⟨hx, hy⟩
    obtain ⟨s, hs, rfl⟩ := mem_radius hx
    obtain ⟨t, ht, he⟩ := mem_radius hy
    have hn : s = t := by
      have hn := congrArg norm he
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1,
        abs_of_nonneg ht.1, hp, hq, mul_one] using hn
    rw [← hn] at he
    by_cases hz : s = 0
    · simp [hz]
    · exact False.elim (hpq ((smul_right_injective _ hz) he))
  · rintro rfl
    exact ⟨left_mem_segment _ _ _, left_mem_segment _ _ _⟩

/-- A unit radius meets the unit circle only at its outer end. This keeps
spoke interiors away from the four boundary arcs in Part IV, Section 7c. -/
theorem unit_radius_inter_sphere {p : ℂ} (hp : ‖p‖ = 1) :
    segment ℝ 0 p ∩ sphere (0 : ℂ) 1 = {p} := by
  ext x
  constructor
  · rintro ⟨hx, hn⟩
    obtain ⟨t, ht, rfl⟩ := mem_radius hx
    have ht1 : t = 1 := by
      have hn := mem_sphere_zero_iff_norm.mp hn
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, hp, mul_one]
        using hn
    simp [ht1]
  · rintro rfl
    exact ⟨right_mem_segment _ _ _, mem_sphere_zero_iff_norm.mpr hp⟩

/-- Part IV, Section 7c: a disc chart supplies a common center and internally
disjoint spokes to any family of distinct boundary ports. Each spoke meets
the disc boundary only at its own port. -/
theorem exists_disc_spokes {ι : Type*} {D : Set ℂ} {h g : ℂ → ℂ}
    (chart : Surface.IsChart D h g) (port : ι → ℂ)
    (hport : ∀ i, port i ∈ Surface.discBd D) (hinj : Function.Injective port) :
    ∃ (z : ℂ) (spoke : ι → Set ℂ), z ∈ D \ Surface.discBd D ∧
      (∀ i, Surface.IsLineWithEnds (spoke i) z (port i) ∧
        spoke i ⊆ D ∧ spoke i ∩ Surface.discBd D = {port i}) ∧
      ∀ i j, i ≠ j → spoke i ∩ spoke j = {z} := by
  have hn : ∀ i, ‖h (port i)‖ = 1 := by
    intro i
    apply mem_sphere_zero_iff_norm.mp
    rw [← chart.bd]
    exact mem_image_of_mem h (hport i)
  have hs : ∀ i, segment ℝ 0 (h (port i)) ⊆ closedBall (0 : ℂ) 1 :=
    fun i => radius_subset (hn i)
  have hz : (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
  have he : ∀ i, g (h (port i)) = port i :=
    fun i => chart.gh (Surface.discBd_subset D (hport i))
  refine ⟨g 0, fun i => g '' segment ℝ 0 (h (port i)), ⟨chart.gm hz, ?_⟩,
    fun i => ⟨?_, chart.g_subset (hs i), ?_⟩, ?_⟩
  · intro hb
    have : h (g 0) ∈ sphere (0 : ℂ) 1 := by
      rw [← chart.bd]
      exact mem_image_of_mem h hb
    rw [chart.hg hz] at this
    simp at this
  · rw [← he i]
    apply Surface.IsLineWithEnds.image_injOn
      (Surface.isLineWithEnds_segment ?_) (chart.gc.mono (hs i))
      (chart.injOn.mono (hs i))
    intro heq
    have := hn i
    rw [← heq] at this
    simp at this
  · rw [← chart.g_sphere, ← chart.g_inter (hs i) sphere_subset_closedBall,
      unit_radius_inter_sphere (hn i)]
    simp only [image_singleton, he]
  · intro i j hij
    rw [← chart.g_inter (hs i) (hs j), unit_radii_inter (hn i) (hn j) ?_,
      image_singleton]
    intro heq
    apply hij
    apply hinj
    rw [← he i, ← he j, heq]

end GraphMinor.LRPlanarity
