module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Algebra.Module.Torsion.Free

/-!
# Radial segments in a vertex disc

Part IV, Section 7a of the planarity note replaces each endpoint tail by a
radius of its vertex disc. Distinct ports on one circle give radii meeting
only at the center. A radius meets that circle only at its port. These two
facts keep radial tails separate from the other middle arcs and radial tails.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Metric

/-- Part IV, Section 7a: a radius meets its boundary circle only at its port. -/
theorem radial_segment_inter_sphere {z p : ℂ} {r : ℝ} (hr : 0 < r)
    (hp : p ∈ sphere z r) : segment ℝ z p ∩ sphere z r = {p} := by
  have hnorm : ‖p - z‖ = r := by rw [← dist_eq_norm]; exact mem_sphere.mp hp
  ext x
  constructor
  · rintro ⟨hx, hxs⟩
    rw [segment_eq_image_lineMap] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have he : t * r = r := by
      have he := mem_sphere.mp hxs
      simpa only [dist_eq_norm, AffineMap.lineMap_apply_module', add_sub_cancel_right,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, hnorm] using he
    have ht1 : t = 1 := mul_right_cancel₀ hr.ne' (he.trans (one_mul r).symm)
    simp only [ht1, AffineMap.lineMap_apply_one, mem_singleton_iff]
  · rintro rfl
    exact ⟨right_mem_segment _ _ _, hp⟩

/-- Part IV, Section 7a: radii to two distinct ports of the same vertex disc
meet only at their common vertex. -/
theorem radial_segments_inter {z p q : ℂ} {r : ℝ} (hr : 0 < r)
    (hp : p ∈ sphere z r) (hq : q ∈ sphere z r) (hpq : p ≠ q) :
    segment ℝ z p ∩ segment ℝ z q = {z} := by
  have hnp : ‖p - z‖ = r := by rw [← dist_eq_norm]; exact mem_sphere.mp hp
  have hnq : ‖q - z‖ = r := by rw [← dist_eq_norm]; exact mem_sphere.mp hq
  ext x
  constructor
  · rintro ⟨hx, hy⟩
    rw [segment_eq_image_lineMap] at hx hy
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, he⟩ := hy
    have he' : s • (p - z) = t • (q - z) := by
      simp only [AffineMap.lineMap_apply_module'] at he
      exact add_right_cancel he.symm
    have hst : s = t := by
      apply mul_right_cancel₀ hr.ne'
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1,
        abs_of_nonneg ht.1, hnp, hnq] using congrArg norm he'
    rw [← hst] at he'
    by_cases hs0 : s = 0
    · simp only [hs0, AffineMap.lineMap_apply_zero, mem_singleton_iff]
    · have heq : p - z = q - z := (smul_right_injective ℂ hs0) he'
      have hh := congrArg (fun w : ℂ => w + z) heq
      have hpqe : p = q := by simpa only [sub_add_cancel] using hh
      exact (hpq hpqe).elim
  · rintro rfl
    exact ⟨left_mem_segment _ _ _, left_mem_segment _ _ _⟩

/-- Part IV, Section 7a: every radial tail lies in its closed vertex disc. -/
theorem radial_segment_subset_disc {z p : ℂ} {r : ℝ} (hr : 0 < r)
    (hp : p ∈ sphere z r) : segment ℝ z p ⊆ closedBall z r :=
  (convex_closedBall z r).segment_subset (mem_closedBall_self hr.le)
    (sphere_subset_closedBall hp)

/-- Part IV, Section 7a: a middle arc meeting a vertex disc only at its
own boundary port misses the radius to any other middle arc's port. -/
theorem disjoint_middle_radial_segment {M : Set ℂ} {z p q : ℂ} {r : ℝ}
    (hr : 0 < r) (hp : p ∈ sphere z r) (hq : q ∈ sphere z r)
    (hM : M ∩ closedBall z r = {p}) (hqM : q ∉ M) :
    Disjoint M (segment ℝ z q) := by
  apply disjoint_left.mpr
  intro x hxM hxR
  have hxp : x = p := mem_singleton_iff.mp (hM ▸
    ⟨hxM, radial_segment_subset_disc hr hq hxR⟩)
  have hxs : x ∈ sphere z r := hxp ▸ hp
  have hxq : x = q := mem_singleton_iff.mp (radial_segment_inter_sphere hr hq ▸ ⟨hxR, hxs⟩)
  exact hqM (hxq ▸ hxM)

end GraphMinor.LRPlanarity
