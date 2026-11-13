module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.DiscMerge
import Mathlib.Topology.Algebra.GroupWithZero
import GraphMinor.GM08.Section6CoverUnit

/-!
# Removing the unit-ball bound from the plane covering theorem

For VIII (6.2), page 264, both curves are compact. A linear rescaling puts
them in the unit ball, where the excursion construction applies. Pulling
back the resulting closed disc preserves enclosure and the requirement
that its boundary lie in the original two curves.
-/

public section

namespace GraphMinor.GM08

open Set Topology Metric Surface

private theorem exists_shrinking_homeomorph {K : Set ℂ} (hK : IsCompact K) :
    ∃ H : ℂ ≃ₜ ℂ, H '' K ⊆ closedBall 0 1 := by
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_ball_lt 0 (0 : ℂ)
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let H := Homeomorph.mulLeft₀ ((r : ℂ)⁻¹) (inv_ne_zero hrC)
  refine ⟨H, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_closedBall_zero_iff]
  change ‖(r : ℂ)⁻¹ * x‖ ≤ 1
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    ← div_eq_inv_mul]
  exact (div_le_one hr).mpr (mem_ball_zero_iff.mp (hKr hx)).le

/-- The unrestricted plane covering theorem used for VIII (6.2). A closed
disc and a curve meeting its boundary in at least two points are contained
in a closed disc whose boundary uses only the two original curves. -/
theorem exists_plane_disc_cover {D F : Set ℂ} (hD : IsClosedDisc D)
    (hF : IsOArc F) (hinter : (discBd D ∩ F).Nontrivial) :
    ∃ E : Set ℂ, IsClosedDisc E ∧ D ⊆ E ∧ F ⊆ E ∧ discBd E ⊆ discBd D ∪ F := by
  obtain ⟨H, hHu⟩ := exists_shrinking_homeomorph (hD.isCompact.union hF.isCompact)
  obtain ⟨hDH, hDHb⟩ := hD.image H.continuous.continuousOn H.symm.continuous.continuousOn
    (fun x _ => H.symm_apply_apply x)
  have hFH : IsOArc (H '' F) := hF.image H.continuous.continuousOn
    H.symm.continuous.continuousOn (fun x _ => H.symm_apply_apply x)
  have hinterH : (discBd (H '' D) ∩ H '' F).Nontrivial := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hinter
    refine ⟨H x, ⟨?_, ⟨x, hx.2, rfl⟩⟩, H y, ⟨?_, ⟨y, hy.2, rfl⟩⟩,
      fun he => hxy (H.injective he)⟩
    · rw [hDHb]
      exact ⟨x, hx.1, rfl⟩
    · rw [hDHb]
      exact ⟨y, hy.1, rfl⟩
  obtain ⟨E, hE, hDE, hFE, hEb, _⟩ := exists_plane_disc_cover_unit hDH hFH hinterH
    ((image_mono subset_union_left).trans hHu) ((image_mono subset_union_right).trans hHu)
  obtain ⟨hEH, hEHb⟩ := hE.image H.symm.continuous.continuousOn H.continuous.continuousOn
    (fun x _ => H.apply_symm_apply x)
  refine ⟨H.symm '' E, hEH, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨H x, hDE ⟨x, hx, rfl⟩, H.symm_apply_apply x⟩
  · intro x hx
    exact ⟨H x, hFE ⟨x, hx, rfl⟩, H.symm_apply_apply x⟩
  · rw [hEHb]
    have htarget : H.symm '' (discBd (H '' D) ∪ H '' F) = discBd D ∪ F := by
      rw [hDHb, image_union, image_image, image_image]
      simp only [Homeomorph.symm_apply_apply, image_id']
    exact htarget ▸ image_mono hEb

end GraphMinor.GM08
