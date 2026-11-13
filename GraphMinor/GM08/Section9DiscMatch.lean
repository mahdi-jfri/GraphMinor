module

public import GraphMinor.Surface.DiscArcs
public import GraphMinor.Surface.CircleMove
import GraphMinor.GM08.Section9CircleMatch
import GraphMinor.Surface.DiscTwist

/-!
# Extending the boundary-root matching across the disc

The circle matching in VIII (9.3) preserves orientation. Extend it to
the complex plane while preserving the norm, then use disc coordinates
to obtain a homeomorphism of the original disc.
-/

public section

namespace GraphMinor.GM08

open Set Surface Metric

universe u

/-- Extend the circle map used for the boundary marks in VIII (9.3),
page 270, to the ambient disc. The extension agrees in disc coordinates. -/
theorem exists_disc_homeomorph_of_circle_match {S : Type u} [TopologicalSpace S]
    {h : S → ℂ} {g : ℂ → S} (c : IsChart univ h g)
    (σ : Circle ≃ₜ Circle) (hσ : PreservesCircleOrientation σ) :
    ∃ α : S ≃ₜ S, ∀ w : Circle, α (g w) = g (σ w) := by
  obtain ⟨Θ, -, hnorm, hcircle⟩ := exists_twist hσ
  have hΘ : MapsTo Θ (closedBall (0 : ℂ) 1) (closedBall 0 1) := by
    intro z hz
    simpa only [mem_closedBall_zero_iff, hnorm] using hz
  have hΘi : MapsTo Θ.symm (closedBall (0 : ℂ) 1) (closedBall 0 1) := by
    intro z hz
    have hn : ‖Θ.symm z‖ = ‖z‖ := by rw [← hnorm (Θ.symm z), Θ.apply_symm_apply]
    simpa only [mem_closedBall_zero_iff, hn] using hz
  let α : S ≃ₜ S := {
    toFun := fun x => g (Θ (h x))
    invFun := fun x => g (Θ.symm (h x))
    left_inv := fun x => by
      dsimp only
      rw [c.hg (hΘ (c.hm (mem_univ x))), Θ.symm_apply_apply, c.gh (mem_univ x)]
    right_inv := fun x => by
      dsimp only
      rw [c.hg (hΘi (c.hm (mem_univ x))), Θ.apply_symm_apply, c.gh (mem_univ x)]
    continuous_toFun := c.gc.comp_continuous
      (Θ.continuous.comp (continuousOn_univ.mp c.hc)) (fun x => hΘ (c.hm (mem_univ x)))
    continuous_invFun := c.gc.comp_continuous
      (Θ.symm.continuous.comp (continuousOn_univ.mp c.hc)) (fun x => hΘi (c.hm (mem_univ x))) }
  refine ⟨α, fun w => ?_⟩
  change g (Θ (h (g w))) = g (σ w)
  rw [c.hg (sphere_subset_closedBall w.2), hcircle]

/-- Boundary marks of equal size in a closed disc can be matched by a
homeomorphism of the disc. This aligns the two graft drawings in the
proof of VIII (9.3), page 270. -/
theorem exists_disc_boundary_match {S : Type u} [TopologicalSpace S]
    (hΔ : IsClosedDisc (univ : Set S)) {Z W : Set S}
    (hZ : Z.Finite) (hW : W.Finite)
    (hZbd : Z ⊆ discBd (univ : Set S)) (hWbd : W ⊆ discBd (univ : Set S))
    (hcard : Z.ncard = W.ncard) : ∃ α : S ≃ₜ S, α '' Z = W := by
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  let p : Circle → S := fun w => g w
  have hpi : Function.Injective p := by
    intro x y heq
    apply Subtype.ext
    exact c.injOn (sphere_subset_closedBall x.2) (sphere_subset_closedBall y.2) heq
  have hpr : range p = discBd (univ : Set S) := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      rw [← c.g_sphere]
      exact mem_image_of_mem g w.2
    · intro hx
      rw [← c.g_sphere] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      exact ⟨⟨z, hz⟩, rfl⟩
  have hZr : Z ⊆ range p := hpr.symm ▸ hZbd
  have hWr : W ⊆ range p := hpr.symm ▸ hWbd
  obtain ⟨σ, hσo, hσ⟩ := exists_circle_match
    (Set.Finite.preimage hpi.injOn hZ) (Set.Finite.preimage hpi.injOn hW)
    (by rw [ncard_preimage_of_injective_subset_range hpi hZr,
      ncard_preimage_of_injective_subset_range hpi hWr]; exact hcard)
  obtain ⟨α, hα⟩ := exists_disc_homeomorph_of_circle_match c σ hσo
  refine ⟨α, ?_⟩
  have heq : α '' (p '' (p ⁻¹' Z)) = p '' (σ '' (p ⁻¹' Z)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨σ w, mem_image_of_mem σ hw, (hα w).symm⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨p w, mem_image_of_mem p hw, hα w⟩
  rw [image_preimage_eq_iff.mpr hZr] at heq
  rw [heq, hσ, image_preimage_eq_iff.mpr hWr]

end GraphMinor.GM08
