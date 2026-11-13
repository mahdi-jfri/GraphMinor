module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import GraphMinor.GM06.Section5RadialCircleExtension
import GraphMinor.Surface.DiscTwist
import Mathlib.Tactic

/-!
# Extending the two cuff maps to the capping discs

The geometric orientation step of VI (5.11), page 134, is carried
from the cylinder to its sphere drawing. Its planar annulus has
radii one half and one. A norm-preserving homeomorphism of that
annulus restricts to a homeomorphism of each boundary circle.
Extend each circle map along straight rays. The resulting plane
homeomorphism agrees with the annular map on that cuff and keeps
all radii. These two extensions will fill the two caps without
using a formula for the chosen cylinder embedding.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The planar annulus used by the concrete cylinder embedding. -/
@[expose] def alg511Annulus : Set ℂ := {z | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1}

/-- A point of an annular circle, with its angular coordinate. -/
@[expose] noncomputable def alg511AnnulusPoint (r : ℝ) (hr : r ∈ Icc (1 / 2 : ℝ) 1)
    (w : Circle) : alg511Annulus :=
  ⟨(r : ℂ) * w, by
    change 1 / 2 ≤ ‖(r : ℂ) * w‖ ∧ ‖(r : ℂ) * w‖ ≤ 1
    simpa only [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one,
      Real.norm_of_nonneg (by linarith [hr.1] : 0 ≤ r)] using (And.intro hr.1 hr.2)⟩

/-- The complex coordinate of the circular point. -/
theorem alg511AnnulusPoint_val (r : ℝ) (hr : r ∈ Icc (1 / 2 : ℝ) 1) (w : Circle) :
    (alg511AnnulusPoint r hr w).val = (r : ℂ) * w := rfl

/-- The displayed annular point has precisely its stated radius. -/
theorem alg511AnnulusPoint_norm (r : ℝ) (hr : r ∈ Icc (1 / 2 : ℝ) 1) (w : Circle) :
    ‖(alg511AnnulusPoint r hr w).val‖ = r := by
  rw [alg511AnnulusPoint_val, norm_mul, Complex.norm_real, Circle.norm_coe, mul_one]
  exact Real.norm_of_nonneg (by linarith [hr.1])

private theorem continuous_annulusPoint (r : ℝ) (hr : r ∈ Icc (1 / 2 : ℝ) 1) :
    Continuous (alg511AnnulusPoint r hr) :=
  Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) (fun w => (alg511AnnulusPoint r hr w).property)

/-- A norm-preserving annular homeomorphism also has a
norm-preserving inverse. -/
theorem alg511Annulus_norm_symm (H : alg511Annulus ≃ₜ alg511Annulus)
    (hH : ∀ z, ‖(H z).val‖ = ‖z.val‖) (z : alg511Annulus) :
    ‖(H.symm z).val‖ = ‖z.val‖ := by
  have h := hH (H.symm z)
  rw [H.apply_symm_apply] at h
  exact h.symm

/-- Every circular level of a radius-preserving annular
homeomorphism has an actual angular homeomorphism. -/
theorem alg511_exists_annulus_circleMap (H : alg511Annulus ≃ₜ alg511Annulus)
    (hH : ∀ z, ‖(H z).val‖ = ‖z.val‖)
    (r : ℝ) (hr : r ∈ Icc (1 / 2 : ℝ) 1) :
    ∃ h : Circle ≃ₜ Circle, ∀ w : Circle,
      (H (alg511AnnulusPoint r hr w)).val = (r : ℂ) * h w := by
  have hrpos : 0 < r := by linarith [hr.1]
  have hnorm (w : Circle) : ‖(H (alg511AnnulusPoint r hr w)).val‖ = r :=
    (hH _).trans (alg511AnnulusPoint_norm r hr w)
  have hnorm' (w : Circle) : ‖(H.symm (alg511AnnulusPoint r hr w)).val‖ = r :=
    (alg511Annulus_norm_symm H hH _).trans (alg511AnnulusPoint_norm r hr w)
  have hne (w : Circle) : (H (alg511AnnulusPoint r hr w)).val ≠ 0 := by
    intro hz
    have h := hnorm w
    rw [hz, norm_zero] at h
    exact hrpos.ne' h.symm
  have hne' (w : Circle) : (H.symm (alg511AnnulusPoint r hr w)).val ≠ 0 := by
    intro hz
    have h := hnorm' w
    rw [hz, norm_zero] at h
    exact hrpos.ne' h.symm
  let f : Circle → Circle := fun w => unitOf (H (alg511AnnulusPoint r hr w)).val (hne w)
  let g : Circle → Circle := fun w => unitOf (H.symm (alg511AnnulusPoint r hr w)).val (hne' w)
  have hf (w : Circle) : alg511AnnulusPoint r hr (f w) = H (alg511AnnulusPoint r hr w) := by
    apply Subtype.ext
    change (r : ℂ) * unitOf _ (hne w) = _
    calc
      (r : ℂ) * (unitOf (H (alg511AnnulusPoint r hr w)).val (hne w) : ℂ) =
          (‖(H (alg511AnnulusPoint r hr w)).val‖ : ℂ) * (unitOf _ (hne w) : ℂ) := by rw [hnorm]
      _ = _ := norm_mul_unitOf _ _
  have hg (w : Circle) : alg511AnnulusPoint r hr (g w) = H.symm (alg511AnnulusPoint r hr w) := by
    apply Subtype.ext
    change (r : ℂ) * unitOf _ (hne' w) = _
    calc
      (r : ℂ) * (unitOf (H.symm (alg511AnnulusPoint r hr w)).val (hne' w) : ℂ) =
          (‖(H.symm (alg511AnnulusPoint r hr w)).val‖ : ℂ) * (unitOf _ (hne' w) : ℂ) := by rw [hnorm']
      _ = _ := norm_mul_unitOf _ _
  have hgf (w : Circle) : g (f w) = w := by
    apply Circle.ext
    change (unitOf (H.symm (alg511AnnulusPoint r hr (f w))).val _ : ℂ) = (w : ℂ)
    rw [coe_unitOf, hnorm']
    have hv : (H.symm (alg511AnnulusPoint r hr (f w))).val = (r : ℂ) * w := by
      rw [hf, H.symm_apply_apply, alg511AnnulusPoint_val]
    rw [hv, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hrpos.ne'), one_mul]
  have hfg (w : Circle) : f (g w) = w := by
    apply Circle.ext
    change (unitOf (H (alg511AnnulusPoint r hr (g w))).val _ : ℂ) = (w : ℂ)
    rw [coe_unitOf, hnorm]
    have hv : (H (alg511AnnulusPoint r hr (g w))).val = (r : ℂ) * w := by
      rw [hg, H.apply_symm_apply, alg511AnnulusPoint_val]
    rw [hv, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hrpos.ne'), one_mul]
  have hfc : Continuous f := continuous_unitOf.comp (Continuous.subtype_mk
    (continuous_subtype_val.comp (H.continuous.comp (continuous_annulusPoint r hr))) hne)
  have hgc : Continuous g := continuous_unitOf.comp (Continuous.subtype_mk
    (continuous_subtype_val.comp (H.symm.continuous.comp (continuous_annulusPoint r hr))) hne')
  let h : Circle ≃ₜ Circle := ⟨⟨f, g, hgf, hfg⟩, hfc, hgc⟩
  refine ⟨h, ?_⟩
  intro w
  change (H (alg511AnnulusPoint r hr w)).val = (r : ℂ) * f w
  exact (congrArg Subtype.val (hf w)).symm

/-- The angular map of an annular circle extends over the whole
plane with its radius fixed, and agrees with the original map on
that entire circular level. -/
theorem alg511_exists_annulus_cuff_extension (H : alg511Annulus ≃ₜ alg511Annulus)
    (hH : ∀ z, ‖(H z).val‖ = ‖z.val‖)
    (r : ℝ) (hr : r ∈ Icc (1 / 2 : ℝ) 1) :
    ∃ E : ℂ ≃ₜ ℂ, E 0 = 0 ∧ (∀ z, ‖E z‖ = ‖z‖) ∧
      ∀ z : alg511Annulus, ‖z.val‖ = r → E z.val = (H z).val := by
  obtain ⟨h, hh⟩ := alg511_exists_annulus_circleMap H hH r hr
  obtain ⟨E, hE0, hEn, hEr⟩ := exists_radial_circle_homeomorph h
  refine ⟨E, hE0, hEn, ?_⟩
  intro z hz
  have hrpos : 0 < r := by linarith [hr.1]
  have hzne : z.val ≠ 0 := by intro h; have hn := norm_eq_zero.mpr h; rw [hz] at hn; linarith
  let w := unitOf z.val hzne
  have hpoint : alg511AnnulusPoint r hr w = z := by
    apply Subtype.ext
    rw [alg511AnnulusPoint_val]
    change (r : ℂ) * unitOf z.val hzne = z.val
    rw [← hz]
    exact norm_mul_unitOf _ _
  have hval := congrArg Subtype.val hpoint
  have hE := hEr r hrpos.le w
  rw [← hh w, hpoint] at hE
  change E ((alg511AnnulusPoint r hr w).val) = _ at hE
  rw [hval] at hE
  exact hE

/-- The same extension carries the inverse boundary map, so the two
closed pieces can be pasted in both directions. -/
theorem alg511_annulus_cuff_extension_symm
    (H : alg511Annulus ≃ₜ alg511Annulus) (hH : ∀ z, ‖(H z).val‖ = ‖z.val‖)
    (r : ℝ) (E : ℂ ≃ₜ ℂ)
    (hE : ∀ z : alg511Annulus, ‖z.val‖ = r → E z.val = (H z).val)
    (z : alg511Annulus) (hz : ‖z.val‖ = r) : E.symm z.val = (H.symm z).val := by
  have hnorm : ‖(H.symm z).val‖ = r := (alg511Annulus_norm_symm H hH z).trans hz
  have heq := hE (H.symm z) hnorm
  rw [H.apply_symm_apply] at heq
  exact (E.eq_symm_apply.mpr heq).symm

end GraphMinor.GM06
