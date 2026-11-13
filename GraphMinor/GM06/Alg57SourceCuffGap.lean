module

public import GraphMinor.GM06.Alg57RetainedSourceRays
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Locating a cuff contact outside the surviving target rays

In Lemma 8 of the implementation of VI (5.7), page 133, the old
target disc misses the cuffs. Its collapsed image therefore has no
cuff point other than the source. A small source-rim cuff contact
lies outside that disc. The explicit tangent-disc coordinates force
its direction into the complementary gap of the surviving target
rays. The comparison below proves this directly from the actual
pointwise collapse equation and the coordinate radius bound.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

private theorem min_sin_le_sin_between {a t b : ℝ}
    (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ Real.pi) :
    min (Real.sin a) (Real.sin b) ≤ Real.sin t := by
  by_cases ht : t ≤ Real.pi / 2
  · exact (min_le_left _ _).trans (Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) ht hat)
  · have hh : Real.sin (Real.pi - b) ≤ Real.sin (Real.pi - t) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith only [ht]) (by linarith only [htb])
    rw [Real.sin_pi_sub, Real.sin_pi_sub] at hh
    exact (min_le_right _ _).trans hh

/-- The portion of a half-angle ray below its sine bound belongs
to the explicit collapsed parameter disc. -/
theorem exists_collapsed_radius_point_on_ray
    {z : ℂ} {u : Circle} (hz : z = (‖z‖ : ℂ) * u)
    {α : ℝ} (hα0 : 0 < α) (hαπ : α < Real.pi)
    (hu : u = Circle.exp α) (hzsin : ‖z‖ ≤ Real.sin α) :
    ∃ x : ClosedUnitDisc, section5CollapsedRadiusDiscPoint x = discPt z := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
  let r : I := ⟨‖z‖ / Real.sin α, div_nonneg (norm_nonneg _) hs.le,
    (div_le_one hs).mpr hzsin⟩
  refine ⟨polarDiscPoint r (Circle.exp (2 * α)), ?_⟩
  have hhalf : 2 * α / 2 = α := by ring
  have h0 : 0 < 2 * α := by linarith only [hα0]
  have hP : 2 * α < 2 * Real.pi := by linarith only [hαπ]
  rw [section5CollapsedRadiusDiscPoint_ray r _ h0 hP]
  have hrval : (r : ℝ) * Real.sin (2 * α / 2) = ‖z‖ := by
    rw [hhalf]
    exact div_mul_cancel₀ _ hs.ne'
  have hnorm : ‖z‖ ≤ 1 := hzsin.trans (Real.sin_le_one _)
  let t : I := ⟨‖z‖, norm_nonneg _, hnorm⟩
  have hpoint : polarDiscPoint
      ⟨(r : ℝ) * Real.sin (2 * α / 2),
        mul_nonneg r.property.1 (section5RadiusCollapse_half_angle_bounds h0 hP).2.2.le,
        (mul_le_mul_of_nonneg_left (Real.sin_le_one _) r.property.1).trans
          (by simpa only [mul_one] using r.property.2)⟩ (Circle.exp (2 * α / 2)) =
      polarDiscPoint t u := by
    apply Subtype.ext
    change planeOf (((((r : ℝ) * Real.sin (2 * α / 2)) : ℝ) : ℂ) *
      Circle.exp (2 * α / 2)) = planeOf ((‖z‖ : ℂ) * u)
    rw [hrval, hhalf, ← hu]
  rw [hpoint, ← discPt_mul]
  exact congrArg discPt hz.symm

/-- Any point outside the actual collapsed target disc has its
coordinate direction outside every interval of retained half-angle
rays for which its radius is below both endpoint sine bounds. -/
theorem source_off_target_disc_direction_order
    {π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane)}
    {Φ Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (w : Circle)
    (hmap : ∀ x, Ψ (section5CollapsedRadiusDiscPoint x) =
      π (Φ (section5RotateDisc w x)))
    {z : ℂ} {u : Circle} (hz : z = (‖z‖ : ℂ) * u)
    (hoff : Ψ (discPt z) ∉ range (fun x => π (Φ x)))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < Real.pi)
    (hza : ‖z‖ ≤ Real.sin a) (hzb : ‖z‖ ≤ Real.sin b) :
    CircleCyclic u (Circle.exp a) (Circle.exp b) := by
  have hout {α : ℝ} (hα : α ∈ Icc a b) : u ≠ Circle.exp α := by
    intro hu
    have hs : ‖z‖ ≤ Real.sin α := (le_min hza hzb).trans
      (min_sin_le_sin_between ha.le hα.1 hα.2 hb.le)
    obtain ⟨x, hx⟩ := exists_collapsed_radius_point_on_ray hz
      (ha.trans_le hα.1) (hα.2.trans_lt hb) hu hs
    apply hoff
    exact ⟨section5RotateDisc w x, (hmap x).symm.trans (congrArg Ψ hx)⟩
  have hua : u ≠ Circle.exp a := hout ⟨le_rfl, hab.le⟩
  obtain ⟨s, hs0, hsP, hs⟩ := exists_angle (z := (Circle.exp a)⁻¹ * u)
    (fun heq => hua (inv_mul_eq_one.mp heq).symm)
  have hu : u = Circle.exp (a + s) := by
    rw [Circle.exp_add, ← hs]
    simp only [mul_inv_cancel_left]
  have hbs : b < a + s := by
    by_contra hh
    exact hout ⟨by linarith only [hs0], le_of_not_gt hh⟩ hu
  have hcyc := circleCyclic_exp_of_lt
    (show a + s < a + 2 * Real.pi by linarith only [hsP])
    (show a + 2 * Real.pi < b + 2 * Real.pi by linarith only [hab])
    (show b + 2 * Real.pi < (a + s) + 2 * Real.pi by linarith only [hbs])
  simpa only [Circle.exp_add_two_pi, ← hu] using hcyc


/-- A chart disjoint from a fixed cuff stays disjoint from that
cuff away from the collapsed source. The unique nontrivial fibre
and injectivity off it prove the assertion pointwise. -/
theorem collapsed_target_chart_avoids_fixed_cuff
    {S : Type*} {π : S → S} {p : S} {A C : Set S}
    (hfibre : π ⁻¹' {p} = A) (hinj : InjOn π Aᶜ)
    (hfix : ∀ x ∈ C, π x = x) {D : Type*} (Φ : D → S)
    (hoff : Disjoint (range Φ) C) {y : S} (hy : y ∈ C) (hyp : y ≠ p) :
    y ∉ range (fun x => π (Φ x)) := by
  have hyA : y ∉ A := by
    intro hh
    have hh' : π y = p := mem_singleton_iff.mp (mem_preimage.mp (hfibre.symm ▸ hh))
    exact hyp ((hfix y hy).symm.trans hh')
  rintro ⟨x, hxy⟩
  have hxA : Φ x ∉ A := by
    intro hh
    have hh' : π (Φ x) = p := mem_singleton_iff.mp (mem_preimage.mp (hfibre.symm ▸ hh))
    exact hyp (hxy.symm.trans hh')
  have hxy' : Φ x = y := hinj hxA hyA (hxy.trans (hfix y hy).symm)
  exact disjoint_left.mp hoff (mem_range_self x) (hxy'.symm ▸ hy)

/-- Two retained ray contacts are in half-angle order starting
from any smaller-rim contact outside the target disc. The anchor
contact need not have a unique coordinate direction. -/
theorem source_anchor_precedes_retained_pair
    {π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane)}
    {Φ Ψ Φ' : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (w : Circle)
    (hquot : ∀ x, Ψ (section5CollapsedRadiusDiscPoint x) =
      π (Φ (section5RotateDisc w x)))
    (f : C(Circle, ℂ)) (v : C(Circle, Circle))
    (hmap : ∀ x, Ψ (discPt (f x)) = Φ' (polarDiscPoint 1 x))
    (hv : ∀ x, f x = (‖f x‖ : ℂ) * v x)
    (hvpos : 0 < wind (fun x => (v x : ℂ)) 0)
    {a b c : Circle} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (hβ : β < Real.pi)
    (ha : v a = Circle.exp α) (hb : v b = Circle.exp β)
    (hca : ∀ x, v x = v a → x = a) (hcb : ∀ x, v x = v b → x = b)
    (hoff : Φ' (polarDiscPoint 1 c) ∉ range (fun x => π (Φ x)))
    (hfa : ‖f c‖ ≤ Real.sin α) (hfb : ‖f c‖ ≤ Real.sin β) :
    CircleCyclic c a b := by
  have hmodel := source_off_target_disc_direction_order w hquot (hv c)
    (by rw [hmap]; exact hoff) hα hαβ hβ hfa hfb
  apply (circleCyclic_iff_positive_loop_anchor v hvpos hca hcb hab hac hbc).mpr
  simpa only [ha, hb] using hmodel

end GraphMinor.GM06
