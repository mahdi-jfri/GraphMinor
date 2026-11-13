module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.DiscTwist
import GraphMinor.Surface.MoveCuff

/-!
# A half turn with an exact inner action

For the crosscap obstruction in GM V, (8.10), the half turn must equal
negation on a neighbourhood of the unit hole. Delay the library's
circle homotopy until radius five quarters, then finish it by radius
three halves. The radial map preserves the norm, so the bijections on
circles make it a proper continuous bijection of the plane.
-/

public section

namespace GraphMinor.GM05

open Set Topology Metric Filter Surface

open scoped unitInterval

/-- A half turn on the radius-five-quarters disc, undone before radius
three halves. The exact inner formula permits a local reflection chart
at the identified boundary of a crosscap. -/
theorem exists_complex_half_turn_core :
    ∃ Θ : ℂ ≃ₜ ℂ,(∀ z,3/2 ≤ ‖z‖ → Θ z=z) ∧ (∀ z,‖Θ z‖=‖z‖) ∧
      ∀ z,‖z‖ ≤ 5/4 → Θ z= -z := by
  obtain ⟨μ₀,hμ₀c,hμ₀0,hμ₀1,hμ₀b⟩ := exists_circle_homotopy (preservesCircleOrientation_mul (-1))
  let κ : unitInterval → unitInterval := fun t ↦ projIcc 0 1 zero_le_one (2*(t : ℝ)-1)
  have hκc : Continuous κ := continuous_projIcc.comp (by fun_prop)
  have hκlow (t : unitInterval) (ht : (t : ℝ) ≤ 1/2) : κ t=0 :=
    projIcc_of_le_left zero_le_one (by linarith only [ht])
  have hκone : κ 1=1 := projIcc_of_right_le zero_le_one (by norm_num)
  let μ : unitInterval × Circle → Circle := fun x ↦ μ₀ (κ x.1,x.2)
  have hμc : Continuous μ := hμ₀c.comp ((hκc.comp continuous_fst).prodMk continuous_snd)
  have hμ1 (w : Circle) : μ (1,w)=w := by
    change μ₀ (κ 1,w)=w
    rw [hκone,hμ₀1]
  have hμb (t : unitInterval) : Function.Bijective (fun w ↦ μ (t,w)) := hμ₀b (κ t)
  have hμlow (t : unitInterval) (ht : (t : ℝ) ≤ 1/2) (w : Circle) : μ (t,w)= -w := by
    change μ₀ (κ t,w)= -w
    rw [hκlow t ht,hμ₀0,Homeomorph.coe_mulLeft]
    exact neg_one_mul w
  have hc := continuous_twistMap hμc
  have hinj : Function.Injective (twistMap μ) := by
    intro z w he
    have hn : ‖z‖ = ‖w‖ := by rw [← norm_twistMap μ z, he, norm_twistMap]
    by_cases hz : z = 0
    · subst hz
      exact (norm_eq_zero.mp (by simpa using hn.symm)).symm
    · have hw : w ≠ 0 := fun h => hz (norm_eq_zero.mp (by simpa [h] using hn))
      simp only [twistMap, dite_eq_right hz, dite_eq_right hw] at he
      rw [← hn] at he
      have hr : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
      have h1 := Circle.ext (mul_left_cancel₀ hr he)
      have h2 := (hμb _).1 h1
      rw [← norm_mul_unitOf z hz, ← norm_mul_unitOf w hw, ← hn, h2]
  have hsurj : Function.Surjective (twistMap μ) := by
    intro w
    by_cases hw : w = 0
    · exact ⟨0, by simp [twistMap, hw]⟩
    · obtain ⟨v, hv⟩ := (hμb (twistParam ‖w‖)).2 (unitOf w hw)
      have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
      have hne : ((‖w‖ : ℝ) : ℂ) * v ≠ 0 := mul_ne_zero (by exact_mod_cast hpos.ne') (Circle.coe_ne_zero v)
      refine ⟨((‖w‖ : ℝ) : ℂ) * v, ?_⟩
      have hnorm : ‖((‖w‖ : ℝ) : ℂ) * v‖ = ‖w‖ := by
        rw [norm_mul, Complex.norm_real, Circle.norm_coe, mul_one, norm_norm]
      simp only [twistMap, dite_eq_right hne]
      rw [unitOf_mul _ hpos v hne, hnorm]
      have hv' : μ (twistParam ‖w‖, v) = unitOf w hw := hv
      rw [hv', norm_mul_unitOf]
  have hproper : IsProperMap (twistMap μ) := by
    refine isProperMap_iff_tendsto_cocompact.mpr ⟨hc, ?_⟩
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    simp only [norm_twistMap]
    exact tendsto_norm_cobounded_atTop
  let Θ : ℂ ≃ₜ ℂ := (Equiv.ofBijective _ ⟨hinj, hsurj⟩).toHomeomorphOfContinuousClosed hc hproper.isClosedMap
  have hΘ : ∀ z, Θ z = twistMap μ z := fun _ => rfl
  refine ⟨Θ,?_,fun z ↦ norm_twistMap μ z,?_⟩
  · intro z hz
    have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz; linarith
    rw [hΘ]
    simp only [twistMap,dite_eq_right hz0]
    rw [twistParam_high hz,hμ1,norm_mul_unitOf]
  · intro z hz
    by_cases hz0 : z=0
    · subst z
      simp [hΘ,twistMap]
    have hparam : (twistParam ‖z‖ : ℝ) ≤ 1/2 := by
      change max 0 (min 1 (2*‖z‖-2)) ≤ 1/2
      apply max_le
      · norm_num
      · exact (min_le_right _ _).trans (by linarith only [hz])
    rw [hΘ]
    simp only [twistMap,dite_eq_right hz0]
    rw [hμlow _ hparam,Circle.coe_neg,mul_neg,norm_mul_unitOf]

end GraphMinor.GM05
