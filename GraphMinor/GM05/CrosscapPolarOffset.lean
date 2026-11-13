module

public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.Surface.Jordan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Coordinates for the local crosscap disc

For the reversing disc in GM V, (8.10), map the upper half of a small
disc to a sector outside the selected unit hole. Its radial coordinate
is one plus the absolute imaginary coordinate divided by eight, and
its angle is the real coordinate divided by eight. Reflection across
the diameter keeps this offset unchanged. On the unit disc the radius
lies between one and nine eighths, inside the exact half-turn region.
-/

public section

namespace GraphMinor.GM05

open Set Topology Metric Surface

/-- The small polar offset used on either side of the crosscap's unit
circle in the local reversing-disc construction. -/
noncomputable def crosscapPolarOffset (z : ℂ) : EuclideanPlane :=
  complexPlane (((1+|z.im|/8 : ℝ) : ℂ)*(Circle.exp (z.re/8) : ℂ))

/-- The formula for the polar offset in complex coordinates. -/
theorem crosscapPolarOffset_def (z : ℂ) :
    crosscapPolarOffset z=complexPlane (((1+|z.im|/8 : ℝ) : ℂ)*(Circle.exp (z.re/8) : ℂ)) := by rfl

/-- The offset varies continuously. -/
theorem continuous_crosscapPolarOffset : Continuous crosscapPolarOffset := by
  unfold crosscapPolarOffset
  fun_prop

/-- Its radius is one plus the absolute imaginary coordinate divided
by eight. -/
theorem norm_crosscapPolarOffset (z : ℂ) : ‖crosscapPolarOffset z‖=1+|z.im|/8 := by
  rw [crosscapPolarOffset_def,complexPlane.norm_map,norm_mul,Complex.norm_real,
    Circle.norm_coe,mul_one,Real.norm_eq_abs,abs_of_nonneg]
  positivity

/-- Reflection across the diameter preserves the polar offset. -/
theorem crosscapPolarOffset_conj (z : ℂ) : crosscapPolarOffset (starRingEnd ℂ z)=crosscapPolarOffset z := by
  simp only [crosscapPolarOffset_def,Complex.conj_im,Complex.conj_re,abs_neg]

/-- All offsets of points in the unit disc lie in the narrow annulus
on which the supported half turn is exactly negation. -/
theorem crosscapPolarOffset_bounds {z : ℂ} (hz : ‖z‖ ≤ 1) :
    1 ≤ ‖crosscapPolarOffset z‖ ∧ ‖crosscapPolarOffset z‖ ≤ 9/8 := by
  have him : |z.im| ≤ 1 := (Complex.abs_im_le_norm z).trans hz
  rw [norm_crosscapPolarOffset]
  constructor <;> linarith only [abs_nonneg z.im,him]

/-- The angular coordinate on the unit disc lies inside the interval
where sine is strictly increasing and cosine is positive. -/
theorem crosscap_polar_angle_bounds {z : ℂ} (hz : ‖z‖ ≤ 1) :
    -(Real.pi/2)<z.re/8 ∧ z.re/8<Real.pi/2 := by
  have hre : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hz
  have hlow := (abs_le.mp hre).1
  have hhigh := (abs_le.mp hre).2
  constructor <;> linarith only [hlow,hhigh,Real.pi_gt_three]

/-- The complex coordinate of each sector offset has positive real
part, so opposite sectors have no common base point. -/
theorem crosscapPolarOffset_re_pos {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0<(complexPlane.symm (crosscapPolarOffset z)).re := by
  rw [crosscapPolarOffset_def,complexPlane.symm_apply_apply]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Circle.coe_exp,Complex.exp_ofReal_mul_I_re]
  exact mul_pos (by positivity) (Real.cos_pos_of_mem_Ioo (crosscap_polar_angle_bounds hz))

/-- The polar offset determines the real coordinate and the absolute
imaginary coordinate on the unit disc. -/
theorem crosscapPolarOffset_eq_iff {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    crosscapPolarOffset z=crosscapPolarOffset w ↔ z.re=w.re ∧ |z.im|=|w.im| := by
  constructor
  · intro he
    have hn := congrArg norm he
    rw [norm_crosscapPolarOffset,norm_crosscapPolarOffset] at hn
    have habs : |z.im|=|w.im| := by linarith only [hn]
    have hC := congrArg complexPlane.symm he
    rw [crosscapPolarOffset_def,crosscapPolarOffset_def,
      complexPlane.symm_apply_apply,complexPlane.symm_apply_apply,habs] at hC
    have hr : ((1+|w.im|/8 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ)<1+|w.im|/8))
    have hd := mul_left_cancel₀ hr hC
    have hs := congrArg Complex.im hd
    simp only [Circle.coe_exp,Complex.exp_ofReal_mul_I_im] at hs
    have hzangle := crosscap_polar_angle_bounds hz
    have hwangle := crosscap_polar_angle_bounds hw
    have heangle := Real.injOn_sin ⟨hzangle.1.le,hzangle.2.le⟩ ⟨hwangle.1.le,hwangle.2.le⟩ hs
    exact ⟨by linarith only [heangle],habs⟩
  · rintro ⟨hre,him⟩
    rw [crosscapPolarOffset_def,crosscapPolarOffset_def,hre,him]

/-- The two sectors on opposite sides of the crosscap's circle have
no common point in the model base. -/
theorem crosscapPolarOffset_ne_neg {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    crosscapPolarOffset z ≠ -crosscapPolarOffset w := by
  intro he
  have hpz := crosscapPolarOffset_re_pos hz
  have hpw := crosscapPolarOffset_re_pos hw
  have h := congrArg (fun u : EuclideanPlane ↦ (complexPlane.symm u).re) he
  simp only [map_neg,Complex.neg_re] at h
  linarith only [hpz,hpw,h]

end GraphMinor.GM05
