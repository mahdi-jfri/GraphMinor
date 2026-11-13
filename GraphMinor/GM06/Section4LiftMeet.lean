module

public import GraphMinor.GM06.Section4Winding
import GraphMinor.GM06.Section4Strip

/-!
# Two forced meetings of lifted forest paths

In the proof of Graph Minors VI (4.2), claim (1), a path with both ends on
a cuff arc cannot turn once more around the cylinder than that arc. Such a
turn forces meetings with two translates of the other path. The angular
offsets at those meetings differ, which a forest excludes.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface Real

/-- Lift a cylinder curve to the strip using a chosen angular lift.
The Boolean reflects the radius when the chosen cuff is the outer cuff. -/
@[expose] noncomputable def cylinderLiftedCurve (f : Curve ClosedCylinder)
    (a : C(unitInterval, ℝ)) (outer : Bool) : C(unitInterval, ℝ × ℝ) :=
  ⟨fun t => (if outer then 3 - (f t).1.1 else (f t).1.1, a t), by
    cases outer <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop⟩

/-- A lifted curve remains between the two sides of the strip. -/
theorem cylinderLiftedCurve_radius_mem (f : Curve ClosedCylinder)
    (a : C(unitInterval, ℝ)) (outer : Bool) (t : unitInterval) :
    (cylinderLiftedCurve f a outer t).1 ∈ Icc (1 : ℝ) 2 := by
  cases outer
  · exact (f t).2.1
  · change 3 - (f t).1.1 ∈ Icc (1 : ℝ) 2
    constructor <;> linarith only [(f t).2.1.1, (f t).2.1.2]

/-- The selected cuff is carried to the left side of the strip. -/
theorem cylinderLiftedCurve_boundary (f : Curve ClosedCylinder)
    (a : C(unitInterval, ℝ)) (outer : Bool) (t : unitInterval)
    (ht : (f t).1.1 = (if outer then 2 else 1)) :
    (cylinderLiftedCurve f a outer t).1 = 1 := by
  cases outer <;> simp_all [cylinderLiftedCurve]
  norm_num

/-- A meeting of angular lifts projects to a meeting of cylinder curves. -/
theorem eq_of_cylinderLiftedCurve_eq {f g : Curve ClosedCylinder}
    {a b : C(unitInterval, ℝ)} {outer : Bool}
    (ha : ∀ t, Circle.exp (a t) = (f t).1.2)
    (hb : ∀ t, Circle.exp (b t) = (g t).1.2)
    {s t : unitInterval} (h : cylinderLiftedCurve f a outer s = cylinderLiftedCurve g b outer t) :
    f s = g t := by
  apply Subtype.ext
  apply Prod.ext
  · have hr := congrArg (fun p : ℝ × ℝ => p.1) h
    cases outer
    · exact hr
    · change 3 - (f s).1.1 = 3 - (g t).1.1 at hr
      linarith only [hr]
  · rw [← ha, ← hb]
    exact congrArg Circle.exp (congrArg (fun p : ℝ × ℝ => p.2) h)

/-- An extra positive turn forces two meetings with distinct angular
offsets, contrary to the absence of circuits in the forest. The ends of
the second path are allowed to equal either end of the first path. -/
theorem not_positive_turn_of_forest
    {H : Drawing ClosedCylinder} (hH : IsGraphForest H.toGraph)
    (outer : Bool) {f g : Curve ClosedCylinder} (hf : range f ⊆ H.U) (hg : range g ⊆ H.U)
    (a b : C(unitInterval, ℝ))
    (ha : ∀ t, Circle.exp (a t) = (f t).1.2)
    (hb : ∀ t, Circle.exp (b t) = (g t).1.2)
    (hf0 : (f 0).1.1 = (if outer then 2 else 1)) (hf1 : (f 1).1.1 = (if outer then 2 else 1))
    (hg0 : (g 0).1.1 = (if outer then 2 else 1)) (hg1 : (g 1).1.1 = (if outer then 2 else 1))
    {d l : ℝ} (hl : 0 < l) (hel : Circle.exp l = 1)
    (hwidth : a 1 - a 0 < l)
    (hstart : b 0 ∈ Icc (a 0) (a 1))
    (hend : d ∈ Icc (a 0) (a 1)) (hb1 : b 1 = d + l) : False := by
  let F := cylinderLiftedCurve f a outer
  let G := cylinderLiftedCurve g b outer
  let a' : C(unitInterval, ℝ) := a + ContinuousMap.const _ l
  let F' := cylinderLiftedCurve f a' outer
  have hFr : ∀ t : unitInterval, (F t).1 ∈ Icc (1 : ℝ) 2 :=
    cylinderLiftedCurve_radius_mem f a outer
  have hGr : ∀ t : unitInterval, (G t).1 ∈ Icc (1 : ℝ) 2 :=
    cylinderLiftedCurve_radius_mem g b outer
  have hF'r : ∀ t : unitInterval, (F' t).1 ∈ Icc (1 : ℝ) 2 :=
    cylinderLiftedCurve_radius_mem f a' outer
  have hmeet₀ := strip_crossing_same_side_le F G hFr hGr
    (cylinderLiftedCurve_boundary f a outer 0 hf0) (cylinderLiftedCurve_boundary f a outer 1 hf1)
    (cylinderLiftedCurve_boundary g b outer 0 hg0) (cylinderLiftedCurve_boundary g b outer 1 hg1)
    ⟨hstart.1, hstart.2, by change a 1 ≤ b 1; linarith only [hend.1, hb1, hwidth]⟩
  have hmeet₁ := strip_crossing_same_side_le G F' hGr hF'r
    (cylinderLiftedCurve_boundary g b outer 0 hg0) (cylinderLiftedCurve_boundary g b outer 1 hg1)
    (cylinderLiftedCurve_boundary f a' outer 0 hf0) (cylinderLiftedCurve_boundary f a' outer 1 hf1)
    (show b 0 ≤ a 0 + l ∧ a 0 + l ≤ b 1 ∧ b 1 ≤ a 1 + l from
      ⟨by linarith only [hstart.2, hwidth],
        by linarith only [hend.1, hb1], by linarith only [hend.2, hb1]⟩)
  obtain ⟨s₀, t₀, hm₀⟩ := hmeet₀
  obtain ⟨t₁, s₁, hm₁⟩ := hmeet₁
  have ha' : ∀ t, Circle.exp (a' t) = (f t).1.2 := by
    intro t
    change Circle.exp (a t + l) = _
    rw [Circle.exp_add, hel, mul_one, ha]
  have he₀ : f s₀ = g t₀ := eq_of_cylinderLiftedCurve_eq ha hb hm₀
  have he₁ : f s₁ = g t₁ := (eq_of_cylinderLiftedCurve_eq hb ha' hm₁).symm
  have hoff := angular_offset_eq_of_forest hH hf hg a b ha hb he₀ he₁
  have hy₀ : a s₀ = b t₀ := congrArg Prod.snd hm₀
  have hy₁ : b t₁ = a s₁ + l := congrArg Prod.snd hm₁
  linarith only [hoff, hy₀, hy₁, hl]

/-- If both ends of a forest curve project into the angle interval of a
second forest curve on the chosen cuff, its lifted endpoint is the point
of that interval. This is the angular form of VI (4.2), claim (1). -/
theorem angle_lift_end_eq_of_forest
    {H : Drawing ClosedCylinder} (hH : IsGraphForest H.toGraph)
    (outer : Bool) {f g : Curve ClosedCylinder} (hf : range f ⊆ H.U) (hg : range g ⊆ H.U)
    (a b : C(unitInterval, ℝ))
    (ha : ∀ t, Circle.exp (a t) = (f t).1.2)
    (hb : ∀ t, Circle.exp (b t) = (g t).1.2)
    (hf0 : (f 0).1.1 = (if outer then 2 else 1)) (hf1 : (f 1).1.1 = (if outer then 2 else 1))
    (hg0 : (g 0).1.1 = (if outer then 2 else 1)) (hg1 : (g 1).1.1 = (if outer then 2 else 1))
    (hwidth : a 1 - a 0 < 2 * π)
    (hstart : b 0 ∈ Icc (a 0) (a 1))
    {d : ℝ} (hend : d ∈ Icc (a 0) (a 1))
    (hd : Circle.exp d = (g 1).1.2) : b 1 = d := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp ((hb 1).trans hd.symm)
  by_cases hm0 : m = 0
  · simpa only [hm0, Int.cast_zero, zero_mul, add_zero] using hm
  rcases lt_or_gt_of_ne hm0 with hmneg | hmpos
  · let g' := GM07.subPathSeg g 1 0
    let b' : C(unitInterval, ℝ) :=
      GM07.subPathSeg b 1 0 - ContinuousMap.const _ ((m : ℝ) * (2 * π))
    have hb' : ∀ t, Circle.exp (b' t) = (g' t).1.2 := by
      intro t
      change Circle.exp (GM07.subPathSeg b 1 0 t - (m : ℝ) * (2 * π)) = _
      rw [Circle.exp_sub, Circle.exp_eq_one.mpr ⟨m, rfl⟩, div_one]
      exact hb _
    have hb'0 : b' 0 = d := by
      change GM07.subPathSeg b 1 0 0 - (m : ℝ) * (2 * π) = d
      rw [GM07.subPathSeg_zero, hm]
      ring
    have hb'1 : b' 1 = b 0 + (-(m : ℝ) * (2 * π)) := by
      change GM07.subPathSeg b 1 0 1 - (m : ℝ) * (2 * π) = _
      rw [GM07.subPathSeg_one]
      ring
    have hmle : (1 : ℝ) ≤ -(m : ℝ) := by
      exact_mod_cast (show (1 : ℤ) ≤ -m by omega)
    have hl : 0 < -(m : ℝ) * (2 * π) :=
      mul_pos (lt_of_lt_of_le zero_lt_one hmle) (mul_pos (by norm_num) pi_pos)
    exact (not_positive_turn_of_forest hH outer hf
      ((GM07.range_subPathSeg_subset g 1 0).trans hg) a b' ha hb'
      hf0 hf1 (by simpa [g'] using hg1) (by simpa [g'] using hg0)
      hl (Circle.exp_eq_one.mpr ⟨-m, by simp⟩)
      (lt_of_lt_of_le hwidth (by nlinarith only [hmle, pi_pos]))
      (by simpa only [hb'0] using hend) hstart hb'1).elim
  · have hmle : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (show (1 : ℤ) ≤ m by omega)
    have hl : 0 < (m : ℝ) * (2 * π) :=
      mul_pos (lt_of_lt_of_le zero_lt_one hmle) (mul_pos (by norm_num) pi_pos)
    exact (not_positive_turn_of_forest hH outer hf hg a b ha hb hf0 hf1 hg0 hg1
      hl (Circle.exp_eq_one.mpr ⟨m, rfl⟩)
      (lt_of_lt_of_le hwidth (by nlinarith only [hmle, pi_pos])) hstart hend hm).elim

end GraphMinor.GM06
