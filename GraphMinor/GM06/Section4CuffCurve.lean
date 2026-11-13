module

public import GraphMinor.GM06.Section4LiftMeet
import Mathlib.Topology.Order.IntermediateValue

/-!
# Subarcs on a cuff and forest curves

An injective cuff curve lifts to a real interval shorter than one full
turn. The forced-meeting argument identifies the endpoint of any forest
curve whose ends lie in this interval. Equality of winding then gives the
homotopy required in Graph Minors VI (4.2), claim (1).
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface Real Function

private theorem exists_angle_lift_start (f : Curve ClosedCylinder)
    (c : ℝ) (hc : Circle.exp c = (f 0).1.2) :
    ∃ b : C(unitInterval, ℝ), b 0 = c ∧ ∀ t, Circle.exp (b t) = (f t).1.2 := by
  let b := Circle.isCoveringMap_exp.liftPath (curveCircleProj f) c hc.symm
  exact ⟨b, Circle.isCoveringMap_exp.liftPath_zero _ _ _,
    fun t => congr_fun (Circle.isCoveringMap_exp.liftPath_lifts _ _ _) t⟩

private theorem lift_width_lt_two_pi (a : C(unitInterval, ℝ))
    (hi : Injective (Circle.exp ∘ a)) : a 1 - a 0 < 2 * π := by
  by_contra h
  have hab : a 0 + 2 * π ∈ Icc (a 0) (a 1) :=
    ⟨by linarith only [pi_pos], by linarith only [not_lt.mp h]⟩
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc
    (show (0 : unitInterval) ≤ 1 from zero_le_one) a.continuous.continuousOn hab
  have he : Circle.exp (a t) = Circle.exp (a 0) := by
    rw [ht, Circle.exp_add_two_pi]
  have ht0 : t = 0 := hi he
  rw [ht0] at ht
  linarith only [ht, pi_pos]

private theorem angle_lift_end_eq_of_forest_uIcc
    {H : Drawing ClosedCylinder} (hH : IsGraphForest H.toGraph)
    (outer : Bool) {f g : Curve ClosedCylinder} (hf : range f ⊆ H.U) (hg : range g ⊆ H.U)
    (a b : C(unitInterval, ℝ))
    (ha : ∀ t, Circle.exp (a t) = (f t).1.2)
    (hb : ∀ t, Circle.exp (b t) = (g t).1.2)
    (hf0 : (f 0).1.1 = (if outer then 2 else 1))
    (hf1 : (f 1).1.1 = (if outer then 2 else 1))
    (hg0 : (g 0).1.1 = (if outer then 2 else 1))
    (hg1 : (g 1).1.1 = (if outer then 2 else 1))
    (hwidth : a 1 - a 0 < 2 * π) (hwidth' : a 0 - a 1 < 2 * π)
    (hstart : b 0 ∈ uIcc (a 0) (a 1))
    {d : ℝ} (hend : d ∈ uIcc (a 0) (a 1))
    (hd : Circle.exp d = (g 1).1.2) : b 1 = d := by
  rcases le_total (a 0) (a 1) with hle | hle
  · exact angle_lift_end_eq_of_forest hH outer hf hg a b ha hb hf0 hf1 hg0 hg1
      hwidth (by simpa only [uIcc_of_le hle] using hstart)
      (by simpa only [uIcc_of_le hle] using hend) hd
  · exact angle_lift_end_eq_of_forest hH outer
      ((GM07.range_subPathSeg_subset f 1 0).trans hf) hg
      (GM07.subPathSeg a 1 0) b (fun t => ha _) hb
      (by simpa only [GM07.subPathSeg_zero] using hf1)
      (by simpa only [GM07.subPathSeg_one] using hf0) hg0 hg1
      (by simpa only [GM07.subPathSeg_one, GM07.subPathSeg_zero] using hwidth')
      (by simpa only [GM07.subPathSeg_zero, GM07.subPathSeg_one, uIcc_of_ge hle] using hstart)
      (by simpa only [GM07.subPathSeg_zero, GM07.subPathSeg_one, uIcc_of_ge hle] using hend) hd

/-- Along an injective cuff curve, the angular lift stays between its
endpoint values. -/
theorem cylinderAngleLift_mem_uIcc_of_cuff_line
    {k : Curve ClosedCylinder} (hk : Function.Injective k)
    {r : ℝ} (hkr : ∀ t, (k t).1.1 = r) (t : unitInterval) :
    cylinderAngleLift k t ∈ uIcc (cylinderAngleLift k 0) (cylinderAngleLift k 1) := by
  have hi : Function.Injective (cylinderAngleLift k) := by
    intro x y hxy
    apply hk
    apply Subtype.ext
    apply Prod.ext
    · exact (hkr x).trans (hkr y).symm
    · rw [← exp_cylinderAngleLift, ← exp_cylinderAngleLift, hxy]
  rcases (cylinderAngleLift k).continuous.strictMono_of_inj_boundedOrder' hi with hm | hm
  · exact ⟨min_le_of_left_le (hm.monotone (show (0 : unitInterval) ≤ t from bot_le)),
      le_max_of_le_right (hm.monotone (show t ≤ (1 : unitInterval) from le_top))⟩
  · exact ⟨min_le_of_right_le (hm.antitone (show t ≤ (1 : unitInterval) from le_top)),
      le_max_of_le_left (hm.antitone (show (0 : unitInterval) ≤ t from bot_le))⟩

/-- A forest curve with ends on an injective cuff arc is homotopic to the
portion of that arc between its ends, provided the forest also contains
a curve homotopic to the full arc. This is the path form of the
no-circuit argument in Graph Minors VI (4.2), claim (1), page 125. -/
theorem forest_curve_homotopic_to_cuff_subcurve
    {H : Drawing ClosedCylinder} (hH : IsGraphForest H.toGraph)
    (outer : Bool) {f g k : Curve ClosedCylinder}
    (hf : range f ⊆ H.U) (hg : range g ⊆ H.U)
    (hk : Injective k) (hkr : ∀ t, (k t).1.1 = (if outer then 2 else 1))
    (hfk : CurvesHomotopic f k) {s t : unitInterval}
    (hg0 : g 0 = k s) (hg1 : g 1 = k t) :
    CurvesHomotopic g (GM07.subPathSeg k s t) := by
  let a := cylinderAngleLift k
  have hai : Injective (Circle.exp ∘ a) := by
    intro x y hxy
    apply hk
    apply Subtype.ext
    apply Prod.ext
    · exact (hkr x).trans (hkr y).symm
    · simpa only [Function.comp_apply, a, exp_cylinderAngleLift] using hxy
  have ha_width := lift_width_lt_two_pi a hai
  have ha_width' : a 0 - a 1 < 2 * π := by
    have hrev := lift_width_lt_two_pi (GM07.subPathSeg a 1 0)
      (hai.comp (by
        intro x y hxy
        apply Subtype.ext
        have he := congrArg Subtype.val hxy
        dsimp at he
        linarith only [he]))
    simpa only [GM07.subPathSeg_zero, GM07.subPathSeg_one] using hrev
  have ha_inj : Injective a := fun x y h => hai (congrArg Circle.exp h)
  have ha_between (v : unitInterval) : a v ∈ uIcc (a 0) (a 1) := by
    rcases a.continuous.strictMono_of_inj_boundedOrder' ha_inj with hm | hm
    · exact ⟨min_le_of_left_le (hm.monotone (show (0 : unitInterval) ≤ v from bot_le)),
        le_max_of_le_right (hm.monotone (show v ≤ (1 : unitInterval) from le_top))⟩
    · exact ⟨min_le_of_right_le (hm.antitone (show v ≤ (1 : unitInterval) from le_top)),
        le_max_of_le_left (hm.antitone (show (0 : unitInterval) ≤ v from bot_le))⟩
  have hf0k : f 0 = k 0 := by
    obtain ⟨ψ, _, hψ0, hψ1, hψy0, hψy0', _, _⟩ := hfk
    exact (hψy0 0).symm.trans (hψy0' 0)
  have hf1k : f 1 = k 1 := by
    obtain ⟨ψ, _, _, _, _, _, hψy1, hψy1'⟩ := hfk
    exact (hψy1 0).symm.trans (hψy1' 0)
  obtain ⟨af, haf0, haf⟩ := exists_angle_lift_start f (a 0)
    (by rw [hf0k]; exact exp_cylinderAngleLift k 0)
  have haf1 : af 1 = a 1 := by
    have hw := windingNumber_eq_of_homotopic hfk
    rw [windingNumber_eq_of_exp_lift af haf,
      windingNumber_eq_of_exp_lift a (exp_cylinderAngleLift k), haf0] at hw
    exact (sub_left_inj).mp ((div_left_inj' (mul_ne_zero (by norm_num)
      Real.pi_ne_zero)).mp hw)
  obtain ⟨b, hb0, hb⟩ := exists_angle_lift_start g (a s)
    (by rw [hg0]; exact exp_cylinderAngleLift k s)
  have hb1 : b 1 = a t := by
    apply angle_lift_end_eq_of_forest_uIcc hH outer hf hg af b haf hb
    · rw [hf0k]; exact hkr 0
    · rw [hf1k]; exact hkr 1
    · rw [hg0]; exact hkr s
    · rw [hg1]; exact hkr t
    · simpa only [haf1, haf0] using ha_width
    · simpa only [haf0, haf1] using ha_width'
    · simpa only [hb0, haf0, haf1] using ha_between s
    · simpa only [haf0, haf1] using ha_between t
    · rw [hg1]; exact exp_cylinderAngleLift k t
  apply curvesHomotopic_of_windingNumber_eq
  · simpa only [GM07.subPathSeg_zero] using hg0
  · simpa only [GM07.subPathSeg_one] using hg1
  · rw [windingNumber_eq_of_exp_lift b hb, hb0, hb1,
      windingNumber_subPathSeg_of_exp_lift a (exp_cylinderAngleLift k)]

end GraphMinor.GM06
