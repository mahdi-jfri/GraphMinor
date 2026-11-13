module

public import GraphMinor.GM06.Section4LiftMeet
import GraphMinor.GM06.Section5

/-!
# Cuff paths avoiding a curve between the cuffs

In Graph Minors VI (4.2), claim (2), a region reaching both cuffs fixes a
cut in their circular order. A path off a crossing curve cannot pass
that cut in its angular lift: otherwise strip crossing forces a meeting.
Thus its lifted ends stay in the same interval between successive
translates of the crossing curve's initial point.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface Real

private theorem strip_crossing_left_le (γ δ : C(unitInterval, ℝ × ℝ))
    (hγr : ∀ t : unitInterval, (γ t).1 ∈ Icc (1 : ℝ) 2)
    (hδr : ∀ t : unitInterval, (δ t).1 ∈ Icc (1 : ℝ) 2)
    (hγ0 : (γ 0).1 = 1) (hγ1 : (γ 1).1 = 1)
    (hδ0 : (δ 0).1 = 1) (hδ1 : (δ 1).1 = 2)
    (hbetween : (δ 0).2 ∈ uIcc (γ 0).2 (γ 1).2) :
    ∃ s t : unitInterval, γ s = δ t := by
  by_cases h₀ : (γ 0).2 = (δ 0).2
  · exact ⟨0, 0, Prod.ext (hγ0.trans hδ0.symm) h₀⟩
  by_cases h₁ : (γ 1).2 = (δ 0).2
  · exact ⟨1, 0, Prod.ext (hγ1.trans hδ0.symm) h₁⟩
  apply strip_crossing_left γ δ hγr hδr hγ0 hγ1 hδ0 hδ1
  rcases le_total (γ 0).2 (γ 1).2 with hle | hle
  · rw [uIcc_of_le hle] at hbetween
    exact Or.inl ⟨lt_of_le_of_ne hbetween.1 h₀, lt_of_le_of_ne hbetween.2 (Ne.symm h₁)⟩
  · rw [uIcc_of_ge hle] at hbetween
    exact Or.inr ⟨lt_of_le_of_ne hbetween.1 h₁, lt_of_le_of_ne hbetween.2 (Ne.symm h₀)⟩

private theorem liftedCurve_other_boundary (f : Curve ClosedCylinder)
    (a : C(unitInterval, ℝ)) (outer : Bool) (t : unitInterval)
    (ht : (f t).1.1 = (if outer then 1 else 2)) :
    (cylinderLiftedCurve f a outer t).1 = 2 := by
  cases outer <;> simp_all [cylinderLiftedCurve]
  norm_num

/-- The lifted initial point of a disjoint crossing curve cannot lie
between the lifted ends of a path on the chosen cuff. -/
theorem angle_lift_start_not_between_of_disjoint_crosscurve
    (outer : Bool) {f g : Curve ClosedCylinder}
    (a b : C(unitInterval, ℝ))
    (ha : ∀ t, Circle.exp (a t) = (f t).1.2)
    (hb : ∀ t, Circle.exp (b t) = (g t).1.2)
    (hf0 : (f 0).1.1 = (if outer then 2 else 1))
    (hf1 : (f 1).1.1 = (if outer then 2 else 1))
    (hg0 : (g 0).1.1 = (if outer then 2 else 1))
    (hg1 : (g 1).1.1 = (if outer then 1 else 2))
    (hdisj : Disjoint (range f) (range g)) : b 0 ∉ uIcc (a 0) (a 1) := by
  intro hbetween
  obtain ⟨s, t, hmeet⟩ := strip_crossing_left_le
    (cylinderLiftedCurve f a outer) (cylinderLiftedCurve g b outer)
    (cylinderLiftedCurve_radius_mem f a outer)
    (cylinderLiftedCurve_radius_mem g b outer)
    (cylinderLiftedCurve_boundary f a outer 0 hf0)
    (cylinderLiftedCurve_boundary f a outer 1 hf1)
    (cylinderLiftedCurve_boundary g b outer 0 hg0)
    (liftedCurve_other_boundary g b outer 1 hg1) hbetween
  have he := eq_of_cylinderLiftedCurve_eq ha hb hmeet
  exact disjoint_left.mp hdisj (mem_range_self s) (he.symm ▸ mem_range_self t)

/-- A cuff-to-cuff curve disjoint from a path with both ends on one cuff
prevents the path's angular lift from crossing either adjacent translate
of its initial point. This supplies the homotopy constraint used in
Graph Minors VI (4.2), claim (2), page 126. -/
theorem angle_lift_end_between_of_disjoint_crosscurve
    (outer : Bool) {f g : Curve ClosedCylinder}
    (a b : C(unitInterval, ℝ))
    (ha : ∀ t, Circle.exp (a t) = (f t).1.2)
    (hb : ∀ t, Circle.exp (b t) = (g t).1.2)
    (hf0 : (f 0).1.1 = (if outer then 2 else 1))
    (hf1 : (f 1).1.1 = (if outer then 2 else 1))
    (hg0 : (g 0).1.1 = (if outer then 2 else 1))
    (hg1 : (g 1).1.1 = (if outer then 1 else 2))
    (hdisj : Disjoint (range f) (range g))
    (hstart : a 0 ∈ Ioo (b 0) (b 0 + 2 * π)) :
    a 1 ∈ Ioo (b 0) (b 0 + 2 * π) := by
  have hno (b' : C(unitInterval, ℝ))
      (hb' : ∀ t, Circle.exp (b' t) = (g t).1.2)
      (hbetween : b' 0 ∈ uIcc (a 0) (a 1)) : False :=
    angle_lift_start_not_between_of_disjoint_crosscurve outer a b' ha hb'
      hf0 hf1 hg0 hg1 hdisj hbetween
  constructor
  · by_contra hn
    have hle : a 1 ≤ b 0 := not_lt.mp hn
    apply hno b hb
    rw [uIcc_of_ge (hle.trans hstart.1.le)]
    exact ⟨hle, hstart.1.le⟩
  · by_contra hn
    have hle : b 0 + 2 * π ≤ a 1 := not_lt.mp hn
    let b' : C(unitInterval, ℝ) := b + ContinuousMap.const _ (2 * π)
    have hb' : ∀ t, Circle.exp (b' t) = (g t).1.2 := by
      intro t
      change Circle.exp (b t + 2 * π) = _
      rw [Circle.exp_add_two_pi, hb]
    apply hno b' hb'
    change b 0 + 2 * π ∈ uIcc (a 0) (a 1)
    rw [uIcc_of_le (hstart.2.le.trans hle)]
    exact ⟨hstart.2.le, hle⟩

end GraphMinor.GM06
