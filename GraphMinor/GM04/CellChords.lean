module

public import GraphMinor.GM04.Painting
import GraphMinor.GM06.Section2Dual
import GraphMinor.GM12.Section4ChordSeparation
import GraphMinor.GM12.Section4ChordGeometry

/-!
# Drawing noncrossing pairs by chords

The forest-drawing step in IV (9.2), page 254, draws a pairing inside each
cell. Chords of the unit disc join its boundary points. For nonalternating
pairs they are disjoint. A disc homeomorphism then gives the required lines
in a cell.
-/

public section

namespace GraphMinor.GM04

open Set Surface

private theorem eC_add_period (a : ℝ) : eC (a + 2 * Real.pi) = eC a := by
  simpa only [Int.cast_one, mul_one] using eC_add_int a 1

private theorem chords_disjoint_ordered {a c b d : ℝ}
    (ha : -Real.pi < a ∧ a ≤ Real.pi) (hc : -Real.pi < c ∧ c ≤ Real.pi)
    (hb : -Real.pi < b ∧ b ≤ Real.pi) (hd : -Real.pi < d ∧ d ≤ Real.pi)
    (hac : a < c) (hbd : b < d)
    (hab : a ≠ b) (had : a ≠ d) (hcb : c ≠ b) (hcd : c ≠ d)
    (hsame : (a < b ∧ b < c) ↔ (a < d ∧ d < c)) :
    Disjoint (segment ℝ (eC a) (eC c)) (segment ℝ (eC b) (eC d)) := by
  by_cases hcb' : c < b
  · exact GM12.ordered_unit_chords_disjoint hac hcb' hbd (by linarith [hd.2, ha.1])
  by_cases hda : d < a
  · exact (GM12.ordered_unit_chords_disjoint hbd hda hac (by linarith [hc.2, hb.1])).symm
  have hbc : b < c := lt_of_le_of_ne (le_of_not_gt hcb') hcb.symm
  have had' : a < d := lt_of_le_of_ne (le_of_not_gt hda) had
  rcases lt_or_gt_of_ne hab with hab' | hba
  · have hdc : d < c := (hsame.mp ⟨hab', hbc⟩).2
    have h := GM12.ordered_unit_chords_disjoint hbd hdc
      (show c < a + 2 * Real.pi by linarith [hc.2, ha.1])
      (show a + 2 * Real.pi < b + 2 * Real.pi by linarith)
    rw [eC_add_period] at h
    rw [segment_symm ℝ (eC c) (eC a)] at h
    exact h.symm
  · have hcd' : c < d := by
      have hout : ¬ (a < d ∧ d < c) := fun h ↦ (not_lt_of_gt hba) (hsame.mpr h).1
      exact lt_of_le_of_ne (le_of_not_gt (fun hdc ↦ hout ⟨had', hdc⟩)) hcd
    have h := GM12.ordered_unit_chords_disjoint hac hcd'
      (show d < b + 2 * Real.pi by linarith [hd.2, hb.1])
      (show b + 2 * Real.pi < a + 2 * Real.pi by linarith)
    rw [eC_add_period] at h
    rwa [segment_symm ℝ (eC d) (eC b)] at h

private theorem chords_disjoint_of_arg_lt {a c b d : Circle}
    (hac : circleStdCoord.angle a < circleStdCoord.angle c)
    (hbd : circleStdCoord.angle b < circleStdCoord.angle d)
    (hab : a ≠ b) (had : a ≠ d) (hcb : c ≠ b) (hcd : c ≠ d)
    (hnc : ¬ circleCrosses circleStdCoord a c b d) :
    Disjoint (segment ℝ (a : ℂ) (c : ℂ)) (segment ℝ (b : ℂ) (d : ℂ)) := by
  have hacne : a ≠ c := fun h ↦ (ne_of_lt hac) (congrArg circleStdCoord.angle h)
  have hbdne : b ≠ d := fun h ↦ (ne_of_lt hbd) (congrArg circleStdCoord.angle h)
  have hnot : ¬ ((circleStdCoord.angle a < circleStdCoord.angle b ∧
      circleStdCoord.angle b < circleStdCoord.angle c) ↔
      ¬ (circleStdCoord.angle a < circleStdCoord.angle d ∧
      circleStdCoord.angle d < circleStdCoord.angle c)) := by
    intro hx
    apply hnc
    refine ⟨hacne, hbdne, hab, had, hcb, hcd, ?_⟩
    simpa only [onOpenArc, min_eq_left hac.le, max_eq_right hac.le] using hx
  have hsame : (circleStdCoord.angle a < circleStdCoord.angle b ∧
      circleStdCoord.angle b < circleStdCoord.angle c) ↔
      (circleStdCoord.angle a < circleStdCoord.angle d ∧
      circleStdCoord.angle d < circleStdCoord.angle c) := by tauto
  have h := chords_disjoint_ordered
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩ hac hbd
    (circleStdCoord.injective.ne hab) (circleStdCoord.injective.ne had)
    (circleStdCoord.injective.ne hcb) (circleStdCoord.injective.ne hcd) hsame
  have hexp (z : Circle) : eC (Complex.arg (z : ℂ)) = (z : ℂ) := by
    change ((Circle.exp (Complex.arg (z : ℂ)) : Circle) : ℂ) = (z : ℂ)
    rw [Circle.exp_arg]
  simpa only [hexp] using h

/-- Distinct noncrossing pairs of unit-circle points have disjoint straight
chords. This supplies the disjoint lines used within a cell in IV (9.2). -/
theorem unit_chords_disjoint_of_not_crosses {a c b d : Circle}
    (hac : a ≠ c) (hbd : b ≠ d) (hab : a ≠ b) (had : a ≠ d)
    (hcb : c ≠ b) (hcd : c ≠ d)
    (hnc : ¬ GM06.CrossesOn (univ : Set Circle) a c b d) :
    Disjoint (segment ℝ (a : ℂ) (c : ℂ)) (segment ℝ (b : ℂ) (d : ℂ)) := by
  have hn : ¬ circleCrosses circleStdCoord a c b d :=
    fun h ↦ hnc (GM06.crossesOn_univ_iff_circleStdCoord.mpr h)
  rcases lt_or_gt_of_ne (circleStdCoord.injective.ne hac) with hac' | hca'
  · rcases lt_or_gt_of_ne (circleStdCoord.injective.ne hbd) with hbd' | hdb'
    · exact chords_disjoint_of_arg_lt hac' hbd' hab had hcb hcd hn
    · have h := chords_disjoint_of_arg_lt hac' hdb' had hab hcd hcb
        (fun h ↦ hn ((circleCrosses_symm_right _ _ _ _ _).mpr h))
      rwa [segment_symm ℝ (d : ℂ) (b : ℂ)] at h
  · rcases lt_or_gt_of_ne (circleStdCoord.injective.ne hbd) with hbd' | hdb'
    · have h := chords_disjoint_of_arg_lt hca' hbd' hcb hcd hab had
        (fun h ↦ hn ((circleCrosses_symm_left _ _ _ _ _).mpr h))
      rwa [segment_symm ℝ (c : ℂ) (a : ℂ)] at h
    · have h := chords_disjoint_of_arg_lt hca' hdb' hcd hcb had hab
        (fun h ↦ hn ((circleCrosses_symm_left _ _ _ _ _).mpr
          ((circleCrosses_symm_right _ _ _ _ _).mpr h)))
      rwa [segment_symm ℝ (c : ℂ) (a : ℂ), segment_symm ℝ (d : ℂ) (b : ℂ)] at h

end GraphMinor.GM04
