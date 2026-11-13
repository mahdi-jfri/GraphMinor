module

public import GraphMinor.GM04.Painting
import GraphMinor.GM06.Section2Dual
import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Noncrossing pairings for the cells of a painting

The robustness assertion in the proof of IV (9.2), page 254, needs a
noncrossing matching between equally many prescribed nodes of two colours.
A matching of least total cost cannot have crossing edges: exchanging their
ends would lower the cost. The cost for coordinates `a,b` is
`|a-b| (L-|a-b|)`, with `L` larger than their coordinate range.
-/

public section

namespace GraphMinor.GM04

open Finset

/-- A minimum-cost bijection between two finite sets admits no improving
exchange of two images. This supplies the finite choice used in the robustness
step of the proof of IV (9.2), page 254. -/
theorem exists_equiv_exchange_le {A B : Type*} [Fintype A] [Fintype B]
    (hcard : Fintype.card A = Fintype.card B) (cost : A → B → ℝ) :
    ∃ e : A ≃ B, ∀ x y,
      cost x (e x) + cost y (e y) ≤ cost x (e y) + cost y (e x) := by
  classical
  have : Nonempty (A ≃ B) := ⟨Fintype.equivOfCardEq hcard⟩
  obtain ⟨e, he⟩ := Finite.exists_min (fun f : A ≃ B ↦ ∑ x, cost x (f x))
  refine ⟨e, fun x y ↦ ?_⟩
  by_cases hxy : x = y
  · subst y
    exact le_rfl
  have hmin := he ((Equiv.swap x y).trans e)
  change (∑ a, cost a (e a)) ≤ ∑ a, cost a (e (Equiv.swap x y a)) at hmin
  have hsum : (∑ a, (cost a (e a) - cost a (e (Equiv.swap x y a)))) =
      (cost x (e x) - cost x (e y)) + (cost y (e y) - cost y (e x)) := by
    have hsupport : ∑ a ∈ ({x, y} : Finset A),
        (cost a (e a) - cost a (e (Equiv.swap x y a))) =
        ∑ a, (cost a (e a) - cost a (e (Equiv.swap x y a))) := by
      apply sum_subset (subset_univ _)
      intro a _ ha
      have hax : a ≠ x := fun h ↦ ha (by simp [h])
      have hay : a ≠ y := fun h ↦ ha (by simp [h])
      rw [Equiv.swap_apply_of_ne_of_ne hax hay, sub_self]
    rw [← hsupport, sum_pair hxy]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hnonpos : (∑ a, (cost a (e a) - cost a (e (Equiv.swap x y a)))) ≤ 0 := by
    rw [sum_sub_distrib]
    exact sub_nonpos.mpr hmin
  rw [hsum] at hnonpos
  linarith

/-- The symmetric cost used to remove crossing pairs in IV (9.2). -/
noncomputable def pairingCost (L a b : ℝ) : ℝ := |a - b| * (L - |a - b|)

private theorem pairingCost_comm (L a b : ℝ) : pairingCost L a b = pairingCost L b a := by
  unfold pairingCost
  rw [abs_sub_comm]

/-- For four cyclically ordered coordinates, either uncrossing of their
crossed pairs strictly lowers the cost. -/
theorem pairingCost_uncross {L a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hspan : d - a < L) :
    pairingCost L a b + pairingCost L c d < pairingCost L a c + pairingCost L b d ∧
    pairingCost L a d + pairingCost L b c < pairingCost L a c + pairingCost L b d := by
  have hac : a < c := hab.trans hbc
  have hbd : b < d := hbc.trans hcd
  have had : a < d := hac.trans hcd
  simp only [pairingCost, abs_of_neg (sub_neg.mpr hab),
    abs_of_neg (sub_neg.mpr hbc), abs_of_neg (sub_neg.mpr hcd),
    abs_of_neg (sub_neg.mpr hac), abs_of_neg (sub_neg.mpr hbd),
    abs_of_neg (sub_neg.mpr had)]
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hbc) (sub_pos.mpr hspan)]
  · nlinarith [mul_pos (sub_pos.mpr hab) (sub_pos.mpr hcd)]

private theorem pairingCost_uncross_oriented {L lo hi a b c d : ℝ}
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi)
    (hc : lo ≤ c ∧ c ≤ hi) (hd : lo ≤ d ∧ d ≤ hi) (hspan : hi - lo < L)
    (_hac : a < c) (hba : b ≠ a) (hbc : b ≠ c) (hda : d ≠ a) (hdc : d ≠ c)
    (hcross : (a < b ∧ b < c) ↔ ¬ (a < d ∧ d < c)) :
    pairingCost L a b + pairingCost L c d < pairingCost L a c + pairingCost L b d ∧
    pairingCost L a d + pairingCost L b c < pairingCost L a c + pairingCost L b d := by
  by_cases hbmid : a < b ∧ b < c
  · have hdout := hcross.mp hbmid
    have hdside : d < a ∨ c < d := by
      rcases le_or_gt d a with h | h
      · exact Or.inl (lt_of_le_of_ne h hda)
      · exact Or.inr (lt_of_le_of_ne (le_of_not_gt (fun hdc' ↦ hdout ⟨h, hdc'⟩)) hdc.symm)
    rcases hdside with hda' | hcd
    · have h := pairingCost_uncross hda' hbmid.1 hbmid.2 (show c - d < L by linarith [hc.2, hd.1])
      simpa only [pairingCost_comm, add_comm] using And.intro h.2 h.1
    · exact pairingCost_uncross hbmid.1 hbmid.2 hcd (by linarith [hd.2, ha.1])
  · have hdmid : a < d ∧ d < c := by
      by_contra hdout
      exact hbmid (hcross.mpr hdout)
    have hbside : b < a ∨ c < b := by
      rcases le_or_gt b a with h | h
      · exact Or.inl (lt_of_le_of_ne h hba)
      · exact Or.inr (lt_of_le_of_ne (le_of_not_gt (fun hbc' ↦ hbmid ⟨h, hbc'⟩)) hbc.symm)
    rcases hbside with hba' | hcb
    · have h := pairingCost_uncross hba' hdmid.1 hdmid.2 (show c - b < L by linarith [hc.2, hb.1])
      simpa only [pairingCost_comm, add_comm] using h
    · have h := pairingCost_uncross hdmid.1 hdmid.2 hcb (show b - a < L by linarith [hb.2, ha.1])
      simpa only [pairingCost_comm, add_comm] using And.intro h.2 h.1

/-- Crossing pairs have an improving exchange for every injective circular
coordinate whose range is shorter than `L`. This is the uncrossing step in the
robustness assertion of IV (9.2), page 254. -/
theorem pairingCost_lt_of_circleCrosses {C : Type*} (coord : Surface.CircleCoord C)
    {L lo hi : ℝ} (hbound : ∀ x, lo ≤ coord.angle x ∧ coord.angle x ≤ hi)
    (hspan : hi - lo < L) {a c b d : C} (hcross : Surface.circleCrosses coord a c b d) :
    pairingCost L (coord.angle a) (coord.angle d) +
      pairingCost L (coord.angle b) (coord.angle c) <
    pairingCost L (coord.angle a) (coord.angle c) +
      pairingCost L (coord.angle b) (coord.angle d) := by
  obtain ⟨hac, _, hab, had, hcb, hcd, hxor⟩ := hcross
  have hane := coord.injective.ne hac
  have hba := (coord.injective.ne hab).symm
  have hbc := (coord.injective.ne hcb).symm
  have hda := (coord.injective.ne had).symm
  have hdc := (coord.injective.ne hcd).symm
  rcases lt_or_gt_of_ne hane with hac' | hca'
  · have hxor' : (coord.angle a < coord.angle b ∧ coord.angle b < coord.angle c) ↔
        ¬ (coord.angle a < coord.angle d ∧ coord.angle d < coord.angle c) := by
      simpa only [Surface.onOpenArc, min_eq_left hac'.le, max_eq_right hac'.le] using hxor
    exact (pairingCost_uncross_oriented (hbound a) (hbound b) (hbound c) (hbound d)
      hspan hac' hba hbc hda hdc hxor').2
  · have hxor' : (coord.angle c < coord.angle b ∧ coord.angle b < coord.angle a) ↔
        ¬ (coord.angle c < coord.angle d ∧ coord.angle d < coord.angle a) := by
      simpa only [Surface.onOpenArc, min_eq_right hca'.le, max_eq_left hca'.le] using hxor
    have h := (pairingCost_uncross_oriented (hbound c) (hbound b) (hbound a) (hbound d)
      hspan hca' hbc hba hdc hda hxor').1
    simpa only [pairingCost_comm, add_comm] using h

/-- Equally large finite sets in a bounded circular coordinate have a
bijection whose pairs do not cross. This supplies the matching used for the
robustness assertion in IV (9.2), page 254. -/
theorem exists_equiv_noncrossing {C : Type*} (coord : Surface.CircleCoord C)
    {L lo hi : ℝ} (hbound : ∀ x, lo ≤ coord.angle x ∧ coord.angle x ≤ hi)
    (hspan : hi - lo < L) (X Y : Set C) (hX : X.Finite) (hY : Y.Finite)
    (hcard : X.ncard = Y.ncard) :
    ∃ e : X ≃ Y, ∀ x y : X,
      ¬ Surface.circleCrosses coord x (e x) y (e y) := by
  classical
  let : Fintype X := hX.fintype
  let : Fintype Y := hY.fintype
  have hcard' : Fintype.card X = Fintype.card Y := by
    simpa only [Set.fintypeCard_eq_ncard] using hcard
  obtain ⟨e, he⟩ := exists_equiv_exchange_le hcard'
    (fun x y ↦ pairingCost L (coord.angle x) (coord.angle y))
  refine ⟨e, fun x y hcross ↦ ?_⟩
  exact (not_lt_of_ge (he x y)) (pairingCost_lt_of_circleCrosses coord hbound hspan hcross)

end GraphMinor.GM04
