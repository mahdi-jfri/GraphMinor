module

public import GraphMinor.Compute.GM06Alg34Input
public import GraphMinor.GM06.Section2Dual
import Mathlib.Data.Finset.Sort

/-!
# Cyclic orders in the finite disc input

List positions in increasing angular order compare in the same way as
the angles themselves. The open arc between two angles therefore agrees
with the interval between their positions. This proves the crossing test
for a finite list of points on the circle.
-/

public section
namespace GraphMinor.GM06

open Set Surface Compute

private theorem alg34_idxOf_lt_iff {n : ℕ} {L : List (Fin n)} {f : Fin n → ℝ}
    (hL : L.Pairwise (fun a b => f a < f b)) {a b : Fin n}
    (ha : a ∈ L) (hb : b ∈ L) : L.idxOf a < L.idxOf b ↔ f a < f b := by
  have ha' := List.idxOf_lt_length_iff.mpr ha
  have hb' := List.idxOf_lt_length_iff.mpr hb
  have hforward : L.idxOf a < L.idxOf b → f a < f b := by
    intro h
    have ht := List.pairwise_iff_getElem.mp hL _ _ ha' hb' h
    simpa only [List.getElem_idxOf] using ht
  refine ⟨hforward, ?_⟩
  intro hab
  by_contra hnot
  rcases lt_or_eq_of_le (Nat.le_of_not_gt hnot) with hlt | heq
  · have ht := List.pairwise_iff_getElem.mp hL _ _ hb' ha' hlt
    have hba : f b < f a := by simpa only [List.getElem_idxOf] using ht
    exact lt_asymm hab hba
  · have he : b = a := (List.idxOf_inj hb).mp heq
    exact (ne_of_lt hab) (congrArg f he.symm)

private theorem alg34_bne_true (a b : Bool) :
    (a != b) = true ↔ ((a = true) ↔ ¬ b = true) := by
  cases a <;> cases b <;> decide

private theorem alg34_between_xor (p q s t : ℕ)
    (hps : p ≠ s) (hpt : p ≠ t) (hqs : q ≠ s) (hqt : q ≠ t) :
    (GM06DrawingData.cyclicBetween p q s != GM06DrawingData.cyclicBetween p q t) = true ↔
      ((min p q < s ∧ s < max p q) ↔ ¬ (min p q < t ∧ t < max p q)) := by
  rw [alg34_bne_true]
  simp only [GM06DrawingData.cyclicBetween]
  split_ifs <;> simp only [decide_eq_true_eq] <;> omega

/-- On an angularly sorted list of distinct circle points, the finite
crossing test is the crossing relation of VI, Section 2, page 117. -/
theorem alg34_crossesOnList_iff {n : ℕ} {L : List (Fin n)} (z : Fin n → Circle)
    (hz : Set.InjOn z {i | i ∈ L})
    (hL : L.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)))
    {a c b d : Fin n} (ha : a ∈ L) (hc : c ∈ L) (hb : b ∈ L) (hd : d ∈ L) :
    GM06DrawingData.crossesOnList L a c b d = true ↔
      circleCrosses circleStdCoord (z a) (z c) (z b) (z d) := by
  have heq {i j : Fin n} (hi : i ∈ L) (hj : j ∈ L) : z i = z j ↔ i = j :=
    ⟨fun h => hz hi hj h, fun h => congrArg z h⟩
  have harc {t : Fin n} (ht : t ∈ L) :
      onOpenArc circleStdCoord (z a) (z c) (z t) ↔
        min (L.idxOf a) (L.idxOf c) < L.idxOf t ∧
          L.idxOf t < max (L.idxOf a) (L.idxOf c) := by
    simp only [onOpenArc, min_lt_iff, lt_max_iff]
    rw [← alg34_idxOf_lt_iff hL ha ht, ← alg34_idxOf_lt_iff hL hc ht,
      ← alg34_idxOf_lt_iff hL ht ha, ← alg34_idxOf_lt_iff hL ht hc]
  simp only [GM06DrawingData.crossesOnList, Bool.and_eq_true, decide_eq_true_eq,
    ha, hc, hb, hd, true_and, circleCrosses, ne_eq, heq ha hc, heq hb hd, heq ha hb,
    heq ha hd, heq hc hb, heq hc hd, harc hb, harc hd, alg34_bne_true]
  by_cases hn : a ≠ c ∧ b ≠ d ∧ a ≠ b ∧ a ≠ d ∧ c ≠ b ∧ c ≠ d
  · have hac := mt (List.idxOf_inj ha).mp hn.1
    have hab := mt (List.idxOf_inj ha).mp hn.2.2.1
    have had := mt (List.idxOf_inj ha).mp hn.2.2.2.1
    have hcb := mt (List.idxOf_inj hc).mp hn.2.2.2.2.1
    have hcd := mt (List.idxOf_inj hc).mp hn.2.2.2.2.2
    simp only [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1,
      hn.2.2.2.2.2, not_false_eq_true, true_and]
    simpa only [alg34_bne_true] using alg34_between_xor _ _ _ _ hab had hcb hcd
  · tauto

end GraphMinor.GM06
