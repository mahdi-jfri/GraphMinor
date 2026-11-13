module

public import GraphMinor.Compute.GM06OptionalRotationSector
public import GraphMinor.GM06.Section2Dual

/-!
# Interpreting the finite rotation sector on the polar circle

For VI (5.7), page 133, a row of directed-end labels has the cyclic
order of its polar rim points. Comparing row positions is therefore
comparing their angles. A third marker outside the selected sector
turns the sector test into the four-point crossing relation on the
rim. The marker removes the choice of where the cyclic row starts.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.Compute

private theorem idxOf_lt_iff_of_sorted {xs : List ℕ} {f : ℕ → ℝ}
    (hs : xs.Pairwise (fun a b => f a < f b)) {a b : ℕ}
    (ha : a ∈ xs) (hb : b ∈ xs) : xs.idxOf a < xs.idxOf b ↔ f a < f b := by
  have hforward : xs.idxOf a < xs.idxOf b → f a < f b := by
    intro h
    have hh := List.pairwise_iff_getElem.mp hs _ _
      (List.idxOf_lt_length_iff.mpr ha) (List.idxOf_lt_length_iff.mpr hb) h
    simpa only [List.getElem_idxOf] using hh
  refine ⟨hforward, ?_⟩
  intro hab
  by_contra hh
  rcases lt_or_eq_of_le (Nat.le_of_not_gt hh) with hlt | heq
  · have hh := List.pairwise_iff_getElem.mp hs _ _
      (List.idxOf_lt_length_iff.mpr hb) (List.idxOf_lt_length_iff.mpr ha) hlt
    have hba : f b < f a := by simpa only [List.getElem_idxOf] using hh
    exact lt_asymm hab hba
  · have hba : b = a := (List.idxOf_inj hb).mp heq
    exact hab.ne (congrArg f hba.symm)
private theorem between_xor_iff (p q r c : ℕ)
    (hpr : p ≠ r) (hpc : p ≠ c) (hqr : q ≠ r) (hqc : q ≠ c) :
    (GM06DrawingData.cyclicBetween p q r != GM06DrawingData.cyclicBetween p q c) = true ↔
      ((min p q < r ∧ r < max p q) ↔ ¬ (min p q < c ∧ c < max p q)) := by
  have hbool (a b : Bool) : (a != b) = true ↔ (a = true ↔ ¬ b = true) := by
    cases a <;> cases b <;> decide
  rw [hbool]
  simp only [GM06DrawingData.cyclicBetween]
  split_ifs <;> simp only [decide_eq_true_eq] <;> omega

/-- On an angularly sorted rotation row, the sector bit equals
crossing the chosen two markers against the candidate and an outside marker. -/
theorem rotationSectorFlag_eq_one_iff_crossesOn
    (xs : List ℕ) (z : ℕ → Circle)
    (hz : Set.InjOn z {a | a ∈ xs})
    (hs : xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)))
    {p q r c : ℕ} (hp : p ∈ xs) (hq : q ∈ xs) (hr : r ∈ xs) (hc : c ∈ xs)
    (hpq : p ≠ q) (hrc : r ≠ c) (hpr : p ≠ r) (hpc : p ≠ c)
    (hqr : q ≠ r) (hqc : q ≠ c)
    (hout : GM06DrawingData.cyclicBetween (xs.idxOf p) (xs.idxOf q) (xs.idxOf c) = false) :
    gm06RotationSectorFlag xs p q r = 1 ↔
      CrossesOn (univ : Set Circle) (z p) (z q) (z r) (z c) := by
  have hi {a b : ℕ} (ha : a ∈ xs) (hb : b ∈ xs) :
      xs.idxOf a < xs.idxOf b ↔ circleStdCoord.angle (z a) < circleStdCoord.angle (z b) :=
    idxOf_lt_iff_of_sorted hs ha hb
  have hidx {a b : ℕ} (ha : a ∈ xs) (hb : b ∈ xs) (hab : a ≠ b) :
      xs.idxOf a ≠ xs.idxOf b := fun hh => hab ((List.idxOf_inj ha).mp hh)
  have hon {a : ℕ} (ha : a ∈ xs) :
      onOpenArc circleStdCoord (z p) (z q) (z a) ↔
        min (xs.idxOf p) (xs.idxOf q) < xs.idxOf a ∧
          xs.idxOf a < max (xs.idxOf p) (xs.idxOf q) := by
    unfold onOpenArc
    by_cases hpqlt : xs.idxOf p < xs.idxOf q
    · have hh := (hi hp hq).mp hpqlt
      rw [min_eq_left hh.le, max_eq_right hh.le,
        min_eq_left hpqlt.le, max_eq_right hpqlt.le]
      exact and_congr (hi hp ha).symm (hi ha hq).symm
    · have hqplt : xs.idxOf q < xs.idxOf p :=
        lt_of_le_of_ne (Nat.le_of_not_gt hpqlt) (hidx hq hp hpq.symm)
      have hh := (hi hq hp).mp hqplt
      rw [min_eq_right hh.le, max_eq_left hh.le,
        min_eq_right hqplt.le, max_eq_left hqplt.le]
      exact and_congr (hi hq ha).symm (hi ha hp).symm
  have hzp : z p ≠ z q := fun hh => hpq (hz hp hq hh)
  have hzr : z r ≠ z c := fun hh => hrc (hz hr hc hh)
  have hzpr : z p ≠ z r := fun hh => hpr (hz hp hr hh)
  have hzpc : z p ≠ z c := fun hh => hpc (hz hp hc hh)
  have hzqr : z q ≠ z r := fun hh => hqr (hz hq hr hh)
  have hzqc : z q ≠ z c := fun hh => hqc (hz hq hc hh)
  have hcross : circleCrosses circleStdCoord (z p) (z q) (z r) (z c) ↔
      (GM06DrawingData.cyclicBetween (xs.idxOf p) (xs.idxOf q) (xs.idxOf r) !=
        GM06DrawingData.cyclicBetween (xs.idxOf p) (xs.idxOf q) (xs.idxOf c)) = true := by
    have hbetween := between_xor_iff _ _ _ _ (hidx hp hr hpr) (hidx hp hc hpc)
      (hidx hq hr hqr) (hidx hq hc hqc)
    constructor
    · intro h
      apply hbetween.mpr
      exact (hon hr).symm.trans (h.2.2.2.2.2.2.trans (not_congr (hon hc)))
    · intro h
      refine ⟨hzp, hzr, hzpr, hzpc, hzqr, hzqc, ?_⟩
      exact (hon hr).trans ((hbetween.mp h).trans (not_congr (hon hc)).symm)
  rw [crossesOn_univ_iff_circleStdCoord, hcross, hout, gm06RotationSectorFlag_eq_one]
  simp only [hr, true_and]
  cases GM06DrawingData.cyclicBetween (xs.idxOf p) (xs.idxOf q) (xs.idxOf r) <;> decide

end GraphMinor.GM06
