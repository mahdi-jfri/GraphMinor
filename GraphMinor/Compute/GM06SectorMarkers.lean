module

public import GraphMinor.Compute.GM06OptionalRotationSector

/-!
# Calibrating a sector with an outside marker

The side test for VI (5.7), page 133, uses two boundary directions
and a third direction known to be outside. A supplied rotation row
may use either orientation. Swap the two sector boundaries when
the outside marker lies between them. The selected cyclic sector
then excludes that marker in either orientation.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Order the two boundary markers so the selected sector excludes the outside marker. -/
def gm06SectorMarkers (xs : List ℕ) (p q c : ℕ) : ℕ × ℕ :=
  if GM06DrawingData.cyclicBetween (xs.idxOf p) (xs.idxOf q) (xs.idxOf c) = true
    then (q, p) else (p, q)

private theorem cyclicBetween_reverse_eq_false {p q c : ℕ}
    (hpq : p ≠ q) (hpc : p ≠ c) (hqc : q ≠ c)
    (h : GM06DrawingData.cyclicBetween p q c = true) :
    GM06DrawingData.cyclicBetween q p c = false := by
  unfold GM06DrawingData.cyclicBetween at *
  split_ifs at * <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not] at * <;> omega

/-- Calibration changes only the order of the two boundary labels. -/
theorem gm06SectorMarkers_cases (xs : List ℕ) (p q c : ℕ) :
    gm06SectorMarkers xs p q c = (p, q) ∨ gm06SectorMarkers xs p q c = (q, p) := by
  unfold gm06SectorMarkers
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- For two listed boundary markers and a distinct outside marker, calibration excludes that outside marker. -/
theorem gm06SectorMarkers_outside (xs : List ℕ) {p q c : ℕ}
    (hp : p ∈ xs) (hq : q ∈ xs)
    (hpq : p ≠ q) (hpc : p ≠ c) (hqc : q ≠ c) :
    GM06DrawingData.cyclicBetween (xs.idxOf (gm06SectorMarkers xs p q c).1)
      (xs.idxOf (gm06SectorMarkers xs p q c).2) (xs.idxOf c) = false := by
  have hidx {a b : ℕ} (ha : a ∈ xs) (hab : a ≠ b) : xs.idxOf a ≠ xs.idxOf b :=
    fun hh => hab ((List.idxOf_inj ha).mp hh)
  unfold gm06SectorMarkers
  split_ifs with h
  · exact cyclicBetween_reverse_eq_false (hidx hp hpq) (hidx hp hpc) (hidx hq hqc) h
  · cases hb : GM06DrawingData.cyclicBetween (xs.idxOf p) (xs.idxOf q) (xs.idxOf c)
    · rfl
    · exact (h hb).elim

/-- The sector flag after calibration against an outside directed label. -/
def gm06CalibratedSectorFlag (xs : List ℕ) (p q c r : ℕ) : ℕ :=
  gm06RotationSectorFlag xs (gm06SectorMarkers xs p q c).1 (gm06SectorMarkers xs p q c).2 r

/-- The calibrated flag is a bit. -/
theorem gm06CalibratedSectorFlag_le_one (xs : List ℕ) (p q c r : ℕ) :
    gm06CalibratedSectorFlag xs p q c r ≤ 1 :=
  gm06RotationSectorFlag_le_one _ _ _ _

end GraphMinor.Compute
