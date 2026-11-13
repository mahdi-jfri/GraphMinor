module

public import GraphMinor.GM06.Section5CalibratedRotationOrder

/-!
# The calibrated crossing test at every listed label

The strict sector excludes both boundary labels, and calibration
excludes the outside label. A crossing also requires four distinct
points. Thus the finite and geometric tests agree at the three
markers as well as at the other labels. This permits the edge scan
in VI (5.7), page 133, to include edges of the given linkage.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.Compute

private theorem cyclicBetween_boundary_false (a b : ℕ) :
    GM06DrawingData.cyclicBetween a b a = false ∧
      GM06DrawingData.cyclicBetween a b b = false := by
  unfold GM06DrawingData.cyclicBetween
  split_ifs <;> simp_all

/-- Calibration excludes each of the three marker labels from its
strict sector, without requiring the labels to be consecutive. -/
theorem calibratedSectorFlag_markers_ne_one (xs : List ℕ) {p q c : ℕ}
    (hp : p ∈ xs) (hq : q ∈ xs) (hpq : p ≠ q) (hpc : p ≠ c) (hqc : q ≠ c) :
    gm06CalibratedSectorFlag xs p q c p ≠ 1 ∧
      gm06CalibratedSectorFlag xs p q c q ≠ 1 ∧
      gm06CalibratedSectorFlag xs p q c c ≠ 1 := by
  have hout := gm06SectorMarkers_outside xs hp hq hpq hpc hqc
  have hboundary (a b r : ℕ) (hr : r = a ∨ r = b) :
      gm06RotationSectorFlag xs a b r ≠ 1 := by
    intro hh
    have ht := (gm06RotationSectorFlag_eq_one xs a b r).mp hh |>.2
    rcases hr with rfl | rfl
    · rw [(cyclicBetween_boundary_false _ _).1] at ht
      cases ht
    · rw [(cyclicBetween_boundary_false _ _).2] at ht
      cases ht
  refine ⟨?_, ?_, ?_⟩
  · unfold gm06CalibratedSectorFlag
    rcases gm06SectorMarkers_cases xs p q c with hh | hh <;> rw [hh]
    · exact hboundary p q p (Or.inl rfl)
    · exact hboundary q p p (Or.inr rfl)
  · unfold gm06CalibratedSectorFlag
    rcases gm06SectorMarkers_cases xs p q c with hh | hh <;> rw [hh]
    · exact hboundary p q q (Or.inr rfl)
    · exact hboundary q p q (Or.inl rfl)
  · intro hh
    have ht := (gm06RotationSectorFlag_eq_one xs _ _ c).mp hh |>.2
    rw [hout] at ht
    cases ht

/-- Every listed directed label, including a marker, satisfies the
calibrated flag exactly when its four geometric directions cross. -/
theorem calibratedSectorFlag_eq_one_iff_crossesOn_of_mem
    (xs : List ℕ) (z : ℕ → Circle)
    (hz : Set.InjOn z {a | a ∈ xs})
    (hs : xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)))
    {p q r c : ℕ} (hp : p ∈ xs) (hq : q ∈ xs) (hr : r ∈ xs) (hc : c ∈ xs)
    (hpq : p ≠ q) (hpc : p ≠ c) (hqc : q ≠ c) :
    gm06CalibratedSectorFlag xs p q c r = 1 ↔
      CrossesOn (univ : Set Circle) (z p) (z q) (z r) (z c) := by
  have hm := calibratedSectorFlag_markers_ne_one xs hp hq hpq hpc hqc
  by_cases hpr : p = r
  · subst r
    simp only [hm.1, false_iff]
    simp [CrossesOn]
  by_cases hqr : q = r
  · subst r
    simp only [hm.2.1, false_iff]
    simp [CrossesOn]
  by_cases hrc : r = c
  · subst r
    simp only [hm.2.2, false_iff]
    simp [CrossesOn]
  exact calibratedSectorFlag_eq_one_iff_crossesOn xs z hz hs hp hq hr hc
    hpq hrc hpr hpc hqr hqc

end GraphMinor.GM06
