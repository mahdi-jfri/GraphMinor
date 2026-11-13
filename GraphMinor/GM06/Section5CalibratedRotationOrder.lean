module

public import GraphMinor.GM06.Section5RotationCircleOrder
public import GraphMinor.Compute.GM06SectorMarkers

/-!
# The calibrated finite sector has the geometric crossing order

For VI (5.7), page 133, calibration puts the outside cuff marker
outside the selected row interval. The sorted-row crossing lemma
then applies. If calibration swapped the two boundary markers,
crossing order is unchanged because the first pair is unordered.
Thus the finite flag works with either rotation orientation.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.Compute

/-- The calibrated finite sector flag computes the geometric rim
crossing test without an assumption about which marker lies outside. -/
theorem calibratedSectorFlag_eq_one_iff_crossesOn
    (xs : List ℕ) (z : ℕ → Circle)
    (hz : Set.InjOn z {a | a ∈ xs})
    (hs : xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)))
    {p q r c : ℕ} (hp : p ∈ xs) (hq : q ∈ xs) (hr : r ∈ xs) (hc : c ∈ xs)
    (hpq : p ≠ q) (hrc : r ≠ c) (hpr : p ≠ r) (hpc : p ≠ c)
    (hqr : q ≠ r) (hqc : q ≠ c) :
    gm06CalibratedSectorFlag xs p q c r = 1 ↔
      CrossesOn (univ : Set Circle) (z p) (z q) (z r) (z c) := by
  have hout := gm06SectorMarkers_outside xs hp hq hpq hpc hqc
  rcases gm06SectorMarkers_cases xs p q c with hkeep | hflip
  · unfold gm06CalibratedSectorFlag
    rw [hkeep]
    rw [hkeep] at hout
    exact rotationSectorFlag_eq_one_iff_crossesOn xs z hz hs hp hq hr hc
      hpq hrc hpr hpc hqr hqc hout
  · unfold gm06CalibratedSectorFlag
    rw [hflip]
    rw [hflip] at hout
    have hrot := rotationSectorFlag_eq_one_iff_crossesOn xs z hz hs hq hp hr hc
      hpq.symm hrc hqr hqc hpr hpc hout
    apply hrot.trans
    rw [crossesOn_univ_iff_circleStdCoord, crossesOn_univ_iff_circleStdCoord]
    exact (circleCrosses_symm_left circleStdCoord (z p) (z q) (z r) (z c)).symm

end GraphMinor.GM06
