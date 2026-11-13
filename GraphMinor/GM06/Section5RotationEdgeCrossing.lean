module

public import GraphMinor.GM06.Section5CalibratedRotationOrder
public import GraphMinor.GM06.Section5PolarRimCoordinates

/-!
# Reading an edge crossing test from its two directed labels

The edge scan for VI (5.7), page 133, queries both directed ends.
A rotation row labels every edge direction exactly by one of those
ends. If an edge misses the three barrier markers, each present
end has four distinct points in the crossing test. The calibrated
finite flag then gives exactly the geometric edge test. A loop's
two ends are tested separately.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute
universe u

/-- A positive calibrated sector flag always names a label in the row. -/
theorem mem_of_calibratedSectorFlag_eq_one (xs : List ℕ) (p q c r : ℕ)
    (h : gm06CalibratedSectorFlag xs p q c r = 1) : r ∈ xs := by
  unfold gm06CalibratedSectorFlag at h
  exact (gm06RotationSectorFlag_eq_one _ _ _ _).mp h |>.1

/-- The two finite dart tests are exactly the rim crossing test for
an edge disjoint from the three markers. -/
theorem exists_rim_crossing_iff_either_calibrated_end
    {S : Type u} [TopologicalSpace S] (Φ : C(ClosedUnitDisc, S))
    (xs : List ℕ) (z : ℕ → Circle) (e : Set S) (edgeId : ℕ)
    (hz : Set.InjOn z {r | r ∈ xs})
    (hs : xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)))
    {p q c : ℕ} (hp : p ∈ xs) (hq : q ∈ xs) (hc : c ∈ xs)
    (hpq : p ≠ q) (hpc : p ≠ c) (hqc : q ≠ c)
    (hlabel : ∀ w : Circle, polarRimMap Φ w ∈ e ↔
      ∃ r ∈ xs, z r = w ∧ (r = 2 * edgeId ∨ r = 2 * edgeId + 1))
    (hpe : polarRimMap Φ (z p) ∉ e) (hqe : polarRimMap Φ (z q) ∉ e)
    (hce : polarRimMap Φ (z c) ∉ e) :
    (∃ w : Circle, polarRimMap Φ w ∈ e ∧ CrossesOn (univ : Set Circle) (z p) (z q) w (z c)) ↔
      gm06CalibratedSectorFlag xs p q c (2 * edgeId) = 1 ∨
        gm06CalibratedSectorFlag xs p q c (2 * edgeId + 1) = 1 := by
  have htest (r : ℕ) (hr : r ∈ xs) (hre : polarRimMap Φ (z r) ∈ e) :
      gm06CalibratedSectorFlag xs p q c r = 1 ↔
        CrossesOn (univ : Set Circle) (z p) (z q) (z r) (z c) := by
    have hpr : p ≠ r := fun h => hpe (h.symm ▸ hre)
    have hqr : q ≠ r := fun h => hqe (h.symm ▸ hre)
    have hrc : r ≠ c := fun h => hce (h ▸ hre)
    exact calibratedSectorFlag_eq_one_iff_crossesOn xs z hz hs hp hq hr hc
      hpq hrc hpr hpc hqr hqc
  constructor
  · rintro ⟨w, hwe, hcross⟩
    obtain ⟨r, hr, hrw, hrId⟩ := (hlabel w).mp hwe
    have hre : polarRimMap Φ (z r) ∈ e := hrw.symm ▸ hwe
    have hflag := (htest r hr hre).mpr (hrw.symm ▸ hcross)
    rcases hrId with h | h
    · exact Or.inl (h ▸ hflag)
    · exact Or.inr (h ▸ hflag)
  · intro h
    have hend (r : ℕ) (hrId : r = 2 * edgeId ∨ r = 2 * edgeId + 1)
        (hflag : gm06CalibratedSectorFlag xs p q c r = 1) :
        ∃ w : Circle, polarRimMap Φ w ∈ e ∧
          CrossesOn (univ : Set Circle) (z p) (z q) w (z c) := by
      have hr := mem_of_calibratedSectorFlag_eq_one xs p q c r hflag
      have hre := (hlabel (z r)).mpr ⟨r, hr, rfl, hrId⟩
      exact ⟨z r, hre, (htest r hr hre).mp hflag⟩
    exact h.elim (hend _ (Or.inl rfl)) (hend _ (Or.inr rfl))

end GraphMinor.GM06
