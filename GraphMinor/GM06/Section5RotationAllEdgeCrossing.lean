module

public import GraphMinor.GM06.Section5CalibratedRotationAllLabels
public import GraphMinor.GM06.Section5PolarRimCoordinates
import GraphMinor.GM06.Section5RotationEdgeCrossing

/-!
# Testing every active edge by its two directed labels

The marker cases of the calibrated flag agree with geometric
crossing too. Hence the two-end test in VI (5.7), page 133, applies
to every edge, including an edge containing the path marker.
No disjointness query is required as a preliminary input.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute
universe u

/-- Exact two-end rim labels turn the geometric crossing predicate
into the two finite flags, for edges meeting markers as well. -/
theorem exists_rim_crossing_iff_either_calibrated_end_all_edges
    {S : Type u} [TopologicalSpace S] (Φ : C(ClosedUnitDisc, S))
    (xs : List ℕ) (z : ℕ → Circle) (e : Set S) (edgeId : ℕ)
    (hz : Set.InjOn z {r | r ∈ xs})
    (hs : xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)))
    {p q c : ℕ} (hp : p ∈ xs) (hq : q ∈ xs) (hc : c ∈ xs)
    (hpq : p ≠ q) (hpc : p ≠ c) (hqc : q ≠ c)
    (hlabel : ∀ w : Circle, polarRimMap Φ w ∈ e ↔
      ∃ r ∈ xs, z r = w ∧ (r = 2 * edgeId ∨ r = 2 * edgeId + 1))
    :
    (∃ w : Circle, polarRimMap Φ w ∈ e ∧ CrossesOn (univ : Set Circle) (z p) (z q) w (z c)) ↔
      gm06CalibratedSectorFlag xs p q c (2 * edgeId) = 1 ∨
        gm06CalibratedSectorFlag xs p q c (2 * edgeId + 1) = 1 := by
  have htest (r : ℕ) (hr : r ∈ xs) :
      gm06CalibratedSectorFlag xs p q c r = 1 ↔
        CrossesOn (univ : Set Circle) (z p) (z q) (z r) (z c) :=
    calibratedSectorFlag_eq_one_iff_crossesOn_of_mem xs z hz hs hp hq hr hc hpq hpc hqc
  constructor
  · rintro ⟨w, hwe, hcross⟩
    obtain ⟨r, hr, hrw, hrId⟩ := (hlabel w).mp hwe
    have hre : polarRimMap Φ (z r) ∈ e := hrw.symm ▸ hwe
    have hflag := (htest r hr).mpr (hrw.symm ▸ hcross)
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
      exact ⟨z r, hre, (htest r hr).mp hflag⟩
    exact h.elim (hend _ (Or.inl rfl)) (hend _ (Or.inr rfl))


end GraphMinor.GM06
