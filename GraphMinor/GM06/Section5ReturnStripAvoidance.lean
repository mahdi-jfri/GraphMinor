module

public import GraphMinor.GM06.Section5LinkageStripCircle
import GraphMinor.GM06.Section5StripAvoidance
import GraphMinor.GM06.Section5StripEnds
import GraphMinor.GM06.Section5LiftedPaths
import GraphMinor.GM06.Section5

/-!
# The prescribed-side return misses the counted linkage lifts

In the one-path crossing count of VI (5.5), page 132, the return
from the last earlier vertex stays in the closed cut strip, then
moves on the initial cuff from the right initial copy to the
following dual point. Linkage lifts starting beyond that dual point
miss both parts. They miss the disc because their indices are not
its boundary indices. On the initial cuff a linkage lift meets only
its initial point, whose angle is already beyond the half gap.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

/-- The return strip and its following initial half gap miss all
linkage lifts with index at least three, in the one-path (5.5) count. -/
theorem disjoint_counted_lift_return_strip
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {n : ℤ} (hn : 3 ≤ n) :
    Disjoint (range (liftedLinkageCurve hG.1 L n))
      (D ∪ ({1} ×ˢ Icc (4 * π) (5 * π))) := by
  have hdis := disjoint_stripDisc_of_other_index L hG hθ
    (show n ≠ 1 by omega) (show n ≠ 1 + 1 by omega) hD hBd hstrip
  refine disjoint_left.mpr ?_
  rintro p ⟨u, hup⟩ (hpD | hpGap)
  · exact disjoint_left.mp hdis ⟨u, hup⟩ hpD
  · have hrad : (liftedLinkageCurve hG.1 L n u).1 = 1 :=
      (congrArg Prod.fst hup).trans (mem_singleton_iff.mp hpGap.1)
    have hu0 : u = 0 := eq_zero_of_strip_radius_one
      (liftedLinkageCurve_props_raw hG.1 L n).2.2.1
      (fun t ht => liftedLinkageCurve_interior_radius L hG n ht) hrad
    have hang : p.2 = 2 * (n : ℝ) * π := by
      rw [← hup, hu0]
      simpa only [Nat.cast_one, div_one] using
        (liftedLinkageCurve_props_raw hG.1 L n).2.2.2.1
    have hbound : 2 * (n : ℝ) * π ≤ 5 * π := hang ▸ hpGap.2.2
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith only [hbound, hnR, pi_pos]

/-- For any number of linkage paths, the return from strip m and
its following half gap misses every lift with index at least m + 2.
This is the common geometric exclusion for the count in VI (5.5). -/
theorem disjoint_counted_lift_return_strip_general
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ) (m : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {n : ℤ} (hn : m + 2 ≤ n) :
    Disjoint (range (liftedLinkageCurve hG.1 L n))
      (D ∪ ({1} ×ˢ Icc (2 * ((m : ℝ) + 1) * π / k)
        ((2 * ((m : ℝ) + 1) + 1) * π / k))) := by
  have hdis := disjoint_stripDisc_of_other_index L hG hθ
    (show n ≠ m by omega) (show n ≠ m + 1 by omega) hD hBd hstrip
  refine disjoint_left.mpr ?_
  rintro p ⟨u, hup⟩ (hpD | hpGap)
  · exact disjoint_left.mp hdis ⟨u, hup⟩ hpD
  · have hrad : (liftedLinkageCurve hG.1 L n u).1 = 1 :=
      (congrArg Prod.fst hup).trans (mem_singleton_iff.mp hpGap.1)
    have hu0 : u = 0 := eq_zero_of_strip_radius_one
      (liftedLinkageCurve_props_raw hG.1 L n).2.2.1
      (fun t ht => liftedLinkageCurve_interior_radius L hG n ht) hrad
    have hang : p.2 = 2 * (n : ℝ) * π / k := by
      rw [← hup, hu0]
      exact (liftedLinkageCurve_props_raw hG.1 L n).2.2.2.1
    have hbound : 2 * (n : ℝ) * π / k ≤ (2 * ((m : ℝ) + 1) + 1) * π / k :=
      hang ▸ hpGap.2.2
    have hscale : (0 : ℝ) < π / k := div_pos pi_pos (Nat.cast_pos.mpr hG.1)
    have hbound' : (2 * (n : ℝ)) * (π / k) ≤ (2 * ((m : ℝ) + 1) + 1) * (π / k) := by
      simpa only [mul_div_assoc] using hbound
    have hindex := (mul_le_mul_iff_left₀ hscale).mp hbound'
    have hnR : (m : ℝ) + 2 ≤ n := by exact_mod_cast hn
    linarith only [hindex, hnR]

end GraphMinor.GM06
