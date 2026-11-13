module

public import GraphMinor.GM06.Section5LiftedPaths
import GraphMinor.GM06.Section5StripCircle

/-!
# The boundary circle between consecutive linkage lifts

The strip Σᵢ in VI Section 5, pages 128–129, lies between two
consecutive linkage paths. In the angular cover its boundary consists
of their lifts and the intervals joining their ends on the radial
lines. Properness, disjointness, and the order of the lifted ends
show that this boundary is a circle.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- The four pieces bounding the strip between consecutive indexed
lifts of the linkage paths. -/
@[expose] def liftedStripBoundary
    {k : ℕ} {G : Drawing ClosedCylinder} (hk : 0 < k)
    (L : CylinderLinkage k G) (m : ℤ) : Set (ℝ × ℝ) :=
  range (liftedLinkageCurve hk L m) ∪ range (liftedLinkageCurve hk L (m + 1)) ∪
    (({1} : Set ℝ) ×ˢ Icc (liftedLinkageCurve hk L m 0).2 (liftedLinkageCurve hk L (m + 1) 0).2) ∪
    (({2} : Set ℝ) ×ˢ Icc (liftedLinkageCurve hk L m 1).2 (liftedLinkageCurve hk L (m + 1) 1).2)

/-- Consecutive linkage lifts and their two boundary intervals form
a circle in the strip argument of VI (5.1), page 129. -/
theorem isOArc_liftedStripBoundary
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m : ℤ) : IsOArc (liftedStripBoundary hG.1 L m) := by
  have hm := liftedLinkageCurve_props_raw hG.1 L m
  have hn := liftedLinkageCurve_props_raw hG.1 L (m + 1)
  have horder := liftedLinkageCurve_consecutive_ends hG.1 L hθ m
  exact isOArc_of_two_proper_strip_arcs _ _
    (isArcMap_liftedLinkageCurve hG.1 L m) (isArcMap_liftedLinkageCurve hG.1 L (m + 1))
    hm.2.1 hn.2.1 hm.2.2.1 hn.2.2.1
    (fun t ht => liftedLinkageCurve_interior_radius L hG m ht)
    (fun t ht => liftedLinkageCurve_interior_radius L hG (m + 1) ht)
    (disjoint_range_liftedLinkageCurve hG.1 L (by omega)) horder.1 horder.2

/-- The lifted strip boundary lies between the two radial lines. -/
theorem liftedStripBoundary_subset_radial_strip
    {k : ℕ} {G : Drawing ClosedCylinder} (hk : 0 < k)
    (L : CylinderLinkage k G) (m : ℤ) :
    liftedStripBoundary hk L m ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2} := by
  intro p hp
  change 1 ≤ p.1 ∧ p.1 ≤ 2
  rcases hp with ((hp | hp) | hp) | hp
  · obtain ⟨t, rfl⟩ := hp
    exact (liftedLinkageCurve_props_raw hk L m).1 t
  · obtain ⟨t, rfl⟩ := hp
    exact (liftedLinkageCurve_props_raw hk L (m + 1)).1 t
  · have hp1 : p.1 = 1 := mem_singleton_iff.mp hp.1
    rw [hp1]
    exact ⟨le_rfl, by norm_num⟩
  · have hp2 : p.1 = 2 := mem_singleton_iff.mp hp.1
    rw [hp2]
    exact ⟨by norm_num, le_rfl⟩

end GraphMinor.GM06
