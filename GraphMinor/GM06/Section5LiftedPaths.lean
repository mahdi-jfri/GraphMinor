module

public import GraphMinor.GM06.Section5
public import GraphMinor.Surface.CrossCut
import GraphMinor.GM06.Section5ProperPaths

/-!
# Proper, disjoint lifted linkage paths

For the strip argument in VI (5.1), page 129, lift the linkage paths
to the radial-angular strip. A lifted curve is injective because its
projection is injective. Distinct indexed lifts are disjoint, and
interior parameters have radius strictly between 1 and 2. Consecutive
lifts have their ends in the same strict order on both radial lines.
-/

public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface

/-- Every lifted linkage curve is an injective arc. -/
theorem isArcMap_liftedLinkageCurve
    {k : ℕ} {G : Drawing ClosedCylinder} (hk : 0 < k)
    (L : CylinderLinkage k G) (m : ℤ) : IsArcMap (liftedLinkageCurve hk L m) := by
  refine ⟨(liftedLinkageCurve hk L m).continuous, ?_⟩
  intro s t hst
  let i := modIdx k hk m
  have hr : (L.curve i s).1.1 = (L.curve i t).1.1 := by
    simpa only [liftedLinkageCurve_fst] using congrArg Prod.fst hst
  have he := (liftedLinkageCurve_props_raw hk L m).2.2.2.2.2
  have hangle : (L.curve i s).1.2 = (L.curve i t).1.2 :=
    (he s).symm.trans ((congrArg Circle.exp (congrArg Prod.snd hst)).trans (he t))
  apply (L.curve_parametrizes i).1
  exact Subtype.ext (Prod.ext hr hangle)

/-- Distinct indexed lifts have disjoint images, including lifts of
the same path in different angular periods. -/
theorem disjoint_range_liftedLinkageCurve
    {k : ℕ} {G : Drawing ClosedCylinder} (hk : 0 < k)
    (L : CylinderLinkage k G) {m n : ℤ} (hmn : m ≠ n) :
    Disjoint (range (liftedLinkageCurve hk L m)) (range (liftedLinkageCurve hk L n)) := by
  apply disjoint_left.mpr
  rintro x ⟨s, hs⟩ ⟨t, ht⟩
  exact hmn (eq_of_liftedLinkageCurve_eq_raw hk L (hs.trans ht.symm))

/-- Interior parameters of a lifted path lie strictly between the
two radial boundary lines. -/
theorem liftedLinkageCurve_interior_radius
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (m : ℤ) {t : unitInterval} (ht : t ∈ Ioo 0 1) :
    1 < (liftedLinkageCurve hG.1 L m t).1 ∧ (liftedLinkageCurve hG.1 L m t).1 < 2 := by
  rw [liftedLinkageCurve_fst]
  exact L.radius_curve_interior hG _ ht

/-- Consecutive lifts are strictly ordered at both ends when all
linkage paths have the stated winding number. -/
theorem liftedLinkageCurve_consecutive_ends
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (hk : 0 < k)
    (L : CylinderLinkage k G) (hθ : L.HasTheta θ) (m : ℤ) :
    (liftedLinkageCurve hk L m 0).2 < (liftedLinkageCurve hk L (m + 1) 0).2 ∧
      (liftedLinkageCurve hk L m 1).2 < (liftedLinkageCurve hk L (m + 1) 1).2 := by
  have hstep : 2 * (m : ℝ) * π / (k : ℝ) < 2 * ((m + 1 : ℤ) : ℝ) * π / (k : ℝ) := by
    apply (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hk)).mpr
    push_cast
    nlinarith only [pi_pos]
  have hm := liftedLinkageCurve_props hk L hθ m
  have hn := liftedLinkageCurve_props hk L hθ (m + 1)
  constructor
  · rw [hm.2.2.2.1, hn.2.2.2.1]
    exact hstep
  · rw [hm.2.2.2.2.1, hn.2.2.2.2.1]
    linarith only [hstep]

end GraphMinor.GM06
