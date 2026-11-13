module

public import GraphMinor.GM06.Section5StripDisc
import GraphMinor.GM06.Section5StripEnds
import GraphMinor.Surface.PlaneDisc
import GraphMinor.Surface.PlaneOrientation
import GraphMinor.Surface.Gluing
import Mathlib.Topology.Connected.Basic

/-!
# Other linkage lifts stay outside a strip disc

For VI (5.1), page 129, the disc between two consecutive lifts
contains no other lifted path. The ends of every other lift lie
outside the boundary intervals. Such a lift misses the whole boundary
circle. Since it is connected and starts outside the disc, it stays
outside the disc.
-/

public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface

/-- Increasing an indexed lift increases the angles of both of its ends. -/
theorem liftedLinkageCurve_ends_lt_of_index_lt
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (hk : 0 < k)
    (L : CylinderLinkage k G) (hθ : L.HasTheta θ) {m n : ℤ} (hmn : m < n) :
    (liftedLinkageCurve hk L m 0).2 < (liftedLinkageCurve hk L n 0).2 ∧
      (liftedLinkageCurve hk L m 1).2 < (liftedLinkageCurve hk L n 1).2 := by
  have hstep : 2 * (m : ℝ) * π / (k : ℝ) < 2 * (n : ℝ) * π / (k : ℝ) := by
    apply (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hk)).mpr
    have hcast : (m : ℝ) < (n : ℝ) := Int.cast_lt.mpr hmn
    nlinarith only [pi_pos, hcast]
  have hm := liftedLinkageCurve_props hk L hθ m
  have hn := liftedLinkageCurve_props hk L hθ n
  constructor
  · rw [hm.2.2.2.1, hn.2.2.2.1]
    exact hstep
  · rw [hm.2.2.2.2.1, hn.2.2.2.2.1]
    linarith only [hstep]

/-- Every lift other than the two defining lifts misses the strip
boundary circle. -/
theorem disjoint_liftedStripBoundary_of_other_index
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) {m n : ℤ} (hnm : n ≠ m) (hnm1 : n ≠ m + 1) :
    Disjoint (range (liftedLinkageCurve hG.1 L n)) (liftedStripBoundary hG.1 L m) := by
  have hn := liftedLinkageCurve_props_raw hG.1 L n
  have hmid := fun (t : unitInterval) (ht : t ∈ Ioo 0 1) =>
    liftedLinkageCurve_interior_radius L hG n ht
  have hindex : n < m ∨ m + 1 < n := by omega
  apply disjoint_left.mpr
  rintro p ⟨t, rfl⟩ hp
  rcases hp with ((hp | hp) | hp) | hp
  · exact disjoint_left.mp (disjoint_range_liftedLinkageCurve hG.1 L hnm)
      (mem_range_self t) hp
  · exact disjoint_left.mp (disjoint_range_liftedLinkageCurve hG.1 L hnm1)
      (mem_range_self t) hp
  · have ht := eq_zero_of_strip_radius_one hn.2.2.1 hmid (mem_singleton_iff.mp hp.1)
    subst t
    rcases hindex with hlt | hlt
    · exact (not_lt_of_ge hp.2.1) (liftedLinkageCurve_ends_lt_of_index_lt hG.1 L hθ hlt).1
    · exact (not_lt_of_ge hp.2.2) (liftedLinkageCurve_ends_lt_of_index_lt hG.1 L hθ hlt).1
  · have ht := eq_one_of_strip_radius_two hn.2.1 hmid (mem_singleton_iff.mp hp.1)
    subst t
    rcases hindex with hlt | hlt
    · exact (not_lt_of_ge hp.2.1) (liftedLinkageCurve_ends_lt_of_index_lt hG.1 L hθ hlt).2
    · exact (not_lt_of_ge hp.2.2) (liftedLinkageCurve_ends_lt_of_index_lt hG.1 L hθ hlt).2

private theorem connected_set_outside_disc
    {D K : Set (ℝ × ℝ)} (hD : IsClosedDisc D) (hK : IsPreconnected K)
    (hbd : Disjoint K (discBd D)) {p : ℝ × ℝ} (hp : p ∈ K) (hpD : p ∉ D) :
    Disjoint K D := by
  let e : ℂ ≃ₜ ℝ × ℝ := Complex.equivRealProdCLM.toHomeomorph
  have hman (q : ℝ × ℝ) : IsManifoldPoint q := by
    have h := isManifoldPoint_of_isOpenEmbedding e.isOpenEmbedding
      (isManifoldPoint_complex (e.symm q))
    simpa only [e.apply_symm_apply] using h
  rcases hD.side hman hK hbd with hin | hout
  · exact False.elim (hpD (hin hp).1)
  · exact hout

/-- Other linkage lifts stay outside the disc enclosed by two
consecutive lifts. -/
theorem disjoint_stripDisc_of_other_index
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) {m n : ℤ} (hnm : n ≠ m) (hnm1 : n ≠ m + 1)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    Disjoint (range (liftedLinkageCurve hG.1 L n)) D := by
  have havoid := disjoint_liftedStripBoundary_of_other_index L hG hθ hnm hnm1
  have hbd : Disjoint (range (liftedLinkageCurve hG.1 L n)) (discBd D) := by
    rw [hBd]
    exact havoid
  have hpD : liftedLinkageCurve hG.1 L n 0 ∉ D := by
    intro hp
    have hpbd : liftedLinkageCurve hG.1 L n 0 ∉ discBd D :=
      fun h => disjoint_left.mp hbd (mem_range_self 0) h
    have hstrict := (discInt_subset_open_radial_strip hD hstrip ⟨hp, hpbd⟩).1
    rw [(liftedLinkageCurve_props_raw hG.1 L n).2.1] at hstrict
    exact lt_irrefl _ hstrict
  exact connected_set_outside_disc hD
    (isPreconnected_range (liftedLinkageCurve hG.1 L n).continuous) hbd (mem_range_self 0) hpD

end GraphMinor.GM06
