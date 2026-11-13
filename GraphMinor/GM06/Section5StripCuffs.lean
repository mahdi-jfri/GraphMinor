module

public import GraphMinor.GM06.Section5StripImage
public import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5StripEnds

/-!
# Cuff intervals in a lifted strip disc

In VI (5.1), page 129, the region boundary can use only the cuff
intervals bounding its strip. A point of the lifted closed disc on
a cuff line is on the disc boundary, by the strict interior radius
bounds. On that line the two lifted paths meet only at their ends.
Thus the point lies in the stated angular interval.
-/

public section

namespace GraphMinor.GM06

open Set Real GraphMinor.Surface

/-- The lifted strip disc meets its initial radial line only in the
interval between its two initial endpoints. -/
theorem stripDisc_radius_one_mem_interval
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {p : ℝ × ℝ} (hp : p ∈ D) (hp1 : p.1 = 1) :
    p.2 ∈ Icc (liftedLinkageCurve hG.1 L m 0).2
      (liftedLinkageCurve hG.1 L (m + 1) 0).2 := by
  have hpbd : p ∈ discBd D := by
    by_contra hn
    have hh := (discInt_subset_open_radial_strip hD hstrip ⟨hp, hn⟩).1
    rw [hp1] at hh
    exact lt_irrefl _ hh
  rw [hBd] at hpbd
  have hm := liftedLinkageCurve_props_raw hG.1 L m
  have hn := liftedLinkageCurve_props_raw hG.1 L (m + 1)
  have horder := (liftedLinkageCurve_consecutive_ends hG.1 L hθ m).1
  rcases hpbd with ((hpbd | hpbd) | hpbd) | hpbd
  · obtain ⟨t, rfl⟩ := hpbd
    have ht := eq_zero_of_strip_radius_one hm.2.2.1
      (fun t ht => liftedLinkageCurve_interior_radius L hG m ht) hp1
    rw [ht]
    exact ⟨le_rfl, horder.le⟩
  · obtain ⟨t, rfl⟩ := hpbd
    have ht := eq_zero_of_strip_radius_one hn.2.2.1
      (fun t ht => liftedLinkageCurve_interior_radius L hG (m + 1) ht) hp1
    rw [ht]
    exact ⟨horder.le, le_rfl⟩
  · exact hpbd.2
  · have hh : p.1 = 2 := mem_singleton_iff.mp hpbd.1
    rw [hp1] at hh
    norm_num at hh

/-- The lifted strip disc meets its terminal radial line only in the
interval between its two terminal endpoints. -/
theorem stripDisc_radius_two_mem_interval
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {p : ℝ × ℝ} (hp : p ∈ D) (hp2 : p.1 = 2) :
    p.2 ∈ Icc (liftedLinkageCurve hG.1 L m 1).2
      (liftedLinkageCurve hG.1 L (m + 1) 1).2 := by
  have hpbd : p ∈ discBd D := by
    by_contra hn
    have hh := (discInt_subset_open_radial_strip hD hstrip ⟨hp, hn⟩).2
    rw [hp2] at hh
    exact lt_irrefl _ hh
  rw [hBd] at hpbd
  have hm := liftedLinkageCurve_props_raw hG.1 L m
  have hn := liftedLinkageCurve_props_raw hG.1 L (m + 1)
  have horder := (liftedLinkageCurve_consecutive_ends hG.1 L hθ m).2
  rcases hpbd with ((hpbd | hpbd) | hpbd) | hpbd
  · obtain ⟨t, rfl⟩ := hpbd
    have ht := eq_one_of_strip_radius_two hm.2.1
      (fun t ht => liftedLinkageCurve_interior_radius L hG m ht) hp2
    rw [ht]
    exact ⟨le_rfl, horder.le⟩
  · obtain ⟨t, rfl⟩ := hpbd
    have ht := eq_one_of_strip_radius_two hn.2.1
      (fun t ht => liftedLinkageCurve_interior_radius L hG (m + 1) ht) hp2
    rw [ht]
    exact ⟨horder.le, le_rfl⟩
  · have hh : p.1 = 1 := mem_singleton_iff.mp hpbd.1
    rw [hp2] at hh
    norm_num at hh
  · exact hpbd.2

/-- The initial cuff meets the closure of Σᵢ only along the closed
angular gap from sᵢ to sᵢ₊₁. -/
theorem closure_strip_inter_initial_cuff_subset_gap
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (i : Fin k) :
    closure (cylinderStrip L i) ∩ cylinderCuff1 ⊆ range (initialCuffGapCurve k i) := by
  let m : ℤ := (i.val : ℤ) + 1
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ m
  have him := image_stripDisc_eq_closure_strip L hG hθ i hD hBd hstrip
  rintro x ⟨hx, hx1⟩
  obtain ⟨p, hp, rfl⟩ := him.symm ▸ hx
  have hp1 : p.1 = 1 := (radialCylinderProjection_fst (hstrip hp)).symm.trans hx1
  have hang := stripDisc_radius_one_mem_interval L hG hθ m hD hBd hstrip hp hp1
  rw [(liftedLinkageCurve_props_raw hG.1 L m).2.2.2.1,
    (liftedLinkageCurve_props_raw hG.1 L (m + 1)).2.2.2.1] at hang
  let a : ℝ := 2 * ((i.val + 1 : ℕ) : ℝ) * π / k
  let d : ℝ := 2 * π / k
  have hd : 0 < d := div_pos (mul_pos two_pos pi_pos) (Nat.cast_pos.mpr hG.1)
  have ha : a ≤ p.2 ∧ p.2 ≤ a + d := by
    dsimp [a, d, m] at hang ⊢
    push_cast at hang ⊢
    constructor
    · exact hang.1
    · convert hang.2 using 1
      ring
  let t : unitInterval := ⟨(p.2 - a) / d,
    div_nonneg (sub_nonneg.mpr ha.1) hd.le,
    (div_le_one₀ hd).mpr (by linarith only [ha.2])⟩
  refine ⟨t, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change 1 = (radialCylinderProjection p).1.1
    rw [radialCylinderProjection_fst (hstrip hp), hp1]
  · change Circle.exp (2 * (((i.val + 1 : ℕ) : ℝ) + (t : ℝ)) * π / k) = Circle.exp p.2
    congr 1
    calc
      2 * (((i.val + 1 : ℕ) : ℝ) + (t : ℝ)) * π / k = a + d * (t : ℝ) := by
        dsimp [a, d]
        ring
      _ = a + (p.2 - a) := by
        change a + d * ((p.2 - a) / d) = a + (p.2 - a)
        rw [mul_div_cancel₀ _ hd.ne']
      _ = p.2 := add_sub_cancel _ _

end GraphMinor.GM06
