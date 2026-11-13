module

public import GraphMinor.GM06.Section5LinkageStripCircle
public import GraphMinor.GM06.Section5RadialProjection
import GraphMinor.GM06.Section5LiftedDiscDisjoint
import GraphMinor.Surface.Gluing

/-!
# A lifted strip disc projects injectively

For the winding calculation of VI (5.1), page 129, a disc between
consecutive lifts has no overlap with any of its nonzero angular
translates when at least two linkage paths are present. Translation
by a whole angular period shifts its lift indices by k. The shifted
disc is separated from the original disc by another lift. Equal
angular projections differ by just such a translate, so they must
come from the same point.
-/

public section

namespace GraphMinor.GM06

open Set Real GraphMinor.Surface

/-- Translating by an integer angular period shifts the strip index
by that many full linkage periods. -/
theorem image_liftedStripBoundary_add_mul
    {k : ℕ} {G : Drawing ClosedCylinder} (hk : 0 < k)
    (L : CylinderLinkage k G) (m z : ℤ) :
    (fun p : ℝ × ℝ => (p.1, p.2 + (z : ℝ) * (2 * π))) '' liftedStripBoundary hk L m =
      liftedStripBoundary hk L (m + (k : ℤ) * z) := by
  let c : ℝ := (z : ℝ) * (2 * π)
  let f : (ℝ × ℝ) → (ℝ × ℝ) := fun p => (p.1, p.2 + c)
  have hcurve (n : ℤ) : f '' range (liftedLinkageCurve hk L n) =
      range (liftedLinkageCurve hk L (n + (k : ℤ) * z)) := by
    rw [← range_comp]
    apply congrArg range
    funext t
    exact (liftedLinkageCurve_add_mul hk L n z t).symm
  have hcuff (r a b : ℝ) : f '' (({r} : Set ℝ) ×ˢ Icc a b) =
      ({r} : Set ℝ) ×ˢ Icc (a + c) (b + c) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq.1, add_le_add_left hq.2.1 c, add_le_add_left hq.2.2 c⟩
    · intro hp
      refine ⟨(p.1, p.2 - c), ⟨hp.1, ?_, ?_⟩, ?_⟩
      · change a ≤ p.2 - c
        linarith only [hp.2.1]
      · change p.2 - c ≤ b
        linarith only [hp.2.2]
      · exact Prod.ext rfl (sub_add_cancel _ _)
  change f '' liftedStripBoundary hk L m = _
  rw [liftedStripBoundary, image_union, image_union, image_union,
    hcurve m, hcurve (m + 1), hcuff, hcuff]
  have hidx : (m + 1) + (k : ℤ) * z = (m + (k : ℤ) * z) + 1 := by omega
  rw [liftedStripBoundary, ← hidx]
  simp only [liftedLinkageCurve_add_mul, c]

/-- Angular projection is injective on the closed disc between two
consecutive linkage lifts when k ≥ 2. This provides disc coordinates
for the winding calculation in VI (5.1), page 129. -/
theorem injOn_radialCylinderProjection_stripDisc
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hk : 1 < k) (hθ : L.HasTheta θ) (m : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    InjOn radialCylinderProjection D := by
  intro p hp q hq heq
  have hr : p.1 = q.1 := by
    calc p.1 = (radialCylinderProjection p).1.1 := (radialCylinderProjection_fst (hstrip hp)).symm
         _ = (radialCylinderProjection q).1.1 := congrArg (fun x : ClosedCylinder => x.1.1) heq
         _ = q.1 := radialCylinderProjection_fst (hstrip hq)
  have ha : Circle.exp p.2 = Circle.exp q.2 := congrArg (fun x : ClosedCylinder => x.1.2) heq
  obtain ⟨z, hz⟩ := Circle.exp_eq_exp.mp ha
  by_cases hz0 : z = 0
  · apply Prod.ext hr
    simpa only [hz0, Int.cast_zero, zero_mul, add_zero] using hz
  let τ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := Homeomorph.addRight (0, (z : ℝ) * (2 * π))
  have hτ : (τ : (ℝ × ℝ) → (ℝ × ℝ)) =
      fun x => (x.1, x.2 + (z : ℝ) * (2 * π)) := by
    funext x
    exact Prod.ext (add_zero x.1) rfl
  have htrans := hD.image τ.continuous.continuousOn τ.symm.continuous.continuousOn
    (fun x _ => τ.symm_apply_apply x)
  have hBdE : discBd (τ '' D) = liftedStripBoundary hG.1 L (m + (k : ℤ) * z) := by
    rw [htrans.2, hBd, hτ]
    exact image_liftedStripBoundary_add_mul hG.1 L m z
  have hstripE : τ '' D ⊆ {x : ℝ × ℝ | 1 ≤ x.1 ∧ x.1 ≤ 2} := by
    rintro x ⟨y, hy, rfl⟩
    change 1 ≤ y.1 + 0 ∧ y.1 + 0 ≤ 2
    simpa only [add_zero, mem_ofPred_eq] using hstrip hy
  have hτq : τ q = p := by
    rw [hτ]
    exact Prod.ext hr.symm hz.symm
  have hpE : p ∈ τ '' D := ⟨q, hq, hτq⟩
  have hkZ : (2 : ℤ) ≤ (k : ℤ) := Int.ofNat_le.mpr hk
  have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg _
  have hgap : m + 1 < m + (k : ℤ) * z ∨ (m + (k : ℤ) * z) + 1 < m := by
    by_cases hzpos : 0 < z
    · have hprod : (k : ℤ) ≤ (k : ℤ) * z := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ z by omega) hk0
      exact Or.inl (by omega)
    · have hprod : (k : ℤ) * z ≤ -(k : ℤ) := by
        simpa only [mul_neg_one] using mul_le_mul_of_nonneg_left (show z ≤ (-1 : ℤ) by omega) hk0
      exact Or.inr (by omega)
  have hdis : Disjoint D (τ '' D) := by
    rcases hgap with hgap | hgap
    · exact disjoint_liftedStripDiscs_of_index_gap L hG hθ hgap hD htrans.1 hBd hBdE hstrip hstripE
    · exact (disjoint_liftedStripDiscs_of_index_gap L hG hθ hgap htrans.1 hD hBdE hBd hstripE hstrip).symm
  exact False.elim (disjoint_left.mp hdis hp hpE)

end GraphMinor.GM06
