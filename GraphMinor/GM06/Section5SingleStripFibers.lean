module

public import GraphMinor.GM06.Section5StripInjective
import GraphMinor.GM06.Section5AdjacentStripDiscs
import GraphMinor.GM06.Section5LiftedDiscDisjoint
import GraphMinor.Surface.Gluing
import Mathlib.Tactic

/-!
# Identifications on a single lifted linkage strip

For the contraction in VI Reduction 3, page 129, a single linkage
path cuts the cylinder into one lifted strip disc. Angular projection
identifies exactly matching points of its two boundary lifts. A
larger angular shift would put two non-adjacent strip discs together,
which is excluded by their disjointness. A shift by one period gives
the shared path of two adjacent discs.
-/

public section

namespace GraphMinor.GM06

open Set Real GraphMinor.Surface

private theorem single_strip_fibers_of_snd_le
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ) (m : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {p q : ℝ × ℝ} (hp : p ∈ D) (hq : q ∈ D) (hpq : q.2 ≤ p.2)
    (heq : radialCylinderProjection p = radialCylinderProjection q) :
    p = q ∨ ∃ t : unitInterval,
      p = liftedLinkageCurve hG.1 L (m + 1) t ∧ q = liftedLinkageCurve hG.1 L m t := by
  have hr : p.1 = q.1 := by
    calc p.1 = (radialCylinderProjection p).1.1 := (radialCylinderProjection_fst (hstrip hp)).symm
         _ = (radialCylinderProjection q).1.1 := congrArg (fun x : ClosedCylinder => x.1.1) heq
         _ = q.1 := radialCylinderProjection_fst (hstrip hq)
  have ha : Circle.exp p.2 = Circle.exp q.2 := congrArg (fun x : ClosedCylinder => x.1.2) heq
  obtain ⟨z, hz⟩ := Circle.exp_eq_exp.mp ha
  have hznonneg : (0 : ℤ) ≤ z := by
    have hh : (0 : ℝ) ≤ (z : ℝ) := by nlinarith only [hz, hpq, pi_pos]
    exact_mod_cast hh
  by_cases hz0 : z = 0
  · apply Or.inl
    apply Prod.ext hr
    simpa only [hz0, Int.cast_zero, zero_mul, add_zero] using hz
  let τ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := Homeomorph.addRight (0, (z : ℝ) * (2 * π))
  have hτ : (τ : (ℝ × ℝ) → (ℝ × ℝ)) =
      fun x => (x.1, x.2 + (z : ℝ) * (2 * π)) := by
    funext x
    exact Prod.ext (add_zero x.1) rfl
  have htrans := hD.image τ.continuous.continuousOn τ.symm.continuous.continuousOn
    (fun x _ => τ.symm_apply_apply x)
  have hBdE : discBd (τ '' D) = liftedStripBoundary hG.1 L (m + z) := by
    rw [htrans.2, hBd, hτ]
    simpa only [Nat.cast_one, one_mul] using image_liftedStripBoundary_add_mul hG.1 L m z
  have hstripE : τ '' D ⊆ {x : ℝ × ℝ | 1 ≤ x.1 ∧ x.1 ≤ 2} := by
    rintro x ⟨y, hy, rfl⟩
    change 1 ≤ y.1 + 0 ∧ y.1 + 0 ≤ 2
    simpa only [add_zero, mem_ofPred_eq] using hstrip hy
  have hτq : τ q = p := by
    rw [hτ]
    exact Prod.ext hr.symm hz.symm
  have hpE : p ∈ τ '' D := ⟨q, hq, hτq⟩
  have hz1 : z = 1 := by
    by_contra hn
    have hgap : m + 1 < m + z := by omega
    have hdis := disjoint_liftedStripDiscs_of_index_gap L hG hθ hgap
      hD htrans.1 hBd hBdE hstrip hstripE
    exact disjoint_left.mp hdis hp hpE
  subst z
  have hcommon := inter_adjacent_liftedStripDiscs L hG hθ m hD htrans.1 hBd hBdE hstrip hstripE
  have hpCommon : p ∈ range (liftedLinkageCurve hG.1 L (m + 1)) := hcommon ▸ ⟨hp, hpE⟩
  obtain ⟨t, ht⟩ := hpCommon
  have hτcurve : τ (liftedLinkageCurve hG.1 L m t) = liftedLinkageCurve hG.1 L (m + 1) t := by
    rw [hτ]
    simpa only [Nat.cast_one, Int.cast_one, one_mul, mul_one] using
      (liftedLinkageCurve_add_mul hG.1 L m (1 : ℤ) t).symm
  have hqeq : q = liftedLinkageCurve hG.1 L m t :=
    τ.injective (hτq.trans (ht.symm.trans hτcurve.symm))
  exact Or.inr ⟨t, ht.symm, hqeq⟩

/-- On the one-path strip disc, projection identifies only equal
points or corresponding points on the two boundary lifts. -/
theorem radialCylinderProjection_single_strip_fibers
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ) (m : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {p q : ℝ × ℝ} (hp : p ∈ D) (hq : q ∈ D)
    (heq : radialCylinderProjection p = radialCylinderProjection q) :
    p = q ∨ ∃ t : unitInterval,
      (p = liftedLinkageCurve hG.1 L (m + 1) t ∧ q = liftedLinkageCurve hG.1 L m t) ∨
      (q = liftedLinkageCurve hG.1 L (m + 1) t ∧ p = liftedLinkageCurve hG.1 L m t) := by
  by_cases hpq : q.2 ≤ p.2
  · rcases single_strip_fibers_of_snd_le L hG hθ m hD hBd hstrip hp hq hpq heq with h | ⟨t, ht⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, Or.inl ht⟩
  · rcases single_strip_fibers_of_snd_le L hG hθ m hD hBd hstrip hq hp
      (not_le.mp hpq).le heq.symm with h | ⟨t, ht⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨t, Or.inr ht⟩

end GraphMinor.GM06
