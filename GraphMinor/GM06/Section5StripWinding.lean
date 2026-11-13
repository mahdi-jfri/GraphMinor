module

public import GraphMinor.GM06.Section5StripInjective
import GraphMinor.GM06.Section4Winding
import GraphMinor.Surface.Gluing

/-!
# Winding across a linkage strip

For VI (5.1), page 129, angular projection identifies a closed lifted
strip disc with its image when k ≥ 2. Its inverse lifts every curve
in that image continuously. If the curve starts at the first lift's
initial vertex and ends at the next lift's terminal vertex, its
angular displacement is the old winding plus one initial gap. This
gives the required increment 1/k.
-/

public section

namespace GraphMinor.GM06

open Set Real GraphMinor.Surface

/-- A curve in a projected strip disc, from the first initial vertex
to the next terminal vertex, has winding θ + 1/k. This is the winding
calculation in VI (5.1), page 129. Its lift is constructed using the
inverse of the injective projection of the compact disc. -/
theorem windingNumber_eq_next_of_range_subset_stripDisc
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hk : 1 < k) (hθ : L.HasTheta θ) (m : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (f : Curve ClosedCylinder) (hf : range f ⊆ radialCylinderProjection '' D)
    (hf0 : f 0 = radialCylinderProjection (liftedLinkageCurve hG.1 L m 0))
    (hf1 : f 1 = radialCylinderProjection (liftedLinkageCurve hG.1 L (m + 1) 1)) :
    windingNumber f = θ + 1 / (k : ℝ) := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  have hinj := injOn_radialCylinderProjection_stripDisc L hG hk hθ m hD hBd hstrip
  let πD : D → ClosedCylinder := fun p => radialCylinderProjection p.1
  have hπc : Continuous πD := continuous_radialCylinderProjection.comp continuous_subtype_val
  have hπi : Function.Injective πD := fun p q h => Subtype.ext (hinj p.2 q.2 h)
  let e : D ≃ₜ range πD := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective πD hπi) hπc.rangeFactorization
  have hfRange (u : unitInterval) : f u ∈ range πD := by
    obtain ⟨p, hp, hpmap⟩ := hf (mem_range_self u)
    exact ⟨⟨p, hp⟩, hpmap⟩
  let γ : C(unitInterval, ℝ × ℝ) :=
    ⟨fun u => (e.symm ⟨f u, hfRange u⟩).1,
      continuous_subtype_val.comp (e.symm.continuous.comp (f.continuous.subtype_mk hfRange))⟩
  have hγD (u : unitInterval) : γ u ∈ D := (e.symm ⟨f u, hfRange u⟩).2
  have hγproj (u : unitInterval) : radialCylinderProjection (γ u) = f u :=
    congrArg Subtype.val (e.apply_symm_apply ⟨f u, hfRange u⟩)
  have hp0 : liftedLinkageCurve hG.1 L m 0 ∈ D := by
    apply discBd_subset D
    rw [hBd]
    exact Or.inl (Or.inl (Or.inl (mem_range_self 0)))
  have hp1 : liftedLinkageCurve hG.1 L (m + 1) 1 ∈ D := by
    apply discBd_subset D
    rw [hBd]
    exact Or.inl (Or.inl (Or.inr (mem_range_self 1)))
  have hγ0 : γ 0 = liftedLinkageCurve hG.1 L m 0 :=
    hinj (hγD 0) hp0 ((hγproj 0).trans hf0)
  have hγ1 : γ 1 = liftedLinkageCurve hG.1 L (m + 1) 1 :=
    hinj (hγD 1) hp1 ((hγproj 1).trans hf1)
  let a : C(unitInterval, ℝ) := ⟨fun u => (γ u).2, continuous_snd.comp γ.continuous⟩
  have ha (u : unitInterval) : Circle.exp (a u) = (f u).1.2 :=
    congrArg (fun x : ClosedCylinder => x.1.2) (hγproj u)
  rw [windingNumber_eq_of_exp_lift a ha]
  change ((γ 1).2 - (γ 0).2) / (2 * π) = θ + 1 / (k : ℝ)
  rw [hγ1, hγ0, (liftedLinkageCurve_props hG.1 L hθ (m + 1)).2.2.2.2.1,
    (liftedLinkageCurve_props hG.1 L hθ m).2.2.2.1]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hG.1.ne', pi_ne_zero]
  ring

end GraphMinor.GM06
