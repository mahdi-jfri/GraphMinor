module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4Winding
import GraphMinor.GM06.Section5StripWinding
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5StripBoundary

/-!
# Winding from a dual point to the left terminal

Lift a curve in the closed linkage strip using its injective projection.
The initial angle is the midpoint of the initial gap, and the terminal
angle lies on the left linkage lift.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface
/-- The access curve in VI (5.3), pages 132–133, has winding θ − 1/(2k)
when at least two paths make the closed strip project injectively. -/
theorem windingNumber_region_access {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hk : 1 < k) (hθ : L.HasTheta θ) (i : Fin k)
    (f : Curve ClosedCylinder) (hfcl : range f ⊆ closure (cylinderStrip L i))
    (hfstart : f 0 = cylinderN1Point k i) (hfend : f 1 = L.curve i 1) :
    windingNumber f = θ - (2 * (k : ℝ))⁻¹ := by
  let m : ℤ := (i.val : ℤ) + 1
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ m
  have him := image_stripDisc_eq_closure_strip L hG hθ i hD hBd hstrip
  have hf : range f ⊆ radialCylinderProjection '' D := him.symm ▸ hfcl
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

  let p : ℝ × ℝ := (1, (2 * (m : ℝ) + 1) * π / k)
  have hp0 : p ∈ D := by
    apply discBd_subset D
    rw [hBd]
    apply Or.inl ∘ Or.inr
    refine ⟨rfl, ?_, ?_⟩
    · rw [(liftedLinkageCurve_props hG.1 L hθ m).2.2.2.1]
      dsimp [p]
      exact div_le_div_of_nonneg_right (by nlinarith only [pi_pos]) (Nat.cast_nonneg k)
    · rw [(liftedLinkageCurve_props hG.1 L hθ (m + 1)).2.2.2.1]
      dsimp [p]
      push_cast
      exact div_le_div_of_nonneg_right (by nlinarith only [pi_pos]) (Nat.cast_nonneg k)
  have hp1 : liftedLinkageCurve hG.1 L m 1 ∈ D := by
    apply discBd_subset D
    rw [hBd]
    exact Or.inl (Or.inl (Or.inl (mem_range_self 1)))
  have hproj0 : radialCylinderProjection p = cylinderN1Point k i := by
    apply Subtype.ext
    apply Prod.ext
    · change max 1 (min 2 1) = 1
      norm_num
    · change Circle.exp _ = Circle.exp _
      congr 1
  have hproj1 : radialCylinderProjection (liftedLinkageCurve hG.1 L m 1) = L.curve i 1 := by
    rw [radialCylinderProjection_liftedLinkageCurve, modIdx_natCast_succ]
  have hγ0 : γ 0 = p := hinj (hγD 0) hp0 ((hγproj 0).trans (hfstart.trans hproj0.symm))
  have hγ1 : γ 1 = liftedLinkageCurve hG.1 L m 1 :=
    hinj (hγD 1) hp1 ((hγproj 1).trans (hfend.trans hproj1.symm))
  let a : C(unitInterval, ℝ) := ⟨fun u => (γ u).2, continuous_snd.comp γ.continuous⟩
  have ha (u : unitInterval) : Circle.exp (a u) = (f u).1.2 :=
    congrArg (fun x : ClosedCylinder => x.1.2) (hγproj u)
  rw [windingNumber_eq_of_exp_lift a ha]
  change ((γ 1).2 - (γ 0).2) / (2 * π) = _
  rw [hγ1, hγ0, (liftedLinkageCurve_props hG.1 L hθ m).2.2.2.2.1]
  dsimp [p]
  field_simp [Nat.cast_ne_zero.mpr hG.1.ne', pi_ne_zero]
  ring
end GraphMinor.GM06
