module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM06.Section5PolarRay
public import GraphMinor.GM11.LocalCone
public import Mathlib.Topology.IsLocalHomeomorph
import GraphMinor.GM06.Section5CoverCurvePoint

/-!
# Lifting a polar direction carried by an angular cuff arc

For the side test in VI (5.7), page 133, a polar cuff ray is
carried by one of the two angular cuff arcs. Invert that injective
arc to obtain a continuous parameter starting at zero. Its explicit
angular formula gives a cover lift. Uniqueness of lifts identifies
it with the chosen inverse chart, so the rim point has the same
signed angular displacement as its cuff-arc parameter.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A polar cuff direction has the signed angle of its carrying
cuff arc in the inverse chart aligned at the initial vertex. -/
theorem exists_positive_parameter_of_polar_cuff_direction
    {k : ℕ} (i : Fin k) {Γ : Drawing (OnePoint EuclideanPlane)}
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar Γ (cylinderToSphere (cylinderM1Point k i)) Φ)
    (g : I → ClosedCylinder) (hg : IsArcMap g)
    (hg0 : g 0 = cylinderM1Point k i) (δ : ℝ)
    (hgAngle : ∀ t : I, g t = cylinderPoint 1 (by norm_num)
      ((cylinderInitialLift k i).2 + δ * (t : ℝ)))
    (w : Circle) (hw : range (polarRayMap Φ w) ⊆ range (cylinderToSphere ∘ g))
    (η : OpenPartialHomeomorph CylinderCover ClosedCylinder)
    (hη : (η : CylinderCover → ClosedCylinder) = cylinderCoverProjection)
    (hsη : cylinderInitialLift k i ∈ η.source)
    (hsmall : ∀ y : ClosedCylinder, cylinderToSphere y ∈ range Φ → y ∈ η.target) :
    ∃ r : I, 0 < r ∧ polarRimMap Φ w = cylinderToSphere (g r) ∧
      η.symm (g r) = (⟨1, by norm_num⟩,
        (cylinderInitialLift k i).2 + δ * (r : ℝ)) := by
  let f : C(I, OnePoint EuclideanPlane) :=
    ⟨cylinderToSphere ∘ g, continuous_cylinderToSphere.comp hg.1⟩
  have hfi : Function.Injective f := injective_cylinderToSphere.comp hg.2
  let E : I ≃ₜ range f := (f.continuous.isClosedEmbedding hfi).isEmbedding.toHomeomorph
  let ψ : C(I, I) :=
    ⟨fun t => E.symm ⟨polarRayMap Φ w t, hw (mem_range_self t)⟩,
      E.symm.continuous.comp ((polarRayMap Φ w).continuous.subtype_mk _)⟩
  have hψ (t : I) : cylinderToSphere (g (ψ t)) = polarRayMap Φ w t :=
    congrArg Subtype.val (E.apply_symm_apply ⟨polarRayMap Φ w t, hw (mem_range_self t)⟩)
  have hψ0 : ψ 0 = 0 := by
    apply hfi
    change cylinderToSphere (g (ψ 0)) = cylinderToSphere (g 0)
    rw [hψ, polarRayMap_zero, hp.centre, hg0]
  have hψ1 : 0 < ψ 1 := unitInterval.pos_iff_ne_zero.mpr (by
    intro hh
    have h10 : polarRayMap Φ w 1 = polarRayMap Φ w 0 := by
      rw [← hψ 1, ← hψ 0, hh, hψ0]
    exact one_ne_zero ((isArcMap_polarRayMap hp.inj w).2 h10))
  let q : C(I, CylinderCover) :=
    ⟨fun t => (⟨1, by norm_num⟩, (cylinderInitialLift k i).2 + δ * (ψ t : ℝ)), by fun_prop⟩
  have hqproj (t : I) : cylinderCoverProjection (q t) = g (ψ t) := by
    rw [hgAngle]
    rfl
  have hfT (t : I) : g (ψ t) ∈ η.target := by
    apply hsmall
    rw [hψ]
    exact mem_range_self (polarDiscPoint t w)
  let Q : C(I, CylinderCover) :=
    ⟨fun t => η.symm (g (ψ t)),
      η.symm.continuousOn.comp_continuous (hg.1.comp ψ.continuous) hfT⟩
  have hQproj (t : I) : cylinderCoverProjection (Q t) = g (ψ t) := by
    change cylinderCoverProjection (η.symm (g (ψ t))) = _
    rw [← hη, η.right_inv (hfT t)]
  have hq0 : q 0 = cylinderInitialLift k i := by
    apply Prod.ext
    · rfl
    · change (cylinderInitialLift k i).2 + δ * (ψ 0 : ℝ) = _
      rw [hψ0]
      simp only [Icc.coe_zero, mul_zero, add_zero]
  have hQ0 : Q 0 = cylinderInitialLift k i := by
    change η.symm (g (ψ 0)) = _
    rw [hψ0, hg0]
    have hs : η (cylinderInitialLift k i) = cylinderM1Point k i := by rw [hη]; rfl
    rw [← hs, η.left_inv hsη]
  have hqQ : q = Q := cover_curves_eq_of_projection_eq q Q
    (fun t => (hqproj t).trans (hQproj t).symm) 0 (hq0.trans hQ0.symm)
  exact ⟨ψ 1, hψ1, (hψ 1).symm, (congrArg (fun a : C(I, CylinderCover) => a 1) hqQ).symm⟩

end GraphMinor.GM06
