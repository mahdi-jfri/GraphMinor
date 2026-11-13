module

public import GraphMinor.GM06.Alg57CornerLabelExists
public import GraphMinor.GM06.Alg57EdgeCorner

/-!
# Which region a face orbit is

`sphere_faceOrbits_ccw` matches the orbits of `φ = σ⁻¹ τ` with the regions. To use it we must know
which region belongs to a given orbit. The region of the orbit of a dart `d` is the region on
the left of `d`. Here we say this in a form that can be checked in any chart along the edge of
`d`: if the edge of `d` runs out along a ray `W` of a positive chart centred at an inner point of
the edge, then the region of the orbit of `d` is the corner after `W`
(`sphere_faceOrbits_ccw_corner`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

variable {Γ : Drawing (OnePoint EuclideanPlane)}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart Γ)}

/-- **Lemma 3, with the region of each orbit.** This is `sphere_faceOrbits_ccw`, together with:
the region of the orbit of a dart `d` is the corner after `W` in any positive chart centred at an
inner point of the edge of `d`, along whose ray `W` the edge runs out in the direction of `d`. -/
theorem sphere_faceOrbits_ccw_corner (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ Γ.U)
    (hγ : EdgePar Γ γ) (hR : IsDrawingRotation Γ γ R) (hccw : IsCcwRotation Γ γ R)
    (hc : R.Connected) (hV : ∀ v ∈ Γ.V, ∃ d : DrawingDart Γ, dartVertex γ d = v)
    (hne : Γ.E.Nonempty) :
    ∃ L : R.Faces → Γ.R, Function.Bijective L ∧
      (∀ (O : R.Faces) (d : DrawingDart Γ),
        d.1.1 ⊆ closure (L O).1 ↔ R.faceOf d = O ∨ R.faceOf (R.rev d) = O) ∧
      (∀ (O : R.Faces), ∀ v ∈ Γ.V,
        v ∈ closure (L O).1 ↔ ∃ d : DrawingDart Γ, dartVertex γ d = v ∧ R.faceOf d = O) ∧
      ∀ (d : DrawingDart Γ) (a : ℝ), a ∈ Ioo (0 : ℝ) 1 →
        ∀ (Φm : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (Ψm : C(ClosedUnitDisc, EuclideanPlane)),
        IsPolar Γ (dartCurve γ d a) Φm → (∀ x, Φm x = (Ψm x : OnePoint EuclideanPlane)) →
        0 < wind (fun w : Circle => chartC Ψm w) (chartC Ψm 0) → (rimDirs Γ Φm).Finite →
        ∀ (Wm : Circle), Wm ∈ rimDirs Γ Φm → ∀ (δ : ℝ), RunsOut Ψm Wm (dartCurve γ d) a δ →
        (L (R.faceOf d)).1 = cornerRegion Γ Φm Wm := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩).1
  obtain ⟨ρ, hρ, hform⟩ := exists_cornerLabel hinf hγ hR hccw
  refine ⟨hρ.label, hρ.sphere_faceOrbits hinf hγ hR hc hV hne |>.1,
    (hρ.sphere_faceOrbits hinf hγ hR hc hV hne).2.1,
    (hρ.sphere_faceOrbits hinf hγ hR hc hV hne).2.2, ?_⟩
  intro d a ha Φm Ψm hpm hΨm hposm hDm Wm hWm δ hrunm
  rw [hρ.label_faceOf]
  obtain ⟨Φ, z, hst, hρd⟩ := hform d
  rw [hρd]
  obtain ⟨Ψ, hΨ, hw⟩ := hst.pos
  have hpos : 0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) := by
    rw [wind_chartC]; exact hw
  obtain ⟨δu, hrunu⟩ := hst.runsOut hγ hΨ rfl
  have hpu : IsPolar Γ (dartCurve γ d 0) Φ := by rw [dartCurve_zero]; exact hst.polar
  exact cornerRegion_start_eq_mid hS hinf d.2 (isEdgeCurve_dartCurve hγ d) hpu hΨ hpos
    (hst.rimDirs_finite hγ) (hst.mem_rimDirs hγ rfl) hrunu ha hpm hΨm hposm hDm hWm hrunm

end GraphMinor.GM06
