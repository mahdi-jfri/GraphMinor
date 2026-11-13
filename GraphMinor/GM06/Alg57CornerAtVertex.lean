module

public import GraphMinor.GM06.Alg57InnerCuffCorner

/-!
# Reading a face corner in any positive vertex chart

The local side proof of VI (5.7), page 133, compares the full drawing
and its linkage-and-cuff subdrawing in one chart. A corner label can
be read in any positive chart giving the same counterclockwise star.
Both charts give the same corner at an interior point of the dart,
by the half-band argument along that edge.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A geometric corner label is read by any positive star for the
same drawing rotation at the dart's vertex. -/
theorem cornerLabel_eq_star
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {R : DartRotation (DrawingDart Γ)} {ρ : DrawingDart Γ → Set (OnePoint EuclideanPlane)}
    (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ Γ.U) (hγ : EdgePar Γ γ)
    (hform : ∀ d, ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane))
      (z : DrawingDart Γ → Circle), IsCcwStar Γ γ R (dartVertex γ d) Φ z ∧
        ρ d = cornerRegion Γ Φ (z d))
    (d : DrawingDart Γ) {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    {z : DrawingDart Γ → Circle} (hst : IsCcwStar Γ γ R (dartVertex γ d) Φ z) :
    ρ d = cornerRegion Γ Φ (z d) := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩).1
  have ha : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  obtain ⟨Φm, Ψm, F, B, δ₁, _, hpm, hΨm, hposm, hDm, _, hout, _⟩ :=
    exists_edge_chart hS hinf d.property (isEdgeCurve_dartCurve hγ d) ha
  have hfin : (rimDirs Γ Φm).Finite := by rw [hDm]; exact (finite_singleton _).insert _
  have hF : F ∈ rimDirs Γ Φm := by rw [hDm]; exact mem_insert _ _
  have hmid := cornerLabel_eq_mid hinf hγ hform d (1 / 2) ha Φm Ψm
    hpm hΨm hposm hfin F hF δ₁ hout
  obtain ⟨Ψ, hΨ, hw⟩ := hst.pos
  have hpos : 0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) := by
    rw [wind_chartC]
    exact hw
  obtain ⟨_, hrun⟩ := hst.runsOut hγ hΨ rfl
  have hp : IsPolar Γ (dartCurve γ d 0) Φ := by
    rw [dartCurve_zero]
    exact hst.polar
  exact hmid.trans (cornerRegion_start_eq_mid hS hinf d.property (isEdgeCurve_dartCurve hγ d)
    hp hΨ hpos (hst.rimDirs_finite hγ) (hst.mem_rimDirs hγ rfl) hrun
    ha hpm hΨm hposm hfin hF hout).symm

end GraphMinor.GM06
