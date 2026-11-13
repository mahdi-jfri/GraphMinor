module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverTranslation
import GraphMinor.GM06.Section5ContractionCoverHomotopy
import GraphMinor.GM06.Section5ContractionCoverFibre
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section4

/-!
# Constructing the lifted contraction and its neighbour section

The Reduction 3 argument in VI (5.5), page 130, uses the actual
boundary-fixed contraction homotopy to choose its cover lift.
Its fixed initial lift determines the lifted contracted edge and
old neighbour. Full-turn translation then chooses neighbour preimages
at all exceptional values, and the off-fibre inverse supplies the rest.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Construct the actual cover contraction and a section taking
every exceptional value to its old neighbour in the corresponding sheet. -/
theorem exists_cover_contraction_with_neighbour_section
    {k : ℕ} {G : Drawing ClosedCylinder} (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v) (hv : v ≠ cylinderM1Point k i)
    (π : C(ClosedCylinder, ClosedCylinder))
    (H : C(unitInterval × ClosedCylinder, ClosedCylinder))
    (hH0 : ∀ p, H (0, p) = p) (hH1 : ∀ p, H (1, p) = π p)
    (hHbd : ∀ p ∈ bd ClosedCylinder, ∀ t, H (t, p) = p)
    (hfibre : π ⁻¹' {cylinderM1Point k i} = closure e)
    (hsurj : ∀ x, x ≠ cylinderM1Point k i → ∃ y, π y = x) :
    ∃ Φ : C(CylinderCover, CylinderCover), ∃ ρ : CylinderCover → CylinderCover,
      (∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p)) ∧
      (∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p)) ∧
      (∀ p, cylinderCoverProjection p ∈ bd ClosedCylinder → Φ p = p) ∧
      (∀ p, Φ (ρ p) = p) ∧
      ∀ p, cylinderCoverProjection p = cylinderM1Point k i → cylinderCoverProjection (ρ p) = v := by
  obtain ⟨A, hAproj, hA0, hAbd⟩ := exists_cover_homotopy_of_boundary_fixed_homotopy H hH0 hHbd
  let Φ : C(CylinderCover, CylinderCover) :=
    ⟨fun p => A (1, p), A.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hproj (p) : cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p) :=
    (hAproj 1 p).trans (hH1 _)
  have htrans (z) (p) : Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p) :=
    cover_homotopy_commutes_with_translation H A hAproj hA0 z p 1
  have hfix (p) (hp : cylinderCoverProjection p ∈ bd ClosedCylinder) : Φ p = p := hAbd p hp 1
  let p := cylinderInitialLift k i
  have hp : cylinderCoverProjection p = cylinderM1Point k i := cylinderCoverProjection_initialLift i
  have hpbd : cylinderCoverProjection p ∈ bd ClosedCylinder := by
    rw [hp, bd_closedCylinder]
    exact Or.inl rfl
  obtain ⟨γ, q, hγ, _, hq, hqfibre⟩ := exists_parametrized_cover_contraction_fibre
    hl hv π Φ hproj htrans hfibre p hp (hfix p hpbd)
  have hq1 : Φ (q 1) = p := by
    have hh : q 1 ∈ Φ ⁻¹' {p} := hqfibre.symm ▸ mem_range_self 1
    exact hh
  have hqv : cylinderCoverProjection (q 1) = v := (hq 1).trans hγ.2.2.2
  obtain ⟨ρ, hρ, hρv⟩ := exists_cover_contraction_section_at_neighbour
    π Φ (cylinderM1Point k i) v hproj htrans hsurj p (q 1) hq1 hp hqv
  exact ⟨Φ, ρ, hproj, htrans, hfix, hρ, hρv⟩

end GraphMinor.GM06
