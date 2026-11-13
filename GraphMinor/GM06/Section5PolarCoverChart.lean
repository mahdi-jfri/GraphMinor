module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM11.LocalCone
public import Mathlib.Topology.IsLocalHomeomorph
import GraphMinor.GM06.Section5SmallPolar

/-!
# Polar charts contained in one angular sheet

For the side test in VI (5.7), page 133, the polar chart lies in
the capped sphere, while the angular cover has a chart on the
cylinder. The annulus embedding induces the cylinder topology.
Extend the target of the cover chart to an open sphere set, then
shrink the polar chart into that set. Its cylinder points now all
belong to the one chosen inverse chart.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- A polar chart at an initial vertex can be chosen so that all its
cylinder points lie in a prescribed angular-cover chart target. -/
theorem exists_polar_chart_in_cover_target
    {k : ℕ} {F : Drawing ClosedCylinder} (i : Fin k)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ)
    (η : OpenPartialHomeomorph CylinderCover ClosedCylinder)
    (hη : (η : CylinderCover → ClosedCylinder) = cylinderCoverProjection)
    (hsη : cylinderInitialLift k i ∈ η.source) :
    ∃ Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane),
      IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Ψ ∧
      ∀ y : ClosedCylinder, cylinderToSphere y ∈ range Ψ → y ∈ η.target := by
  obtain ⟨O, hOo, hOT⟩ :=
    isClosedEmbedding_cylinderToSphere.isEmbedding.isInducing.isOpen_iff.mp η.open_target
  have hs : cylinderM1Point k i ∈ η.target := by
    have hh := η.map_source hsη
    rw [hη] at hh
    exact hh
  have hsO : cylinderToSphere (cylinderM1Point k i) ∈ O := by
    change cylinderM1Point k i ∈ cylinderToSphere ⁻¹' O
    rwa [hOT]
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  obtain ⟨Ψ, hΨ, hΨO⟩ := exists_small_polar_chart hS hp hOo hsO
  refine ⟨Ψ, hΨ, ?_⟩
  intro y hy
  have hh : y ∈ cylinderToSphere ⁻¹' O := hΨO hy
  rwa [hOT] at hh

end GraphMinor.GM06
