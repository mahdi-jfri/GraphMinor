module

public import GraphMinor.GM06.Section5InitialPolarCrossingTest
import GraphMinor.GM06.Section5PolarShrink
import GraphMinor.GM06.Section5CappedCuffSubdrawings
import GraphMinor.GM06.Section5CappedInitialPath
import GraphMinor.GM11.Walks

/-!
# The clockwise test in the input polar chart

For VI (5.7), page 133, the geometric side test is constructed in a
small restriction of the input chart. Positive restriction preserves
all edge and subdrawing directions. The crossing test therefore uses
the original directions, as required by the encoded rotation row.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The given initial chart, without changing its direction labels,
recognizes clockwise edges by four-point crossing. -/
theorem exists_initial_input_polar_clockwise_crossing_test
    {k : ℕ} {G F : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hGF : G.IsSubdrawing F) (hbdF : bd ClosedCylinder ⊆ F.U)
    (hθ : L.HasTheta θ) (i : Fin k)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ) :
    ∃ p q c : Circle, p ≠ q ∧ p ≠ c ∧ q ≠ c ∧
      polarRimMap Φ p ∈ cylinderToSphere '' cylinderCuff1 ∧
      polarRimMap Φ c ∈ cylinderToSphere '' cylinderCuff1 ∧
      polarRimMap Φ q ∈ (cylinderSphereDrawing (L.pathDrawing i)).U ∧
      ∀ e ∈ G.E, Disjoint e (⋃ j, (L.pathDrawing j).U) →
        (IsClockwiseInitialEdge L i e ↔ ∃ w : Circle,
          polarRimMap Φ w ∈ cylinderToSphere '' e ∧ CrossesOn (univ : Set Circle) p q w c) := by
  let : LocallyConnectedSpace (OnePoint EuclideanPlane) :=
    IsClosedSurface.locallyConnectedSpace
      (GM11.IsSphere.isClosedSurface (show IsSphere (OnePoint EuclideanPlane) from
        ⟨Homeomorph.refl _⟩)).1
  obtain ⟨Ψ, hΨ, _, ⟨a, ha, hscale⟩, p, q, c, hpq, hpc, hqc, hpC, hcC, hqP, htest⟩ :=
    exists_initial_polar_clockwise_crossing_test L hG hGF hbdF hθ i hp
      isOpen_univ (mem_univ _)
  have hPiF := cylinderSphereDrawing_isSubdrawing ((L.isSubdrawing i).1.trans hGF)
  have hnPi : IsGammaNice (cylinderSphereDrawing F) (cylinderSphereDrawing (L.pathDrawing i)).U :=
    isGammaNice_of_frontier hPiF subset_rfl
      (frontier_subset_closure.trans (by rw [(cylinderSphereDrawing (L.pathDrawing i)).isClosed_U.closure_eq]))
  obtain ⟨C₁, _, hC₁F, _, hC₁U, _⟩ := exists_capped_cuff_subdrawings F hbdF
  have hnC : IsGammaNice (cylinderSphereDrawing F) (cylinderToSphere '' cylinderCuff1) := by
    rw [← hC₁U]
    exact isGammaNice_of_frontier hC₁F subset_rfl
      (frontier_subset_closure.trans (by rw [C₁.isClosed_U.closure_eq]))
  refine ⟨p, q, c, hpq, hpc, hqc,
    (polar_rim_mem_nice_iff_of_radial_restriction hp a ha hscale hnC p).mpr hpC,
    (polar_rim_mem_nice_iff_of_radial_restriction hp a ha hscale hnC c).mpr hcC,
    (polar_rim_mem_nice_iff_of_radial_restriction hp a ha hscale hnPi q).mpr hqP, ?_⟩
  intro e he hoff
  have heF : cylinderToSphere '' e ∈ (cylinderSphereDrawing F).E := by
    rw [cylinderSphereDrawing_E]
    exact ⟨e, hGF.2 he, rfl⟩
  have hnE : IsGammaNice (cylinderSphereDrawing F) (cylinderToSphere '' e) :=
    ⟨{cylinderToSphere '' e}, by simpa using (show cylinderToSphere '' e ∈
      (cylinderSphereDrawing F).A from Or.inl (Or.inr heF)), by simp⟩
  rw [htest e he hoff]
  exact exists_congr fun w => and_congr_left fun _ =>
    (polar_rim_mem_nice_iff_of_radial_restriction hp a ha hscale hnE w).symm

end GraphMinor.GM06
