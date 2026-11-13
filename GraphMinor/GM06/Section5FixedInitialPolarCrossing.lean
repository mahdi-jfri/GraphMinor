module

public import GraphMinor.GM06.Section5InitialPolarCrossingTest
public import GraphMinor.GM06.Section5PolarShrink
import GraphMinor.GM06.Section5CappedInitialPath
import GraphMinor.GM11.Walks

/-!
# The clockwise test with specified input directions

The local proof of the corrected side test constructs its cuff
and path directions in a smaller chart. Each follows a specified
initial arc. The same arc in the input chart has a unique direction,
so radial restriction identifies the two labels. The crossing test
therefore holds for the supplied cuff and path directions, without
choosing new markers from its conclusion.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The two specified cuff rays and the specified path ray in the
input chart give the corrected clockwise crossing test of VI (5.7). -/
theorem clockwise_edge_iff_crossing_fixed_initial_rays
    {k : ℕ} {G F : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hGF : G.IsSubdrawing F) (hbdF : bd ClosedCylinder ⊆ F.U)
    (hθ : L.HasTheta θ) (i : Fin k)
    (g h : I → ClosedCylinder) (hgh : IsTwoArcs g h)
    (hg0 : g 0 = cylinderM1Point k i) (hcover : range g ∪ range h = cylinderCuff1)
    (hhAngle : ∀ t : I, h t = cylinderPoint 1 (by norm_num)
      ((cylinderInitialLift k i).2 + π * (t : ℝ)))
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ)
    (p q c : Circle)
    (hpr : range (polarRayMap Φ p) ⊆ range (cylinderToSphere ∘ g))
    (hcr : range (polarRayMap Φ c) ⊆ range (cylinderToSphere ∘ h))
    (hqr : range (polarRayMap Φ q) ⊆ (cylinderSphereDrawing (L.pathDrawing i)).U) :
    p ≠ q ∧ p ≠ c ∧ q ≠ c ∧
      ∀ e ∈ G.E, Disjoint e (⋃ j, (L.pathDrawing j).U) →
        (IsClockwiseInitialEdge L i e ↔ ∃ w : Circle,
          polarRimMap Φ w ∈ cylinderToSphere '' e ∧ CrossesOn (univ : Set Circle) p q w c) := by
  let : LocallyConnectedSpace (OnePoint EuclideanPlane) :=
    IsClosedSurface.locallyConnectedSpace
      (GM11.IsSphere.isClosedSurface (show IsSphere (OnePoint EuclideanPlane) from
        ⟨Homeomorph.refl _⟩)).1
  obtain ⟨Ψ, hΨ, _, ⟨a, ha, hscale⟩, p₀, q₀, c₀, hpq, hpc, hqc, hpg, hch, _, _, hqP, htest⟩ :=
    exists_initial_polar_clockwise_crossing_test_with_cuff_rays L hG hGF hbdF hθ i
      g h hgh hg0 hcover hhAngle hp isOpen_univ (mem_univ _)
  let fg : C(I, OnePoint EuclideanPlane) :=
    ⟨cylinderToSphere ∘ g, continuous_cylinderToSphere.comp hgh.arc_left.1⟩
  let fh : C(I, OnePoint EuclideanPlane) :=
    ⟨cylinderToSphere ∘ h, continuous_cylinderToSphere.comp hgh.arc_right.1⟩
  have hfg : IsArcMap fg :=
    ⟨fg.continuous, injective_cylinderToSphere.comp hgh.arc_left.2⟩
  have hfh : IsArcMap fh :=
    ⟨fh.continuous, injective_cylinderToSphere.comp hgh.arc_right.2⟩
  have hfg0 : fg 0 = cylinderToSphere (cylinderM1Point k i) := congrArg cylinderToSphere hg0
  have hfh0 : fh 0 = cylinderToSphere (cylinderM1Point k i) :=
    congrArg cylinderToSphere (hgh.zero.trans hg0)
  have hp₀ : p₀ = p := polar_direction_eq_of_radial_restriction_in_arc hΨ a hscale fg hfg hfg0 hpg hpr
  have hc₀ : c₀ = c := polar_direction_eq_of_radial_restriction_in_arc hΨ a hscale fh hfh hfh0 hch hcr
  let P := cylinderSphereDrawing (L.pathDrawing i)
  let f := cylinderSphereCurve (L.curve i)
  have hf : ParametrizesSet f P.U (cylinderToSphere (cylinderM1Point k i))
      (cylinderToSphere (L.curve i 1)) := by
    rw [cylinderSphereDrawing_U]
    exact cylinderSphereCurve_parametrizesSet (L.curve_parametrizes i)
  have hPiF := cylinderSphereDrawing_isSubdrawing ((L.isSubdrawing i).1.trans hGF)
  have hnPi : IsGammaNice (cylinderSphereDrawing F) P.U :=
    isGammaNice_of_frontier hPiF subset_rfl
      (frontier_subset_closure.trans (by rw [P.isClosed_U.closure_eq]))
  have hq₀range : range (polarRayMap Ψ q₀) ⊆ range f := by
    rintro _ ⟨r, rfl⟩
    rw [hf.2.1]
    have hh := hΨ.star P.isClosed_U hnPi hqP r
    rwa [discScale_polarDiscPoint_one] at hh
  have hqrange : range (polarRayMap Φ q) ⊆ range f := hf.2.1.symm ▸ hqr
  have hq₀ : q₀ = q := polar_direction_eq_of_radial_restriction_in_arc hΨ a hscale f
    ⟨f.continuous, hf.1⟩ hf.2.2.1 hq₀range hqrange
  subst p₀
  subst q₀
  subst c₀
  refine ⟨hpq, hpc, hqc, ?_⟩
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
