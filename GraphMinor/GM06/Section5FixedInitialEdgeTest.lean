module

public import GraphMinor.GM06.Section5FixedInitialPolarCrossing
import GraphMinor.GM06.Section5PolarLinkageDirection
import GraphMinor.GM06.Section5CoverSides

/-!
# The clockwise geometric test for all active edges

An open edge that meets a linkage path is wholly in that path.
It therefore has no clockwise lift, since that lift lies outside
the linkage. Its polar directions can only be the single path
marker, which cannot cross itself. Thus the fixed-ray test of
VI (5.7), page 133, also rejects linkage edges without a separate
query about their geometric disjointness.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The supplied cuff and path rays give the clockwise test on all
edges, including the edges of the given linkage. -/
theorem clockwise_edge_iff_crossing_fixed_initial_rays_all_edges
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
      ∀ e ∈ G.E,
        (IsClockwiseInitialEdge L i e ↔ ∃ w : Circle,
          polarRimMap Φ w ∈ cylinderToSphere '' e ∧ CrossesOn (univ : Set Circle) p q w c) := by
  obtain ⟨hpq, hpc, hqc, htest⟩ :=
    clockwise_edge_iff_crossing_fixed_initial_rays L hG hGF hbdF hθ i
      g h hgh hg0 hcover hhAngle hp p q c hpr hcr hqr
  refine ⟨hpq, hpc, hqc, ?_⟩
  intro e he
  by_cases hoff : Disjoint e (⋃ j, (L.pathDrawing j).U)
  · exact htest e he hoff
  have hsub := edge_subset_linkage_of_not_disjoint L he hoff
  have hq : polarRimMap Φ q ∈ (cylinderSphereDrawing (L.pathDrawing i)).U :=
    hqr (mem_range_self (1 : I))
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := he.1
    have hout : x ∉ ⋃ j, (L.pathDrawing j).U :=
      (connectedComponentIn_subset _ _ (hs.incident_and_subset.2 hx)).2
    exact False.elim (hout (hsub hx))
  · rintro ⟨w, ⟨x, hxe, hxw⟩, hcross⟩
    have hwL : polarRimMap Φ w ∈ cylinderToSphere '' (⋃ j, (L.pathDrawing j).U) :=
      ⟨x, hsub hxe, hxw⟩
    have hwq := (polar_rim_mem_linkage_iff_eq L hGF i hp q hq w).mp hwL
    rcases hcross with ⟨_, _, _, _, _, _, _, _, hqw, _⟩
    exact False.elim (hqw hwq.symm)

end GraphMinor.GM06
