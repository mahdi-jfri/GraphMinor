module

public import GraphMinor.GM06.Section5FixedInitialEdgeTest
public import GraphMinor.GM11.Rotation
import GraphMinor.GM06.Section5CappedInitialPath
import GraphMinor.GM06.Section5CuffSpokeArcs
import GraphMinor.GM06.Section5PolarSubdrawingEnds

/-!
# Reading the three clockwise markers from directed ends

For the reduction scan in VI (5.7), page 133, the two signed cuff
ends and the first path end specify the three markers in the input
rotation. The cuff parametrizations put their spokes in the two
half-cuff arcs. The path end belongs to the given path subdrawing.
The fixed-direction crossing theorem then applies to these ends.
The two ends of a one-vertex cuff remain separate throughout.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The negative cuff end, first path end and positive cuff end
provide the clockwise crossing test from their actual ray labels. -/
theorem clockwise_edge_iff_crossing_signed_halfedges
    {k : ℕ} {G F : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hGF : G.IsSubdrawing F) (hbdF : bd ClosedCylinder ⊆ F.U)
    (hθ : L.HasTheta θ) (i : Fin k)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar (cylinderSphereDrawing F) γ)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ)
    (a b c : halfEdges (cylinderSphereDrawing F) γ
      (cylinderToSphere (cylinderM1Point k i)))
    (d : halfEdges (cylinderSphereDrawing F) γ
      (cylinderToSphere (cylinderM1Point k i)) → Circle)
    (hd : ∀ e, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d e)) ∈ range (spoke γ e.1))
    (ha : a.1.2 = true) (hc : c.1.2 = false)
    (haAngle : ∀ t, γ a.1.1 t = cylinderToSphere (cylinderPoint 1 (by norm_num)
      ((cylinderInitialLift k i).2 - 2 * π / k + 2 * π * (t : ℝ) / k)))
    (hcAngle : ∀ t, γ c.1.1 t = cylinderToSphere (cylinderPoint 1 (by norm_num)
      ((cylinderInitialLift k i).2 + 2 * π * (t : ℝ) / k)))
    (hb : b.1.1 ∈ (cylinderSphereDrawing (L.pathDrawing i)).E) :
    d a ≠ d b ∧ d a ≠ d c ∧ d b ≠ d c ∧
      ∀ e ∈ G.E,
        (IsClockwiseInitialEdge L i e ↔ ∃ w : Circle,
          polarRimMap Φ w ∈ cylinderToSphere '' e ∧
            CrossesOn (univ : Set Circle) (d a) (d b) w (d c)) := by
  let : LocallyConnectedSpace (OnePoint EuclideanPlane) :=
    IsClosedSurface.locallyConnectedSpace
      (GM11.IsSphere.isClosedSurface (show IsSphere (OnePoint EuclideanPlane) from
        ⟨Homeomorph.refl _⟩)).1
  obtain ⟨g, h, hgh, hg0, hcover, hgAngle, hhAngle⟩ :=
    exists_initial_cuff_half_arcs (cylinderInitialLift k i).2
  have hg0' : g 0 = cylinderM1Point k i := hg0
  let fa : I → ClosedCylinder := fun t => cylinderPoint 1 (by norm_num)
    ((cylinderInitialLift k i).2 - 2 * π / k + 2 * π * (t : ℝ) / k)
  let fc : I → ClosedCylinder := fun t => cylinderPoint 1 (by norm_num)
    ((cylinderInitialLift k i).2 + 2 * π * (t : ℝ) / k)
  have hka : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hag := negative_cuff_spoke_range_subset hka (cylinderInitialLift k i).2
    fa g (fun _ => rfl) hgAngle
  have hch := positive_cuff_spoke_range_subset hka (cylinderInitialLift k i).2
    fc h (fun _ => rfl) hhAngle
  have has : range (spoke γ a.1) ⊆ range (cylinderToSphere ∘ g) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨r, hr⟩ := hag (mem_range_self t)
    refine ⟨r, ?_⟩
    change cylinderToSphere (g r) = γ a.1.1 (halfPar a.1.2 t)
    rw [ha, haAngle]
    exact congrArg cylinderToSphere hr
  have hcs : range (spoke γ c.1) ⊆ range (cylinderToSphere ∘ h) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨r, hr⟩ := hch (mem_range_self t)
    refine ⟨r, ?_⟩
    change cylinderToSphere (h r) = γ c.1.1 (halfPar c.1.2 t)
    rw [hc, hcAngle]
    exact congrArg cylinderToSphere hr
  have hP := cylinderSphereDrawing_isSubdrawing ((L.isSubdrawing i).1.trans hGF)
  have hbr : polarRimMap Φ (d b) ∈ (cylinderSphereDrawing (L.pathDrawing i)).U :=
    (polar_rim_mem_subdrawing_iff_halfedge_edge_mem hP hγ hp b (d b) (hd b)).mpr hb
  exact clockwise_edge_iff_crossing_fixed_initial_rays_all_edges L hG hGF hbdF hθ i
    g h hgh hg0' hcover hhAngle hp (d a) (d b) (d c)
    ((polar_ray_range_subset_halfedge_spoke hp a (d a) (hd a)).trans has)
    ((polar_ray_range_subset_halfedge_spoke hp c (d c) (hd c)).trans hcs)
    (polar_ray_range_subset_subdrawing_of_rim_mem hP hp (d b) hbr)

end GraphMinor.GM06
