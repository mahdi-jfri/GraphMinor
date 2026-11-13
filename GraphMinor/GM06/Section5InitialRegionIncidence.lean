module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM11.Corners
import GraphMinor.GM06.Section5CappedPuncture
import GraphMinor.GM06.Section5DistinctCorners
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.PerimeterPull

/-!
# Two incident half-edges per region at an initial vertex

For the boundary argument of VI (5.1), page 129, the drawing with
cuffs remains connected after deleting an initial vertex. In the
capped sphere its corners therefore belong to distinct regions.
Consequently each incident region has at most two half-edges at that
vertex. This is the local incidence bound used to distinguish the
region beside the initial cuff gap from extra edges at the start.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- At an initial vertex of an unreduced Section 5 drawing with at
least two linkage paths, each capped region has at most two incident
half-edges. -/
theorem ncard_initial_region_halfEdges_le_two
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V)
    (i : Fin k)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar (cylinderSphereDrawing F) γ)
    {r : Set (OnePoint EuclideanPlane)} (hr : r ∈ (cylinderSphereDrawing F).R)
    (hsr : cylinderToSphere (cylinderM1Point k i) ∈ closure r) :
    {j : halfEdges (cylinderSphereDrawing F) γ (cylinderToSphere (cylinderM1Point k i)) |
      j.1.1 ⊆ closure r}.ncard ≤ 2 := by
  classical
  let D := cylinderSphereDrawing F
  let s := cylinderToSphere (cylinderM1Point k i)
  have : Finite (halfEdges D γ s) := (finite_halfEdges D γ s).to_subtype
  have hs : s ∈ D.V := by
    rw [cylinderSphereDrawing_V, hFV]
    exact mem_image_of_mem cylinderToSphere
      ((L.isSubdrawing i).1.1 (isPathDrawing_end_vertices (L.isPath i)).1)
  by_cases h2 : 2 ≤ Nat.card (halfEdges D γ s)
  · have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
    have hS := GM11.IsSphere.isClosedSurface hsph
    let : ConnectedSpace (OnePoint EuclideanPlane) := hS.2
    obtain ⟨next, ρ, P, W, Q, τ, hsec⟩ := exists_sectors hS.1 D hγ hs h2
    have hinj := corners_injective_of_punctured_drawing_connected hS.1 hsph hs hsec
      (isConnected_punctured_cylinderSphereDrawing L hk hG hno hFU i).isPreconnected
    obtain ⟨j, hj⟩ := hsec.corners.all r hr hsr
    rw [hj, incident_halfEdges_eq_corner_pair hsec.corners hinj j]
    rw [ncard_pair (hsec.next_ne j).symm]
  · exact le_trans (ncard_le_card _) (Nat.le_of_lt (Nat.lt_of_not_ge h2))

end GraphMinor.GM06
