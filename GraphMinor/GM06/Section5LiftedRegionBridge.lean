module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5ContractionNeighbourAccess
import GraphMinor.GM06.Section5CoverSides
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Extending lifted neighbour access through a region

In the Reduction 3 construction for VI (5.5), page 130, extend a
short access curve from the old neighbour to a chosen point of the
selected lifted region. The region is open and connected in the
locally path-connected cover, so its interior points can be joined
by a path. Concatenation retains the chosen sheet and introduces
no further drawing contacts.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

private theorem extend_access_to_region_point
    {X : Type*} [TopologicalSpace X] {r : Set X} (hr : IsPathConnected r)
    (a : C(unitInterval, X)) {w x : X} (ha0 : a 0 = w)
    (ha : ∀ t, 0 < t → a t ∈ r) (hx : x ∈ r) :
    ∃ b : C(unitInterval, X), b 0 = w ∧ b 1 = x ∧ ∀ t, 0 < t → b t ∈ r := by
  let p : Path w (a 1) := ⟨a, ha0, rfl⟩
  have hj := hr.joinedIn (a 1) (ha 1 zero_lt_one) x hx
  let b := (p.trans hj.somePath).toContinuousMap
  refine ⟨b, Path.source _, Path.target _, ?_⟩
  intro t ht
  change (p.trans hj.somePath) t ∈ r
  rw [Path.trans_apply]
  split_ifs with hhalf
  · apply ha
    change (0 : ℝ) < 2 * (t : ℝ)
    have ht' : 0 < (t : ℝ) := ht
    linarith only [ht']
  · exact hj.somePath_mem _

/-- Join the specified old neighbour lift to any point of its
incident lifted component, with all positive parameters in that component. -/
theorem exists_curve_from_contraction_neighbour_to_cover_region_point
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) (hGF : G.IsSubdrawing F)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hv : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2)
    (w : CylinderCover) (hw : cylinderCoverProjection w = v)
    {r : Set CylinderCover} (hr : r ∈ componentsIn (cylinderCoverProjection ⁻¹' F.Uᶜ))
    (hwr : w ∈ closure r) {x : CylinderCover} (hx : x ∈ r) :
    ∃ g : C(unitInterval, CylinderCover), g 0 = w ∧ g 1 = x ∧ ∀ t, 0 < t → g t ∈ r := by
  let : LocallyPathConnectedSpace (Icc (1 : ℝ) 2) := (convex_Icc (1 : ℝ) 2).locallyPathConnectedSpace
  let : LocallyPathConnectedSpace CylinderCover := inferInstance
  have hro : IsOpen r := by
    obtain ⟨y, _, rfl⟩ := hr
    exact (F.isClosed_U.preimage continuous_cylinderCoverProjection).isOpen_compl.connectedComponentIn
  have hrc : IsPreconnected r := by
    obtain ⟨y, _, rfl⟩ := hr
    exact isPreconnected_connectedComponentIn
  have hrpath : IsPathConnected r := hro.isConnected_iff_isPathConnected.mp ⟨⟨x, hx⟩, hrc⟩
  obtain ⟨a, ha0, ha⟩ := exists_access_at_contraction_neighbour_in_cover
    L hG i hGF hval hl hv hvC w hw hr hwr
  exact extend_access_to_region_point hrpath a ha0 ha hx

/-- Join two specified lifts of the old neighbour through their
common lifted region, with no other drawing contacts. -/
theorem exists_curve_between_contraction_neighbour_lifts_through_region
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) (hGF : G.IsSubdrawing F)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hv : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2)
    (w w' : CylinderCover) (hw : cylinderCoverProjection w = v)
    (hw' : cylinderCoverProjection w' = v)
    {r : Set CylinderCover} (hr : r ∈ componentsIn (cylinderCoverProjection ⁻¹' F.Uᶜ))
    (hwr : w ∈ closure r) (hw'r : w' ∈ closure r) (x : CylinderCover) (hx : x ∈ r) :
    ∃ g : C(unitInterval, CylinderCover), g 0 = w ∧ g 1 = w' ∧
      ∀ t, 0 < t → t < 1 → g t ∈ r := by
  obtain ⟨a, ha0, ha1, ha⟩ := exists_curve_from_contraction_neighbour_to_cover_region_point
    L hG i hGF hval hl hv hvC w hw hr hwr hx
  obtain ⟨b, hb0, hb1, hb⟩ := exists_curve_from_contraction_neighbour_to_cover_region_point
    L hG i hGF hval hl hv hvC w' hw' hr hw'r hx
  let p : Path w x := ⟨a, ha0, ha1⟩
  let q : Path w' x := ⟨b, hb0, hb1⟩
  let g := (p.trans q.symm).toContinuousMap
  refine ⟨g, Path.source _, Path.target _, ?_⟩
  intro t ht0 ht1
  change (p.trans q.symm) t ∈ r
  rw [Path.trans_apply]
  split_ifs with hhalf
  · apply ha
    change (0 : ℝ) < 2 * (t : ℝ)
    have ht : 0 < (t : ℝ) := ht0
    linarith only [ht]
  · apply hb
    change (0 : ℝ) < 1 - (2 * (t : ℝ) - 1)
    have ht : (t : ℝ) < 1 := ht1
    linarith only [ht]

end GraphMinor.GM06
