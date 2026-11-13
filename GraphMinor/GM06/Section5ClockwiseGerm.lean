module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5CoverCurve
import Mathlib.Topology.Connected.Basic

/-!
# Passing from a lifted edge point to the clockwise side

The finite side test in VI (5.7), page 133, inspects a directed end
near its initial vertex. Once an interior point of that lifted end is
in the preceding strip, connectedness puts the whole lifted open edge
in the same strip. Its parametrization also supplies incidence at the
chosen initial lift. This gives the corrected Reduction 1 certificate.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- An open edge lifted from the prescribed initial vertex is clockwise
as soon as one of its interior lifted points is in the preceding strip. -/
theorem isClockwiseInitialEdge_of_lifted_edge_point
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k)
    (f : Curve ClosedCylinder) {e : Set ClosedCylinder}
    (hstart : f 0 = cylinderM1Point k i)
    (himage : f '' Ioo (0 : unitInterval) 1 = e)
    (hoff : Disjoint e (⋃ j : Fin k, (L.pathDrawing j).U))
    {t : unitInterval} (ht : t ∈ Ioo (0 : unitInterval) 1)
    (hpoint : cylinderCurveLiftAt f (cylinderInitialLift k i).2 t ∈
      cylinderCoverStrip L (i.val : ℤ)) : IsClockwiseInitialEdge L i e := by
  let F := cylinderCurveLiftAt f (cylinderInitialLift k i).2
  let A := F '' Ioo (0 : unitInterval) 1
  have hangle : Circle.exp (cylinderInitialLift k i).2 = (f 0).1.2 := by
    rw [hstart]
    rfl
  have hproj (u : unitInterval) : cylinderCoverProjection (F u) = f u :=
    cylinderCoverProjection_curveLiftAt f _ hangle u
  have hconn : IsConnected A :=
    ⟨⟨F t, t, ht, rfl⟩, isPreconnected_Ioo.image F F.continuous.continuousOn⟩
  have hprojA : cylinderCoverProjection '' A = e := by
    rw [image_image]
    have heq : (fun u => cylinderCoverProjection (F u)) = f := funext hproj
    rw [heq, himage]
  have hzero : F 0 = cylinderInitialLift k i := by
    rw [cylinderCurveLiftAt_zero, hstart]
    rfl
  have hinc : cylinderInitialLift k i ∈ closure A := by
    rw [← hzero]
    apply mem_closure_image F.continuous.continuousAt
    rw [closure_Ioo (zero_ne_one : (0 : unitInterval) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  have hsub : A ⊆ cylinderCoverProjection ⁻¹'
      (univ \ ⋃ j : Fin k, (L.pathDrawing j).U) := by
    rintro _ ⟨u, hu, rfl⟩
    change cylinderCoverProjection (F u) ∈ (univ \ ⋃ j : Fin k, (L.pathDrawing j).U)
    rw [hproj]
    refine ⟨mem_univ _, ?_⟩
    have hfu : f u ∈ e := himage ▸ mem_image_of_mem f hu
    exact fun h => disjoint_left.mp hoff hfu h
  refine ⟨A, hconn, hprojA, hinc, ?_⟩
  change A ⊆ connectedComponentIn
    (cylinderCoverProjection ⁻¹' (univ \ ⋃ j : Fin k, (L.pathDrawing j).U)) _
  rw [connectedComponentIn_eq hpoint]
  exact hconn.isPreconnected.subset_connectedComponentIn ⟨t, ht, rfl⟩ hsub

/-- A short access curve from the chosen initial lift into an edge suffices
for the clockwise certificate. Path lifting makes its cover component
project onto the whole edge, without assuming an entire edge lift. -/
theorem isClockwiseInitialEdge_of_lifted_access
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k)
    {e : Set ClosedCylinder} (he : e ∈ G.E)
    (g : Curve CylinderCover) (hg0 : g 0 = cylinderInitialLift k i)
    (hge : ∀ t : unitInterval, 0 < t → cylinderCoverProjection (g t) ∈ e)
    (hoff : Disjoint e (⋃ j : Fin k, (L.pathDrawing j).U))
    (hpoint : g 1 ∈ cylinderCoverStrip L (i.val : ℤ)) : IsClockwiseInitialEdge L i e := by
  let T := cylinderCoverProjection ⁻¹' e
  let A := connectedComponentIn T (g 1)
  have hseed : g 1 ∈ T := hge 1 zero_lt_one
  have hA : IsConnected A :=
    ⟨⟨g 1, mem_connectedComponentIn hseed⟩, isPreconnected_connectedComponentIn⟩
  have hAT : A ⊆ T := connectedComponentIn_subset _ _
  have hprojA : cylinderCoverProjection '' A = e := by
    apply subset_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hAT hx
    · intro y hy
      obtain ⟨p, hp⟩ := he.2.2.1.joinedIn _ hseed _ hy
      let f : Curve ClosedCylinder := p.toContinuousMap
      have hf0 : f 0 = cylinderCoverProjection (g 1) := p.source
      have hf1 : f 1 = y := p.target
      have hangle : Circle.exp (g 1).2 = (f 0).1.2 := by rw [hf0]; rfl
      let F := cylinderCurveLiftAt f (g 1).2
      have hF0 : F 0 = g 1 := by
        rw [cylinderCurveLiftAt_zero, hf0]
        rfl
      have hproj (u : unitInterval) : cylinderCoverProjection (F u) = f u :=
        cylinderCoverProjection_curveLiftAt f _ hangle u
      have hFT : range F ⊆ T := by
        rintro _ ⟨u, rfl⟩
        change cylinderCoverProjection (F u) ∈ e
        rw [hproj]
        exact hp u
      have hFA : range F ⊆ A :=
        (isPreconnected_range F.continuous).subset_connectedComponentIn ⟨0, hF0⟩ hFT
      exact ⟨F 1, hFA (mem_range_self 1), (hproj 1).trans hf1⟩
  have hBA : g '' Ioi (0 : unitInterval) ⊆ A := by
    have hsub : g '' Ioi (0 : unitInterval) ⊆ T := by
      rintro _ ⟨u, hu, rfl⟩
      exact hge u hu
    exact (isPreconnected_Ioi.image g g.continuous.continuousOn).subset_connectedComponentIn
      ⟨1, zero_lt_one, rfl⟩ hsub
  have hinc : cylinderInitialLift k i ∈ closure A := by
    rw [← hg0]
    apply closure_mono hBA
    apply mem_closure_image g.continuous.continuousAt
    rw [closure_Ioi' (⟨1, zero_lt_one⟩ : (Ioi (0 : unitInterval)).Nonempty)]
    exact le_rfl
  have hsub : A ⊆ cylinderCoverProjection ⁻¹'
      (univ \ ⋃ j : Fin k, (L.pathDrawing j).U) := by
    intro x hx
    exact ⟨mem_univ _, fun h => disjoint_left.mp hoff (hAT hx) h⟩
  refine ⟨A, hA, hprojA, hinc, ?_⟩
  change A ⊆ connectedComponentIn
    (cylinderCoverProjection ⁻¹' (univ \ ⋃ j : Fin k, (L.pathDrawing j).U)) _
  rw [connectedComponentIn_eq hpoint]
  exact hA.isPreconnected.subset_connectedComponentIn (mem_connectedComponentIn hseed) hsub

end GraphMinor.GM06
