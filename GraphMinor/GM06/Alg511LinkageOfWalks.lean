module

public import GraphMinor.GM06.Alg511FlowPaths
import GraphMinor.GM06.Section5
import GraphMinor.GM06.Section5Red
import Mathlib.Tactic

/-!
# Assembling chosen path walks into the initial linkage

For VI (5.11), page 134, the edge scans may choose among parallel
edges. Keep the selected actual walks when constructing the initial
linkage. Simple walks have injective parametrizations, and disjoint
vertex supports give disjoint path drawings. Thus the resulting
linkage retains each selected path and its computed winding.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Surface GraphMinor.GM11 Set

/-- Simple disjoint actual walks with prescribed cuff ends form a
linkage whose curves parametrize exactly the selected walks. -/
theorem alg511_linkage_of_actual_walks {k : ℕ} (G : Drawing ClosedCylinder)
    (start finish : Fin k → ClosedCylinder)
    (W : ∀ i, GraphWalk G.toGraph (start i) (finish i))
    (hsource : ∀ i, start i = cylinderM1Point k i)
    (htarget : ∀ i, finish i ∈ cylinderM2 k)
    (hsimple : ∀ i, (W i).IsSimple)
    (hdisjoint : ∀ i j, i ≠ j → ∀ v, v ∈ (W i).support → v ∈ (W j).support → False) :
    ∃ L : CylinderLinkage k G, ∀ i,
      L.pathDrawing i = walkDrawing G (W i) ∧
      ParametrizesSet (L.curve i) (walkDrawing G (W i)).U (start i) (finish i) := by
  classical
  have hne : ∀ i, start i ≠ finish i := by
    intro i heq
    obtain ⟨j, hj⟩ := htarget i
    have hp : cylinderM1Point k i = cylinderM2Point k j :=
      (hsource i).symm.trans (heq.trans hj.symm)
    have hr := congrArg cylinderRadius hp
    norm_num [cylinderM1Point, cylinderM2Point] at hr
  let D := fun i => walkDrawing G (W i)
  have hDG : ∀ i, (D i).IsSubdrawing G := fun i => walkDrawing_isSubdrawing G (W i)
  have hpath : ∀ i, IsPathDrawing (D i) (start i) (finish i) :=
    fun i => isPathDrawing_walkDrawing_of_isSimple G (hsimple i) (hne i)
  have hDdisjoint : Pairwise (fun i j => Disjoint (D i).U (D j).U) := by
    intro i j hij
    apply alg511_disjoint_subdrawing_pointSets (hDG i) (hDG j)
    apply disjoint_left.mpr
    intro v hvi hvj
    exact hdisjoint i j hij v (by simpa [D, walkDrawing_V] using hvi)
      (by simpa [D, walkDrawing_V] using hvj)
  choose f hf using fun i => (hpath i).2
  let L : CylinderLinkage k G := {
    pathDrawing := D
    curve := f
    isSubdrawing := fun i => ⟨hDG i, (hDG i).U_subset⟩
    isPath := by
      intro i
      rw [(hf i).2.2.2, ← hsource i]
      exact hpath i
    curve_parametrizes := by
      intro i
      rw [(hf i).2.2.2, ← hsource i]
      exact hf i
    curve_one_mem := by
      intro i
      rw [(hf i).2.2.2]
      exact htarget i
    pairwise_disjoint := hDdisjoint }
  exact ⟨L, fun i => ⟨rfl, hf i⟩⟩

/-- The winding of any selected path is feasible, since the
constructed linkage has the same winding on all its paths. -/
theorem alg511_selected_curve_winding_feasible {k : ℕ} {G : Drawing ClosedCylinder}
    (hk : 0 < k) (L : CylinderLinkage k G) (i : Fin k) :
    IsThetaFeasible k G (windingNumber (L.curve i)) := by
  obtain ⟨theta, htheta⟩ := L.exists_hasTheta hk
  refine ⟨L, ?_⟩
  intro j
  exact (htheta j).trans (htheta i).symm

end GraphMinor.GM06
