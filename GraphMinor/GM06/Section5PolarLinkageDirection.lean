module

public import GraphMinor.GM06.Section5CappedInitialPath
public import GraphMinor.GM06.Section5PolarPathDirection

/-!
# A single linkage direction in the initial rotation

The given path at an initial vertex contributes one rim direction.
Every other linkage path misses that vertex, so radial invariance
makes the whole chart miss those paths. Thus an edge of the linkage
cannot pass the clockwise crossing test. These facts let the finite
scan in VI (5.7), page 133, test all active edges without a separate
geometric disjointness query.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The complete linkage meets an initial polar rim exactly in the
specified direction of its path at that vertex. -/
theorem polar_rim_mem_linkage_iff_eq
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hGF : G.IsSubdrawing F) (i : Fin k)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ)
    (q : Circle) (hq : polarRimMap Φ q ∈ (cylinderSphereDrawing (L.pathDrawing i)).U)
    (w : Circle) :
    polarRimMap Φ w ∈ cylinderToSphere '' (⋃ j, (L.pathDrawing j).U) ↔ w = q := by
  let : LocallyConnectedSpace (OnePoint EuclideanPlane) :=
    IsClosedSurface.locallyConnectedSpace
      (GM11.IsSphere.isClosedSurface (show IsSphere (OnePoint EuclideanPlane) from
        ⟨Homeomorph.refl _⟩)).1
  have hPi := cylinderSphereDrawing_isSubdrawing ((L.isSubdrawing i).1.trans hGF)
  have hf : ParametrizesSet (cylinderSphereCurve (L.curve i))
      (cylinderSphereDrawing (L.pathDrawing i)).U
      (cylinderToSphere (cylinderM1Point k i)) (cylinderToSphere (L.curve i 1)) := by
    rw [cylinderSphereDrawing_U]
    exact cylinderSphereCurve_parametrizesSet (L.curve_parametrizes i)
  obtain ⟨q₀, _, hunique⟩ := exists_unique_polar_rim_direction_of_path hPi _ hf hp
  constructor
  · rintro ⟨y, hy, hyw⟩
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
    have hwj : polarRimMap Φ w ∈ (cylinderSphereDrawing (L.pathDrawing j)).U := by
      rw [cylinderSphereDrawing_U]
      exact ⟨y, hyj, hyw⟩
    by_cases hji : j = i
    · subst j
      exact (hunique w hwj).trans (hunique q hq).symm
    · have hstart : cylinderM1Point k i ∈ (L.pathDrawing i).U := by
        rw [← (L.curve_parametrizes i).2.1]
        exact ⟨0, (L.curve_parametrizes i).2.2.1⟩
      have hmiss : Disjoint (range Φ) (cylinderSphereDrawing (L.pathDrawing j)).U := by
        apply disjoint_polar_chart_subdrawing_of_centre_not_mem
          (cylinderSphereDrawing_isSubdrawing ((L.isSubdrawing j).1.trans hGF)) hp
        rw [cylinderSphereDrawing_U]
        rintro ⟨x, hx, hxs⟩
        have hxi : x = cylinderM1Point k i := injective_cylinderToSphere hxs
        exact disjoint_left.mp (L.pairwise_disjoint hji) (hxi ▸ hx) hstart
      exact False.elim (disjoint_left.mp hmiss (mem_range_self (polarDiscPoint 1 w)) hwj)
  · rintro rfl
    rw [cylinderSphereDrawing_U] at hq
    obtain ⟨y, hy, hyq⟩ := hq
    exact ⟨y, mem_iUnion.mpr ⟨i, hy⟩, hyq⟩

/-- An open drawing edge that meets the linkage is wholly an edge
of one of its paths. Drawing vertices cannot lie in that open edge. -/
theorem edge_subset_linkage_of_not_disjoint
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    {e : Set ClosedCylinder} (he : e ∈ G.E)
    (h : ¬ Disjoint e (⋃ j, (L.pathDrawing j).U)) :
    e ⊆ ⋃ j, (L.pathDrawing j).U := by
  obtain ⟨x, hxe, hxL⟩ := not_disjoint_iff.mp h
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hxL
  have hxV : x ∉ (L.pathDrawing j).V := fun hx =>
    (he.2.1 hxe).2 ((L.isSubdrawing j).1.1 hx)
  obtain ⟨f, hf, hxf⟩ := (L.pathDrawing j).exists_edge_of_mem hxj hxV
  have hef : e = f := G.edge_eq_of_mem he ((L.isSubdrawing j).1.2 hf) hxe hxf
  intro y hy
  exact mem_iUnion.mpr ⟨j, (hf.2.1 (hef ▸ hy)).1⟩

end GraphMinor.GM06
