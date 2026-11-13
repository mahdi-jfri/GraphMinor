module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section4SubgraphDrawing

/-!
# The ends of a cylinder linkage

The k disjoint linkage paths have distinct terminal vertices in the
k-element prescribed set on the second cuff. They therefore use every
prescribed terminal vertex. A subdrawing that contains the linkage
retains all prescribed boundary vertices, so it remains an instance of
Section 5. These facts justify the deletions in the proof of VI (5.1).
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Distinct paths of a cylinder linkage have distinct terminal vertices. -/
theorem CylinderLinkage.curve_one_injective
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G) :
    Function.Injective (fun i => L.curve i 1) := by
  intro i j hij
  change L.curve i 1 = L.curve j 1 at hij
  by_contra hne
  have hi : L.curve i 1 ∈ (L.pathDrawing i).U := by
    rw [← (L.curve_parametrizes i).2.1]
    exact mem_range_self 1
  have hj : L.curve i 1 ∈ (L.pathDrawing j).U := by
    rw [hij, ← (L.curve_parametrizes j).2.1]
    exact mem_range_self 1
  exact disjoint_left.mp (L.pairwise_disjoint hne) hi hj

/-- The terminal vertices of a cylinder linkage cover the prescribed
set on the second cuff. -/
theorem CylinderLinkage.curve_one_surjective
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    {x : ClosedCylinder} (hx : x ∈ cylinderM2 k) :
    ∃ i : Fin k, L.curve i 1 = x := by
  classical
  choose j hj using L.curve_one_mem
  have hji : Function.Injective j := by
    intro a b hab
    apply L.curve_one_injective
    exact (hj a).symm.trans ((congrArg (cylinderM2Point k) hab).trans (hj b))
  have hjs : Function.Surjective j := Finite.surjective_of_injective hji
  obtain ⟨r, hr⟩ := hx
  obtain ⟨i, hi⟩ := hjs r
  exact ⟨i, (hj i).symm.trans ((congrArg (cylinderM2Point k) hi).trans hr)⟩

/-- Every drawing containing a cylinder linkage contains all prescribed
boundary vertices. -/
theorem CylinderLinkage.boundary_vertices_subset
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hF : ∀ i, (L.pathDrawing i).IsSubdrawing F) :
    cylinderM1 k ∪ cylinderM2 k ⊆ F.V := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨i, rfl⟩ := hx
    exact (hF i).1 (isPathDrawing_end_vertices (L.isPath i)).1
  · obtain ⟨i, rfl⟩ := L.curve_one_surjective hx
    exact (hF i).1 (isPathDrawing_end_vertices (L.isPath i)).2

/-- A subdrawing containing the linkage has the same boundary vertices
as the original Section 5 drawing, and is itself a Section 5 drawing. -/
theorem isCylinderSection5Drawing_of_contains_linkage
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hFG : F.IsSubdrawing G)
    (hF : ∀ i, (L.pathDrawing i).IsSubdrawing F) :
    IsCylinderSection5Drawing k F := by
  refine ⟨hG.1, isProper_of_isSubdrawing hG.2.1 hFG, Subset.antisymm ?_ ?_⟩
  · intro x hx
    rw [← hG.2.2]
    exact ⟨hFG.1 hx.1, hx.2⟩
  · intro x hx
    refine ⟨L.boundary_vertices_subset hF hx, ?_⟩
    exact (hG.2.2.symm ▸ hx).2

end GraphMinor.GM06
