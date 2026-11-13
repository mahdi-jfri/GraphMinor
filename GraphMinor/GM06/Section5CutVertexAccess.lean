module

public import GraphMinor.GM06.Section5CutLiftWalk
import GraphMinor.GM06.Section5SinglePathAccess

/-!
# Reaching the boundary core from an interior cut vertex

A cut vertex projecting away from the initial vertex can reach the
linkage in the original graph without passing through that vertex,
by the exclusion of Reduction 2. Lift this walk until its first seam
contact. Its end lies on the cut-disc boundary, and its support
avoids both initial copies. This connects the interior vertices to
the punctured boundary core in the one-path proof of VI (5.1).
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Every cut vertex projecting away from the initial vertex has a
walk to the disc boundary avoiding both initial copies, if Reduction 2 is unavailable. -/
theorem exists_cut_walk_to_boundary_avoiding_initial_of_no_reduction2
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno2 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction2Step 1 G L H M)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    {x : D} (hx : x ∈ F.V) (hxs : radialCylinderProjection x.1 ≠ cylinderM1Point 1 0) :
    ∃ y ∈ bd D, ∃ R : GraphWalk F.toGraph x y,
      ∀ z ∈ R.support, radialCylinderProjection z.1 ≠ cylinderM1Point 1 0 := by
  have hxG : radialCylinderProjection x.1 ∈ G.V := by
    rw [hFV] at hx
    exact hx
  obtain ⟨v, hv, W, hW⟩ := exists_original_walk_to_linkage_avoiding_initial_of_no_reduction2 L hG hno2 hxG hxs
  have hxF : x ∈ F.V := by rw [hFV]; exact hxG
  obtain ⟨y, R, hy, hR⟩ := exists_cut_walk_to_linkage_avoiding_initial L hG hθ hD hBd hstrip
    F hFU hFV hEdges hxF W hv hW
  have hybd : y ∈ bd D := by
    rw [← preimage_boundary_union_path_single_strip L hG hθ hD hBd hstrip]
    exact Or.inr ((L.pathDrawing 0).V_subset_U hy)
  exact ⟨y, hybd, R, hR⟩


/-- Every cut vertex projecting away from the initial vertex has a
walk to the disc boundary whose support avoids both initial copies. -/
theorem exists_cut_walk_to_boundary_avoiding_initial
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    {x : D} (hx : x ∈ F.V) (hxs : radialCylinderProjection x.1 ≠ cylinderM1Point 1 0) :
    ∃ y ∈ bd D, ∃ R : GraphWalk F.toGraph x y,
      ∀ z ∈ R.support, radialCylinderProjection z.1 ≠ cylinderM1Point 1 0 := by
  exact exists_cut_walk_to_boundary_avoiding_initial_of_no_reduction2 L hG hθ
    (fun H M hH h2 => hno ⟨H, M, hH, Or.inr (Or.inl h2)⟩) hD hBd hstrip F hFU hFV hEdges hx hxs

end GraphMinor.GM06
