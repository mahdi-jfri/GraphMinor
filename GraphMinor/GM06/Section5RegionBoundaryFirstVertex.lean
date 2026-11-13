module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5AdjoinBoundary
import GraphMinor.GM06.Section5BoundaryConnected
import GraphMinor.GM06.Section5GapEdge
import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5RegionClosureAvoid
import GraphMinor.GM06.Section5InitialEdgeExclusion
import GraphMinor.GM06.Section5FirstHit
import GraphMinor.GM06.Section5RegionGraphPath
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# Following the region boundary to its first linkage vertex

For the boundary-contact argument in VI (5.1), page 129, adjoin the
cuffs and follow Rᵢ from sᵢ towards sᵢ₊₁, avoiding the added gap edge.
Stop at the first linkage vertex other than sᵢ. Simplicity keeps all
other linkage vertices out of this prefix, and avoiding the gap
excludes every added initial-cuff edge from it.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The region boundary supplies a prefix to its first noninitial
linkage vertex in the drawing with cuffs adjoined. This prefix uses
no initial-cuff edge. -/
theorem exists_region_boundary_prefix_first_linkage_vertex
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k) :
    ∃ (F Q : Drawing ClosedCylinder) (v : ClosedCylinder),
      G.IsSubdrawing F ∧ F.U = G.U ∪ bd ClosedCylinder ∧ F.V = G.V ∧
      v ∈ (⋃ j : Fin k, (L.pathDrawing j).V) ∧ v ≠ cylinderM1Point k i ∧
      IsSubpathOf F Q (cylinderM1Point k i) v ∧
      Q.U ⊆ closure (cylinderRegion k G i) ∧
      Q.V ∩ (⋃ j : Fin k, (L.pathDrawing j).V) ⊆ {cylinderM1Point k i, v} ∧
      ∀ e ∈ Q.E, ¬ e ⊆ cylinderCuff1 := by
  classical
  obtain ⟨F, hGF, hFU, hFV⟩ := exists_drawing_adjoining_boundary L hG
  have hconn : IsConnected F.U := by
    rw [hFU]
    exact isConnected_union_boundary_of_no_section5_reduction L hG hno
  obtain ⟨a, ha, _, _, haBd, _, _, _, hgap⟩ := exists_added_initial_gap_edge hG hGF hFU hFV i
  have hsV (j : Fin k) : cylinderM1Point k j ∈ G.V :=
    (L.isSubdrawing j).1.1 (isPathDrawing_end_vertices (L.isPath j)).1
  have hs := initial_vertices_mem_closure_cylinderRegion hG i
  have hne : cylinderM1Point k i ≠ cylinderM1Point k (finSuccCycle i) := by
    intro heq
    exact finSuccCycle_ne_of_one_lt hk i ((cylinderM1Point_injective hG.1 heq).symm)
  obtain ⟨A, hA, hAR, haA⟩ := exists_subpath_in_region_closure_avoiding_cuff_edge hFU hFV hconn
    (cylinderRegion_mem_regions hG i) ⟨hsV i, hs.1⟩ ⟨hsV _, hs.2⟩ hne ha haBd
  let B := (⋃ j : Fin k, (L.pathDrawing j).V) \ {cylinderM1Point k i}
  have hsNot : cylinderM1Point k i ∉ B := fun h => h.2 rfl
  have htB : cylinderM1Point k (finSuccCycle i) ∈ B :=
    ⟨mem_iUnion.mpr ⟨_, (isPathDrawing_end_vertices (L.isPath (finSuccCycle i))).1⟩, hne.symm⟩
  obtain ⟨v, hvB, Q, hQA, hQV⟩ := exists_subpath_to_vertex_set hA.2.2 hsNot htB
  have hQF := hQA.1.trans hA.1
  have hQR : Q.U ⊆ closure (cylinderRegion k G i) := hQA.2.1.trans hAR
  have haQ : a ∉ Q.E := fun h => haA (hQA.1.2 h)
  refine ⟨F, Q, v, hGF, hFU, hFV, hvB.1, hvB.2,
    ⟨hQF, hQF.U_subset, hQA.2.2⟩, hQR, ?_, ?_⟩
  · rintro x ⟨hxQ, hxL⟩
    by_cases hxs : x = cylinderM1Point k i
    · exact Or.inl hxs
    · exact Or.inr (hQV ⟨hxQ, ⟨hxL, hxs⟩⟩)
  · intro e he
    exact not_subset_initial_cuff_of_avoids_gap_edge L hG hθ hFV i hQF hQR ha hgap haQ he

end GraphMinor.GM06
