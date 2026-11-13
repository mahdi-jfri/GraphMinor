module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5InitialOldRegionEdges
import GraphMinor.GM06.Section5GapEdge
import GraphMinor.GM06.Section5AdjoinedEdges
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5AdjoinBoundary
import GraphMinor.GM06.Section5BoundaryConnected
import GraphMinor.GM06.Section5RegionClosureAvoid
import GraphMinor.GM06.Section5InitialEdgeExclusion
import GraphMinor.GM06.Section5RegionGraphPath
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# The unique original edge starting along the initial region

For the boundary-contact step of VI (5.1), page 129, follow the
boundary of Rᵢ from sᵢ to the next initial vertex, avoiding the added
cuff-gap edge. The first edge cannot be on either cuff, so it belongs
to the original graph. The region-incidence bound makes it the
unique original edge at sᵢ incident with Rᵢ.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

private theorem exists_nonloop_first_edge
    {P : Drawing ClosedCylinder} {s t : ClosedCylinder} (hP : IsPathDrawing P s t) :
    ∃ e ∈ P.E, ∃ v, v ≠ s ∧ P.toGraph.IsLink e s v := by
  obtain ⟨W, hW, _, _⟩ := hP.1
  cases W with
  | nil _ => exact False.elim ((isPathDrawing_start_ne_end hP) rfl)
  | @cons s v t e hl R =>
    refine ⟨e, hl.1, v, ?_, hl⟩
    intro hvs
    exact (List.nodup_cons.mp hW).1 (hvs ▸ R.start_mem_support)

/-- In the unreduced situation of VI (5.1), there is a unique
original edge at sᵢ incident with Rᵢ, and it is a non-loop edge. -/
theorem exists_unique_initial_region_edge
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k) :
    ∃ e ∈ G.E, ∃ v, v ≠ cylinderM1Point k i ∧
      G.toGraph.IsLink e (cylinderM1Point k i) v ∧ e ⊆ closure (cylinderRegion k G i) ∧
      ∀ f ∈ G.E, cylinderM1Point k i ∈ closure f →
        f ⊆ closure (cylinderRegion k G i) → f = e := by
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
  obtain ⟨Q, hQ, hQR, haQ⟩ := exists_subpath_in_region_closure_avoiding_cuff_edge hFU hFV hconn
    (cylinderRegion_mem_regions hG i) ⟨hsV i, hs.1⟩ ⟨hsV _, hs.2⟩ hne ha haBd
  obtain ⟨e, heQ, v, hvs, hlQ⟩ := exists_nonloop_first_edge hQ.2.2
  have heF : e ∈ F.E := hQ.1.2 heQ
  have hlF := (hQ.1.isLink_iff heQ).mp hlQ
  have hscl : cylinderM1Point k i ∈ closure e :=
    (show cylinderM1Point k i ∈ closure e ∩ F.V from hlF.2.2.2.symm ▸ mem_insert _ {v}).1
  have heR : e ⊆ closure (cylinderRegion k G i) :=
    fun x hx => hQR ((heQ.2.1 hx).1)
  have heG : e ∈ G.E := by
    rcases edge_mem_or_subset_boundary_of_adjoining hGF hFU hFV heF with heG | heBd
    · exact heG
    · rcases edge_subset_one_cuff_of_subset_boundary heF heBd with heC | heC
      · exact False.elim ((not_subset_initial_cuff_of_avoids_gap_edge L hG hθ hFV i
          hQ.1 hQR ha hgap haQ heQ) heC)
      · have hclosed : IsClosed cylinderCuff2 := isClosed_eq
          (continuous_fst.comp continuous_subtype_val) continuous_const
        have hs2 : cylinderM1Point k i ∈ cylinderCuff2 := closure_minimal heC hclosed hscl
        have hbad : (1 : ℝ) = 2 := hs2
        norm_num at hbad
  refine ⟨e, heG, v, hvs, (hGF.isLink_iff heG).mpr hlF, heR, ?_⟩
  intro f hf hsf hfR
  exact eq_of_initial_old_region_edges L hk hG hno i hf heG hsf hscl hfR heR

end GraphMinor.GM06
