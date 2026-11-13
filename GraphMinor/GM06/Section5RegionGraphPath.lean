module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5GapEdge
import GraphMinor.GM06.Section5AdjoinedEdges
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section5AdjoinBoundary
import GraphMinor.GM06.Section5BoundaryConnected
import GraphMinor.GM06.Section5RegionClosureAvoid
import GraphMinor.GM06.Section5InitialEdgeExclusion
import GraphMinor.GM06.Section5TerminalEdge
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section5Red
import GraphMinor.GM11.Walks

/-!
# Following a linkage region in the original graph

In the proof of VI (5.1), page 129, suppose Rᵢ meets Pᵢ only at sᵢ.
Adjoin the cuffs and follow the region boundary from sᵢ to sᵢ₊₁,
avoiding the added edge across their initial gap. No other initial
cuff edge is in the region closure. A terminal cuff edge would put
the end of Pᵢ in that closure. Thus the path uses only original edges.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- A cyclic successor is distinct from its index when at least two
indices are present. -/
theorem finSuccCycle_ne_of_one_lt {k : ℕ} (hk : 1 < k) (i : Fin k) :
    finSuccCycle i ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  simp only [finSuccCycle] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

/-- The region-boundary path in VI (5.1), page 129, can be taken in G
once the region meets Pᵢ only at sᵢ. The two ends are the initial
vertices bordering the gap defining the region. -/
theorem exists_subpath_in_original_region_closure
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hk : 1 < k) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hcontact : closure (cylinderRegion k G i) ∩ (L.pathDrawing i).U ⊆
      {cylinderM1Point k i}) :
    ∃ Q : Drawing ClosedCylinder,
      IsSubpathOf G Q (cylinderM1Point k i) (cylinderM1Point k (finSuccCycle i)) ∧
      Q.U ⊆ closure (cylinderRegion k G i) := by
  obtain ⟨F, hGF, hFU, hFV⟩ := exists_drawing_adjoining_boundary L hG
  have hconn : IsConnected F.U := by
    rw [hFU]
    exact isConnected_union_boundary_of_no_section5_reduction L hG hno
  obtain ⟨e, he, _, _, heBd, _, _, _, hgap⟩ :=
    exists_added_initial_gap_edge hG hGF hFU hFV i
  have hsV (j : Fin k) : cylinderM1Point k j ∈ G.V :=
    (L.isSubdrawing j).1.1 (isPathDrawing_end_vertices (L.isPath j)).1
  have hs := initial_vertices_mem_closure_cylinderRegion hG i
  have hne : cylinderM1Point k i ≠ cylinderM1Point k (finSuccCycle i) := by
    intro heq
    exact finSuccCycle_ne_of_one_lt hk i ((cylinderM1Point_injective hG.1 heq).symm)
  obtain ⟨Q, hQ, hQR, heQ⟩ := exists_subpath_in_region_closure_avoiding_cuff_edge
    hFU hFV hconn (cylinderRegion_mem_regions hG i)
    ⟨hsV i, hs.1⟩ ⟨hsV (finSuccCycle i), hs.2⟩ hne he heBd
  have hterm : L.curve i 1 ∉ closure (cylinderRegion k G i) := by
    intro ht
    have htU : L.curve i 1 ∈ (L.pathDrawing i).U :=
      (L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).2
    have heq := mem_singleton_iff.mp (hcontact ⟨ht, htU⟩)
    exact isPathDrawing_start_ne_end (L.isPath i) heq.symm
  have hQG : Q.IsSubdrawing G := by
    constructor
    · intro x hx
      rw [← hFV]
      exact hQ.1.1 hx
    · intro d hd
      have hdF := hQ.1.2 hd
      rcases edge_mem_or_subset_boundary_of_adjoining hGF hFU hFV hdF with hdG | hdBd
      · exact hdG
      · rcases edge_subset_one_cuff_of_subset_boundary hdF hdBd with hdC | hdC
        · exact False.elim ((not_subset_initial_cuff_of_avoids_gap_edge L hG hθ hFV i
            hQ.1 hQR he hgap heQ hd) hdC)
        · have hdR : d ⊆ closure (cylinderRegion k G i) :=
            fun _ hx => hQR ((hd.2.1 hx).1)
          have ht := curve_one_mem_closure_of_terminal_cuff_edge L hG hθ hFU hFV i hdF hdC
            (hdR.trans (closure_mono (cylinderRegion_subset_strip L i)))
          exact False.elim (hterm (closure_minimal hdR isClosed_closure ht))
  exact ⟨Q, ⟨hQG, hQG.U_subset, hQ.2.2⟩, hQR⟩

end GraphMinor.GM06
