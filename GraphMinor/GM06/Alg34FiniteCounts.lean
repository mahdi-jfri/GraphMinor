module

public import GraphMinor.GM06.Alg34GapInducedBaseRep
public import GraphMinor.GM06.Alg34ComponentRep
import GraphMinor.GM06.DiscRegions
import GraphMinor.GM11.Regions

/-!
# Finite counts and connectivity of represented drawing arrays

The supplied bijections identify the finite array counts with the
vertex, edge and region counts of the drawing. The proved geometric
region monotonicity therefore bounds the computed region count after
any induced deletion. Connected drawings also give preconnected finite
endpoint graphs through the explicit reachability interpretation.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- The supplied vertex count is the number of vertices in its interpretation. -/
theorem vertices_ncard (h : GM06DrawingRep x G Δ) : G.V.ncard = x.n := by
  simpa only [Nat.card_fin, Nat.card_coe_set_eq] using (Nat.card_congr h.vertex).symm

/-- The supplied edge count is the number of edges in its interpretation. -/
theorem edges_ncard (h : GM06DrawingRep x G Δ) : G.E.ncard = x.ends.length := by
  simpa only [Nat.card_fin, Nat.card_coe_set_eq] using (Nat.card_congr h.edge).symm

/-- The supplied region count is the number of regions in its interpretation. -/
theorem regions_ncard (h : GM06DrawingRep x G Δ) : G.R.ncard = x.regions.length := by
  simpa only [Nat.card_fin, Nat.card_coe_set_eq] using (Nat.card_congr h.region).symm

/-- Geometric connectivity implies preconnectedness of the finite endpoint graph. -/
theorem vertexGraph_preconnected (h : GM06DrawingRep x G Δ)
    (hc : IsGraphConnected G.toGraph) : x.vertexGraph.Preconnected := by
  intro a b
  exact (h.vertex_reachable_iff a b).mpr
    (hc.2 _ (h.vertex a).property _ (h.vertex b).property)

/-- A nonempty represented proper disc drawing has at least one supplied region. -/
theorem regions_pos_of_vertices (h : GM06DrawingRep x G Δ)
    (hS : IsClosedDiscSpace S) (hp : G.IsProper) (hn : 0 < x.n) :
    0 < x.regions.length := by
  let v : Fin x.n := ⟨0, hn⟩
  obtain ⟨p, _, hpU⟩ := disc_exists_notMem_U hS hp isOpen_univ
    (show (Set.univ : Set S).Nonempty from ⟨(h.vertex v).val, trivial⟩)
  obtain ⟨r, hr, _⟩ := GM11.exists_region_of_notMem hpU
  have hi := (h.region.symm ⟨r, hr⟩).isLt
  omega

/-- Induced deletion on a represented proper disc cannot increase region count. -/
theorem inducedData_regions_le [T1Space S] (h : GM06DrawingRep x G Δ)
    (hS : IsClosedDiscSpace S) (hp : G.IsProper) (vs : List (Fin x.n)) :
    (x.inducedData vs).regions.length ≤ x.regions.length := by
  have hn := (h.inducedGapBaseRep vs).regions_ncard
  rw [← hn, ← h.regions_ncard]
  exact disc_region_ncard_le_of_isSubdrawing hS hp
    (induceDrawing_isSubdrawing G (h.vertexImage_subset vs))

/-- Induced deletion cannot increase the sum of vertices and regions. -/
theorem inducedData_vertices_regions_le [T1Space S] (h : GM06DrawingRep x G Δ)
    (hS : IsClosedDiscSpace S) (hp : G.IsProper) (vs : List (Fin x.n)) :
    (x.inducedData vs).n + (x.inducedData vs).regions.length ≤ x.n + x.regions.length := by
  have hr := h.inducedData_regions_le hS hp vs
  have hn : (x.inducedData vs).n ≤ x.n := by
    simpa only [GM06DrawingData.inducedData_n, GM06DrawingData.activeVertices,
      List.length_finRange] using
      (List.length_filter_le (fun v => decide (v ∈ vs)) (List.finRange x.n))
  omega

end GraphMinor.Compute.GM06DrawingRep
