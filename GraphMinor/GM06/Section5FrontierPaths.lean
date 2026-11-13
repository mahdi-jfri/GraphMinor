module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM06.Section5RegionWalkTools
import GraphMinor.GM06.Section5WalkSubpaths
public import GraphMinor.GM11.RegionCount
import GraphMinor.GM06.Section5WalkAvoidEdge
import GraphMinor.GM11.PerimeterCount

/-!
# Paths along a region frontier

For the region argument of VI (5.1), page 129, the walk around an
open-disc region visits all frontier vertices. Extracting a simple
path between two of them keeps every support vertex and every edge
on the frontier. We prove this directly from the tracing curve of
the region walk.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

/-- Two distinct frontier vertices of an open-disc region in a sphere
are joined by a path along that frontier. -/
theorem exists_subpath_in_region_frontier
    {S : Type u} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {G : Drawing S} (hG : G.IsTwoCell) (hE : G.E.Nonempty)
    {r : Set S} (hr : r ∈ G.R) {a b : S}
    (ha : a ∈ G.V ∩ frontier r) (hb : b ∈ G.V ∩ frontier r) (hab : a ≠ b) :
    ∃ P : Drawing S, IsSubpathOf G P a b ∧ P.U ⊆ frontier r := by
  let : T2Space S := hS.2.1
  obtain ⟨u, W, h, _, _, _, hrange, _, hrun, _⟩ := exists_region_walk hS hsph hG hE hr
  have hsupport (x : S) (hx : x ∈ G.V ∩ frontier r) : x ∈ W.support := by
    obtain ⟨z, hz⟩ := hrange.symm ▸ hx.2
    obtain ⟨t, ht, hzt⟩ := exists_collar_time z
    have hφ : collarCurve h t = x := by
      change h (Circle.exp (2 * Real.pi * t), 0) = x
      rw [← hzt]
      exact hz
    have htV : collarCurve h t ∈ G.V := hφ.symm ▸ hx.1
    have hxW := vertex_mem_support_of_runsAlongOn W hrun t ⟨ht.1, ht.2.le⟩ htV
    rwa [hφ] at hxW
  have hφfront : ∀ t ∈ Icc (0 : ℝ) 1, collarCurve h t ∈ frontier r := by
    intro t _
    rw [← hrange]
    exact ⟨Circle.exp (2 * Real.pi * t), rfl⟩
  have hparts := support_edges_subset_of_runsAlongOn W hrun hφfront
  obtain ⟨P, hP, hPV, hPE⟩ := exists_subpath_of_walk_support G W (hsupport a ha) (hsupport b hb) hab
  refine ⟨P, hP, ?_⟩
  rw [P.U_eq]
  apply union_subset
  · intro x hx
    exact hparts.1 x (hPV hx)
  · apply iUnion₂_subset
    intro e he
    exact closure_minimal (hparts.2 e (hPE he)) isClosed_frontier

/-- The frontier path can avoid an edge having at most one side in
the region. In VI (5.1) this leaves out the added initial cuff edge. -/
theorem exists_subpath_in_region_frontier_avoiding_one_sided_edge
    {S : Type u} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {G : Drawing S} (hG : G.IsTwoCell) (hE : G.E.Nonempty)
    {r : Set S} (hr : r ∈ G.R) {a b : S}
    (ha : a ∈ G.V ∩ frontier r) (hb : b ∈ G.V ∩ frontier r) (hab : a ≠ b)
    {e : Set S} (he : e ∈ G.E) (hone : ¬ IsTwoSided r e) :
    ∃ P : Drawing S, IsSubpathOf G P a b ∧ P.U ⊆ frontier r ∧ e ∉ P.E := by
  classical
  let : T2Space S := hS.2.1
  obtain ⟨u, W, h, _, _, _, hrange, _, hrun, hcount⟩ := exists_region_walk hS hsph hG hE hr
  have hsupport (x : S) (hx : x ∈ G.V ∩ frontier r) : x ∈ W.support := by
    obtain ⟨z, hz⟩ := hrange.symm ▸ hx.2
    obtain ⟨t, ht, hzt⟩ := exists_collar_time z
    have hφ : collarCurve h t = x := by
      change h (Circle.exp (2 * Real.pi * t), 0) = x
      rw [← hzt]
      exact hz
    have htV : collarCurve h t ∈ G.V := hφ.symm ▸ hx.1
    have hxW := vertex_mem_support_of_runsAlongOn W hrun t ⟨ht.1, ht.2.le⟩ htV
    rwa [hφ] at hxW
  have hφfront : ∀ t ∈ Icc (0 : ℝ) 1, collarCurve h t ∈ frontier r := by
    intro t _
    rw [← hrange]
    exact ⟨Circle.exp (2 * Real.pi * t), rfl⟩
  have hparts := support_edges_subset_of_runsAlongOn W hrun hφfront
  have hce : W.edges.count e ≤ 1 := by
    change edgeCount W.edges e ≤ 1
    rw [hcount e he]
    split_ifs <;> simp_all
  obtain ⟨P, hP, hPV, hPE, hnot⟩ := exists_subpath_avoiding_edge_of_closed_walk G W e hce
    (hsupport a ha) (hsupport b hb) hab
  refine ⟨P, hP, ?_, hnot⟩
  rw [P.U_eq]
  apply union_subset
  · intro x hx
    exact hparts.1 x (hPV hx)
  · apply iUnion₂_subset
    intro f hf
    exact closure_minimal (hparts.2 f (hPE hf)) isClosed_frontier

end GraphMinor.GM06
