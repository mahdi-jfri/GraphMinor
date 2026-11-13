module

public import GraphMinor.GM02.PortRouteVertices
public import GraphMinor.GM02.PortEdgeResources
public import GraphMinor.GM02.PortEdgeConnectivity
import GraphMinor.GM02.FeasiblePathSupport

/-!
# A split path inside one route's reserved vertices

Join the two chosen terminal edges through the copies of the route's
inner vertices. Work in the subgraph induced by its reserved set, then
extract a simple path. Mapping the path to the full split graph keeps
its support inside that set, which gives disjointness between routes.
-/

set_option backward.isDefEq.respectTransparency.types false

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- One host route yields a prescribed split path inside its reserved vertex set. -/
theorem exists_portRoute_path {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) (i : Fin k)
    (inner : List α) (W : GraphWalk G (ends i).1 (ends i).2)
    (hs : W.support = (ends i).1 :: (inner ++ [(ends i).2]))
    (hinner : ∀ y ∈ inner, y ∈ V(G) \ V(H))
    (hedges : ∀ e ∈ W.edges, e ∈ E(G))
    (hchoice : ∀ side, (choice.edge (i, side)).val ∈ W.edges) :
    ∃ P : PairPath (pathGraph (portGraph G H choice)) (portPair G H choice i).val,
      P.vertices ⊆ portRouteVertices inner W.edges i := by
  let S := portRouteVertices inner W.edges i
  let F := (portGraph G H choice).induce S
  have hS : S ⊆ V(portGraph G H choice) :=
    portRouteVertices_subset G H inner W.edges i hinner hedges
  have hFG : F ≤ portGraph G H choice := (portGraph G H choice).induce_le hS
  have hAdj : ∀ a b, (portGraph G H choice).Adj a b → a ∈ S → b ∈ S → a ≠ b →
      (pathGraph F).Adj a b := by
    intro a b hab ha hb hne
    obtain ⟨e, he⟩ := hab
    exact ⟨⟨e, he, ha, hb⟩, hne⟩
  have hInc : ∀ e ∈ W.edges, ∀ y ∈ inner, G.Inc e y →
      (pathGraph F).Adj (portEdge e) (portOld y) := by
    intro e he y hy hi
    apply hAdj
    · apply (portGraph_adj_iff G H choice _ _).2
      exact ⟨Or.inr (Or.inl ⟨e, hedges e he, rfl⟩), Or.inl ⟨y, hinner y hy, rfl⟩, hi⟩
    · exact (portEdge_mem_routeVertices inner W.edges i e).2 he
    · exact (portOld_mem_routeVertices inner W.edges i y).2 hy
    · simp [portEdge, portOld]
  have hterminal : ∀ side, (pathGraph F).Adj (portTerminal (i, side))
      (portEdge (choice.edge (i, side)).val) := by
    intro side
    apply hAdj
    · exact (portTerminal_adj_portEdge_iff G H choice (i, side) _).2 rfl
    · exact (portTerminal_mem_routeVertices inner W.edges i (i, side)).2 rfl
    · exact (portEdge_mem_routeVertices inner W.edges i _).2 (hchoice side)
    · simp [portTerminal, portEdge]
  have hmid := portEdges_reachable_of_route (pathGraph F) W inner hs hInc
    _ (hchoice false) _ (hchoice true)
  have hr : (pathGraph F).Reachable (portTerminal (i, false)) (portTerminal (i, true)) :=
    (hterminal false).reachable.trans (hmid.trans (hterminal true).symm.reachable)
  obtain ⟨w, hw⟩ := hr.exists_isPath
  let P : PairPath (pathGraph F) s(portTerminal (i, false), portTerminal (i, true)) :=
    ⟨_, _, rfl, w, hw⟩
  have hP : P.vertices ⊆ S := P.vertices_subset (by simp [portTerminal])
  refine ⟨P.mapLe hFG, ?_⟩
  intro a ha
  exact hP ((PairPath.vertices_mapLe hFG P).le ha)

end GraphMinor.GM02
