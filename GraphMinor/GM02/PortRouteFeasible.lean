module

public import GraphMinor.GM02.PortRoutePath
public import GraphMinor.GM02.RouteEndpointEdges

/-!
# Feasible split paths from disjoint host routes

Choose an incident edge at each end of each route. Inside the route's
reserved vertex set, extract the prescribed split path. These reserved
sets are disjoint, so the resulting paths give feasibility of the split
termination. This works also for an empty edge set and isolated branches.
-/

set_option backward.isDefEq.respectTransparency.types false

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

private theorem walk_edge_mem {α : Type u} {β : Type v} {G : Graph α β}
    {a b : α} (W : GraphWalk G a b) {e : β} (he : e ∈ W.edges) : e ∈ E(G) := by
  induction W with
  | nil => exact (List.not_mem_nil he).elim
  | cons h rest ih =>
    rcases List.mem_cons.1 he with heq | he
    · exact heq ▸ h.edge_mem
    · exact ih he

/-- Disjoint edge-labelled host routes give a feasible corrected split choice. -/
theorem exists_portFeasible_of_routes {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    (ends : Fin k → α × α) (inner : Fin k → List α)
    (W : ∀ i, GraphWalk G (ends i).1 (ends i).2)
    (hends : ∀ i, (ends i).1 ∈ V(H))
    (hNoLoop : ∀ e a, a ∈ V(H) → ¬G.IsLoopAt e a)
    (hs : ∀ i, (W i).support = (ends i).1 :: (inner i ++ [(ends i).2]))
    (hout : ∀ i y, y ∈ inner i → y ∈ V(G) \ V(H))
    (heN : ∀ i, (W i).edges.Nodup) (heNon : ∀ i, (W i).edges ≠ [])
    (hDis : ∀ i j, i ≠ j →
      Disjoint {y | y ∈ inner i} {y | y ∈ inner j} ∧
      Disjoint {e | e ∈ (W i).edges} {e | e ∈ (W j).edges}) :
    ∃ choice : PortChoice G ends,
      (portTermination G H choice).Feasible (portGraph G H choice) := by
  obtain ⟨choice, hchoice⟩ := exists_portChoice_of_routes G H ends W hends hNoLoop heN heNon
  have hpaths : ∀ i, ∃ P : PairPath (pathGraph (portGraph G H choice)) (portPair G H choice i).val,
      P.vertices ⊆ portRouteVertices (inner i) (W i).edges i := by
    intro i
    exact exists_portRoute_path G H choice i (inner i) (W i) (hs i) (hout i)
      (fun e he => walk_edge_mem (W i) he) (fun side => hchoice (i, side))
  choose paths hbound using hpaths
  have hindex : ∀ p : {p // p ∈ (portTermination G H choice).pairs}, ∃ i, portPair G H choice i = p := by
    intro p
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 p.property
    exact ⟨i, Subtype.ext hi⟩
  choose index hindex using hindex
  let P : ∀ p : {p // p ∈ (portTermination G H choice).pairs},
      PairPath (pathGraph (portGraph G H choice)) p.val := fun p =>
    { start := (paths (index p)).start
      finish := (paths (index p)).finish
      ends_eq := (paths (index p)).ends_eq.trans (congrArg Subtype.val (hindex p))
      walk := (paths (index p)).walk
      isPath := (paths (index p)).isPath }
  refine ⟨choice, P, ?_⟩
  intro p q hpq
  have hij : index p ≠ index q := by
    intro heq
    exact hpq ((hindex p).symm.trans ((congrArg (portPair G H choice) heq).trans (hindex q)))
  have hd := portRouteVertices_disjoint inner (fun i => (W i).edges) (index p) (index q) hij
    (hDis _ _ hij).1 (hDis _ _ hij).2
  rw [Set.disjoint_left]
  intro a ha hb
  exact Set.disjoint_left.1 hd (hbound (index p) ha) (hbound (index q) hb)

end GraphMinor.GM02
