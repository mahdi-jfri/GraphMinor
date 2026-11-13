module

public import GraphMinor.GM02.PortWalk
import GraphMinor.GM02.OrientPairPath
import GraphMinor.GM02.FeasiblePathSupport

/-!
# Host walks supplied by feasible split paths

Orient each prescribed split path and collapse its two-step segments.
The resulting walk uses each host edge at most once. A host edge occurs
in that walk precisely when its edge vertex occurred on the split path.
This retains the edge information needed for parallel pattern edges.
-/

set_option backward.isDefEq.respectTransparency.types false

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- An edge label determines its split vertex uniquely. -/
theorem portEdgeLabel_eq_some_iff {α : Type u} {β : Type v} {k : ℕ}
    (a : PortVertex α β k) (e : β) : portEdgeLabel a = some e ↔ a = portEdge e := by
  rcases a with (a | f) | p <;> simp [portEdgeLabel, portEdge]

/-- Project a member of a feasible split family, retaining all original edge names. -/
theorem exists_portRoute_with_lists {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends)
    (hVH : V(H) ⊆ V(G)) (hends : ∀ i, (ends i).1 ∈ V(H) ∧ (ends i).2 ∈ V(H))
    (P : ∀ p : {p // p ∈ (portTermination G H choice).pairs}, PairPath (pathGraph (portGraph G H choice)) p.val)
    (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices) (i : Fin k) :
    ∃ (q : (pathGraph (portGraph G H choice)).Path
          (portTerminal (i, false)) (portTerminal (i, true)))
      (W : Surface.GraphWalk G (ends i).1 (ends i).2),
      {a | a ∈ q.val.support} = (P (portPair G H choice i)).vertices ∧
      W.support = q.val.support.filterMap (portLabel ends) ∧
      W.edges = q.val.support.filterMap portEdgeLabel := by
  obtain ⟨q, hq, _⟩ := (P (portPair G H choice i)).exists_oriented_path
  have hv : ∀ a ∈ (P (portPair G H choice i)).vertices, ∀ x,
      portLabel ends a = some x → x ∈ V(G) := by
    intro a ha x hx
    have hd := (portTermination G H choice).not_diag _ (portPair G H choice i).property
    exact portLabel_mem_host G H choice hVH hends a x
      ((P (portPair G H choice i)).vertices_subset hd ha) hx
  have hl : ∀ a ∈ (P (portPair G H choice i)).vertices,
      ∀ b ∈ (P (portPair G H choice i)).vertices, ∀ e x y, a ≠ b →
        (portGraph G H choice).Adj a (portEdge e) →
        (portGraph G H choice).Adj (portEdge e) b →
        portLabel ends a = some x → portLabel ends b = some y → G.IsLink e x y := by
    intro a ha b hb e x y hab hae heb hax hby
    exact port_two_step_isLink G H choice a b e x y hae heb hax hby
      (portPath_labels_ne G H choice hends P hP i a b e x y ha hb hab hae heb hax hby)
  obtain ⟨W, hWv, hWe⟩ := exists_portWalk G H choice _ hv hl q.val q.property.support_nodup
    (fun a ha => hq.le ha) (by rfl) (by rfl)
  exact ⟨q, W, hq, hWv, hWe⟩

/-- Each projected feasible path uses every original host edge at most once. -/
theorem exists_portRoute {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends)
    (hVH : V(H) ⊆ V(G)) (hends : ∀ i, (ends i).1 ∈ V(H) ∧ (ends i).2 ∈ V(H))
    (P : ∀ p : {p // p ∈ (portTermination G H choice).pairs}, PairPath (pathGraph (portGraph G H choice)) p.val)
    (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices) (i : Fin k) :
    ∃ W : Surface.GraphWalk G (ends i).1 (ends i).2,
      W.edges.Nodup ∧
      (∀ e, e ∈ W.edges ↔ portEdge e ∈ (P (portPair G H choice i)).vertices) := by
  obtain ⟨q, W, hq, _, hWe⟩ := exists_portRoute_with_lists G H choice hVH hends P hP i
  refine ⟨W, ?_, ?_⟩
  · rw [hWe]
    refine List.Nodup.filterMap (fun a b e ha hb => ?_) q.property.support_nodup
    have ha' := (portEdgeLabel_eq_some_iff a e).1 ha
    have hb' := (portEdgeLabel_eq_some_iff b e).1 hb
    exact ha'.trans hb'.symm
  · intro e
    rw [hWe, List.mem_filterMap]
    constructor
    · rintro ⟨a, ha, he⟩
      have hae := (portEdgeLabel_eq_some_iff a e).1 he
      exact hae ▸ hq.le ha
    · intro he
      exact ⟨portEdge e, hq.ge he, rfl⟩

end GraphMinor.GM02
