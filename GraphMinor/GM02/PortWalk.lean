module

public import GraphMinor.GM02.PortAlternation
public import GraphMinor.Surface.Defs

/-!
# Collapsing split paths to edge-labelled host walks

Read a split path two steps at a time. The middle vertex names the
host edge, and its two neighbors give that edge's ends. The resulting
walk records exactly the projected vertex list and host-edge list.
-/

set_option backward.isDefEq.respectTransparency.types false

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

private theorem edgeLabel_eq_none_of_label {α : Type u} {β : Type v} {k : ℕ}
    (ends : Fin k → α × α) (a : PortVertex α β k) (x : α)
    (ha : portLabel ends a = some x) : portEdgeLabel a = none := by
  rcases a with (a | e) | p
  · rfl
  · cases ha
  · rfl

/-- Collapsing a split path preserves its complete projected vertex and edge lists. -/
theorem exists_portWalk {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends)
    (S : Set (PortVertex α β k))
    (hvertex : ∀ a ∈ S, ∀ x, portLabel ends a = some x → x ∈ V(G))
    (hlink : ∀ a ∈ S, ∀ b ∈ S, ∀ e x y, a ≠ b →
      (portGraph G H choice).Adj a (portEdge e) →
      (portGraph G H choice).Adj (portEdge e) b →
      portLabel ends a = some x → portLabel ends b = some y → G.IsLink e x y)
    {a b : PortVertex α β k} {x y : α}
    (w : (pathGraph (portGraph G H choice)).Walk a b)
    (hnd : w.support.Nodup) (hs : ∀ c ∈ w.support, c ∈ S)
    (hax : portLabel ends a = some x) (hby : portLabel ends b = some y) :
    ∃ W : Surface.GraphWalk G x y,
      W.support = w.support.filterMap (portLabel ends) ∧
      W.edges = w.support.filterMap portEdgeLabel := by
  have aux : ∀ n a x (w : (pathGraph (portGraph G H choice)).Walk a b),
      w.length = n → w.support.Nodup → (∀ c ∈ w.support, c ∈ S) →
      portLabel ends a = some x →
      ∃ W : Surface.GraphWalk G x y,
        W.support = w.support.filterMap (portLabel ends) ∧
        W.edges = w.support.filterMap portEdgeLabel := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a x w hn hnd hs hax
      cases w with
      | nil =>
        have hxy : x = y := Option.some.inj (hax.symm.trans hby)
        subst y
        refine ⟨.nil (hvertex b (hs b (by simp)) x hax), ?_, ?_⟩
        · simp [Surface.GraphWalk.support, hax]
        · simp [Surface.GraphWalk.edges, edgeLabel_eq_none_of_label ends b x hax]
      | @cons a c b hac rest =>
        obtain ⟨e, rfl⟩ := portAdj_exists_edge G H choice a c x hax hac.1
        cases rest with
        | nil => cases hby
        | @cons _ d _ hed tail =>
          obtain ⟨z, hdz⟩ := portEdge_adj_exists_label G H choice e d hed.1
          have htail : ∀ c ∈ tail.support, c ∈ S := by
            intro c hc
            exact hs c (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr (Or.inr hc))
          have hnd' : tail.support.Nodup := hnd.of_cons.of_cons
          have had : a ≠ d := by
            intro had
            exact (List.nodup_cons.1 hnd).1 (by simp [had])
          have hl := hlink a (hs a (by simp)) d (htail d tail.start_mem_support)
            e x z had hac.1 hed.1 hax hdz
          obtain ⟨W, hWv, hWe⟩ := ih tail.length (by simp only [SimpleGraph.Walk.length_cons] at hn; omega)
            d z tail rfl hnd' htail hdz
          refine ⟨.cons hl W, ?_, ?_⟩
          · change x :: W.support = (a :: portEdge e :: tail.support).filterMap (portLabel ends)
            rw [List.filterMap_cons, hax]
            change x :: W.support = x :: (portEdge e :: tail.support).filterMap (portLabel ends)
            change x :: W.support = x :: tail.support.filterMap (portLabel ends)
            exact congrArg (List.cons x) hWv
          · change e :: W.edges = (a :: portEdge e :: tail.support).filterMap portEdgeLabel
            rw [List.filterMap_cons, edgeLabel_eq_none_of_label ends a x hax]
            change e :: W.edges = e :: tail.support.filterMap portEdgeLabel
            exact congrArg (List.cons e) hWe
  exact aux w.length a x w rfl hnd hs hax

end GraphMinor.GM02
