module

public import GraphMinor.GM02.PortGraph
public import GraphMinor.Surface.Defs
import GraphMinor.GM11.Walks

/-!
# Connecting the edge vertices along a host route

Successive host edges meet at an inner route vertex. Their two split
edge vertices can therefore be joined through that old vertex. Induction
along the host walk joins any two of its edge vertices. This argument
needs no choice of a simple path: a path will be extracted from this
connectivity after the terminal incidences have been added.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- All edge vertices of a host route are connected through the copies of its inner vertices. -/
theorem portEdges_reachable_of_route {α : Type u} {β : Type v} {k : ℕ} {G : Graph α β}
    (F : SimpleGraph (PortVertex α β k)) {a b : α} (W : GraphWalk G a b) (inner : List α)
    (hs : W.support = a :: (inner ++ [b]))
    (hInc : ∀ e ∈ W.edges, ∀ y ∈ inner, G.Inc e y → F.Adj (portEdge e) (portOld y)) :
    ∀ e ∈ W.edges, ∀ f ∈ W.edges, F.Reachable (portEdge e) (portEdge f) := by
  induction W generalizing inner with
  | nil => intro e he; exact (List.not_mem_nil he).elim
  | @cons a x b e₁ h₁ rest ih =>
    cases rest with
    | nil =>
      intro e he f hf
      have he' : e = e₁ := List.mem_singleton.1 he
      have hf' : f = e₁ := List.mem_singleton.1 hf
      subst e; subst f
      exact SimpleGraph.Reachable.refl _
    | @cons x z b e₂ h₂ tail =>
      cases inner with
      | nil =>
        have ht : tail.support = [] := (List.cons.inj (List.cons.inj hs).2).2
        exact (tail.support_ne_nil ht).elim
      | cons y l =>
        have hxy : x = y := (List.cons.inj (List.cons.inj hs).2).1
        subst y
        have htail : tail.support = l ++ [b] := (List.cons.inj (List.cons.inj hs).2).2
        have hrest : (GraphWalk.cons h₂ tail).support = x :: (l ++ [b]) :=
          congrArg (List.cons x) htail
        have hSub : ∀ e ∈ (GraphWalk.cons h₂ tail).edges, e ∈ (GraphWalk.cons h₁ (GraphWalk.cons h₂ tail)).edges :=
          fun e he => List.mem_cons_of_mem _ he
        have hr := ih l hrest (fun e he y hy hi =>
          hInc e (hSub e he) y (List.mem_cons_of_mem _ hy) hi)
        have h₁Adj := hInc e₁ List.mem_cons_self x List.mem_cons_self h₁.inc_right
        have h₂Adj := hInc e₂ (List.mem_cons_of_mem _ List.mem_cons_self) x List.mem_cons_self h₂.inc_left
        have h12 : F.Reachable (portEdge e₁) (portEdge e₂) := h₁Adj.reachable.trans h₂Adj.symm.reachable
        have hfirst : ∀ f ∈ (GraphWalk.cons h₂ tail).edges, F.Reachable (portEdge e₁) (portEdge f) :=
          fun f hf => h12.trans (hr e₂ List.mem_cons_self f hf)
        intro e he f hf
        rcases List.mem_cons.1 he with heq | heTail
        · rw [heq]
          rcases List.mem_cons.1 hf with hfq | hfTail
          · simpa only [hfq] using (SimpleGraph.Reachable.refl (portEdge e₁) : F.Reachable _ _)
          · exact hfirst f hfTail
        · rcases List.mem_cons.1 hf with hfq | hfTail
          · rw [hfq]; exact (hfirst e heTail).symm
          · exact hr e heTail f hfTail

end GraphMinor.GM02
