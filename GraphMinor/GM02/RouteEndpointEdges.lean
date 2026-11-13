module

public import GraphMinor.GM02.PortTermination
public import GraphMinor.Surface.Defs

/-!
# Choosing the incident edges of split terminals

Take the first edge of each host route and an edge at its last end.
When the route is closed, these choices differ: a one-edge closed walk
would be a host loop at a branch vertex, and a longer walk cannot repeat
its first edge. This gives exactly the extra loop condition of the
corrected split choice.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- A nonempty host walk has a traversed edge incident with its last vertex. -/
theorem GraphWalk.exists_end_inc_edge {α : Type u} {β : Type v} {G : Graph α β}
    {a b : α} (W : GraphWalk G a b) (hNon : W.edges ≠ []) :
    ∃ e, G.Inc e b ∧ e ∈ W.edges := by
  induction W with
  | nil => exact (hNon rfl).elim
  | @cons a x b e h rest ih =>
    cases rest with
    | nil => exact ⟨e, h.inc_right, List.mem_cons_self⟩
    | cons h' tail =>
      obtain ⟨f, hf, hm⟩ := ih (List.cons_ne_nil _ _)
      exact ⟨f, hf, List.mem_cons_of_mem _ hm⟩

/-- The ends of a closed route can choose different edges when there is no host loop at its first end. -/
theorem GraphWalk.exists_endpoint_edges {α : Type u} {β : Type v} {G : Graph α β}
    {a b : α} (W : GraphWalk G a b) (hN : W.edges.Nodup) (hNon : W.edges ≠ [])
    (hNoLoop : ∀ e, ¬G.IsLoopAt e a) :
    ∃ e f, G.Inc e a ∧ G.Inc f b ∧ e ∈ W.edges ∧ f ∈ W.edges ∧ (a = b → e ≠ f) := by
  cases W with
  | nil => exact (hNon rfl).elim
  | @cons a x b e h rest =>
    cases rest with
    | nil =>
      refine ⟨e, e, h.inc_left, h.inc_right, List.mem_cons_self, List.mem_cons_self, ?_⟩
      intro hab
      exact (hNoLoop e (hab ▸ h)).elim
    | @cons x z b f h' tail =>
      obtain ⟨g, hg, hm⟩ := GraphWalk.exists_end_inc_edge (GraphWalk.cons h' tail) (List.cons_ne_nil _ _)
      refine ⟨e, g, h.inc_left, hg, List.mem_cons_self, List.mem_cons_of_mem _ hm, ?_⟩
      intro _ heg
      exact (List.nodup_cons.1 hN).1 (heg.symm ▸ hm)

/-- Host routes with no repeated edge supply a split choice, with both selected edges on the corresponding route. -/
theorem exists_portChoice_of_routes {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    (ends : Fin k → α × α) (W : ∀ i, GraphWalk G (ends i).1 (ends i).2)
    (hends : ∀ i, (ends i).1 ∈ V(H))
    (hNoLoop : ∀ e a, a ∈ V(H) → ¬G.IsLoopAt e a)
    (hN : ∀ i, (W i).edges.Nodup) (hNon : ∀ i, (W i).edges ≠ []) :
    ∃ choice : PortChoice G ends, ∀ p : Fin k × Bool, (choice.edge p).val ∈ (W p.1).edges := by
  choose first last hfirst hlast hmfirst hmlast hne using
    (fun i => GraphWalk.exists_endpoint_edges (W i) (hN i) (hNon i)
      (fun e => hNoLoop e (ends i).1 (hends i)))
  let pick : Fin k × Bool → E(G) := fun p =>
    if p.2 then ⟨last p.1, (hlast p.1).edge_mem⟩ else ⟨first p.1, (hfirst p.1).edge_mem⟩
  refine ⟨⟨pick, ?_, ?_⟩, ?_⟩
  · rintro ⟨i, side⟩
    cases side <;> simp only [pick, Bool.false_eq_true, ↓reduceIte]
    · exact hfirst i
    · exact hlast i
  · intro i hi heq
    have he := congrArg Subtype.val heq
    exact hne i hi he
  · rintro ⟨i, side⟩
    cases side <;> simp only [pick, Bool.false_eq_true, ↓reduceIte]
    · exact hmfirst i
    · exact hmlast i

end GraphMinor.GM02
