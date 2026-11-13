module

public import GraphMinor.Compute.GM06Alg34Graph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# The finite graph used to compute drawing components

Ignore parallel copies and self-loops when searching for components.
The supplied endpoint positions still witness every adjacency. Removing
self-loops does not affect reachability: a multigraph walk yields a
simple-graph walk, and each simple adjacency lifts along one of its
supplied edge labels. This is the component computation for VI (3.3).
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

open Surface

/-- The simple adjacency graph of the supplied multigraph endpoints. -/
def vertexGraph (x : GM06DrawingData) : SimpleGraph (Fin x.n) where
  Adj a b := a ≠ b ∧ ∃ e : Fin x.ends.length,
    (a = x.ends[e].1 ∧ b = x.ends[e].2) ∨ (a = x.ends[e].2 ∧ b = x.ends[e].1)
  symm := ⟨by
    rintro a b ⟨hne, e, he⟩
    refine ⟨hne.symm, e, ?_⟩
    exact he.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

instance (x : GM06DrawingData) : DecidableRel x.vertexGraph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ ∃ e : Fin x.ends.length, _))

/-- Every multigraph walk joins reachable labels in the finite component graph. -/
theorem vertexGraph_reachable_of_walk (x : GM06DrawingData) {a b : Fin x.n}
    (W : GraphWalk x.graph a b) : x.vertexGraph.Reachable a b := by
  induction W with
  | nil _ => exact SimpleGraph.Reachable.refl _
  | @cons a b c e he W ih =>
    by_cases hab : a = b
    · exact hab ▸ ih
    · exact (SimpleGraph.Adj.reachable (show x.vertexGraph.Adj a b from ⟨hab, e, he⟩)).trans ih

/-- Each adjacency of the finite component graph has a supplied edge
witness and therefore lifts to a multigraph walk. -/
theorem vertexGraph_walk_of_reachable (x : GM06DrawingData) {a b : Fin x.n}
    (hab : x.vertexGraph.Reachable a b) : Nonempty (GraphWalk x.graph a b) := by
  have hp := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hab
  clear hab
  induction hp with
  | refl => exact ⟨.nil trivial⟩
  | @tail b c hab hbc ih =>
    obtain ⟨W⟩ := ih
    obtain ⟨_, e, he⟩ := hbc
    exact ⟨W.append (.cons he (.nil trivial))⟩

/-- Components computed from finite endpoint adjacency are exactly
components defined by walks of the supplied multigraph. -/
theorem vertexGraph_reachable_iff (x : GM06DrawingData) (a b : Fin x.n) :
    x.vertexGraph.Reachable a b ↔ Nonempty (GraphWalk x.graph a b) :=
  ⟨x.vertexGraph_walk_of_reachable, fun ⟨W⟩ => x.vertexGraph_reachable_of_walk W⟩

end GraphMinor.Compute.GM06DrawingData
