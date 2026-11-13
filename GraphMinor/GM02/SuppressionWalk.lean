module

public import GraphMinor.GM02.TopologicalContainment
public import GraphMinor.Surface.Defs
import GraphMinor.GM11.Walks

/-!
# Walks retained or shortened by suppression

A walk avoiding the suppressed vertex uses neither of its incident
edges, so every link and vertex of that walk is retained. Joining the
new replacement edge to such a retained walk shortens a route by one
inner vertex. Both statements retain the precise vertex and edge lists.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- A walk avoiding the suppressed vertex is retained with exactly the same lists. -/
theorem exists_suppression_walk {α : Type u} {β : Type v} {K : Graph α β}
    (d : SuppressionData K) {a b : α} (W : GraphWalk K a b)
    (havoid : d.vertex ∉ W.support) :
    ∃ W' : GraphWalk d.result a b, W'.support = W.support ∧ W'.edges = W.edges := by
  apply W.exists_transfer
  · intro e x y he hxy
    have h₁ : e ≠ d.first := by
      intro h
      subst e
      exact havoid (W.left_mem_support_of_mem_edges he d.first_link)
    have h₂ : e ≠ d.second := by
      intro h
      subst e
      exact havoid (W.left_mem_support_of_mem_edges he d.second_link)
    exact Or.inl ⟨hxy, h₁, h₂⟩
  · intro x hx
    exact ⟨W.mem_vertexSet_of_mem_support hx, fun h => havoid (h ▸ hx)⟩

/-- The replacement edge followed by a retained tail is the shortened route. -/
theorem exists_shortened_suppression_walk {α : Type u} {β : Type v} {K : Graph α β}
    (d : SuppressionData K) {b : α} (tail : GraphWalk K d.right b)
    (havoid : d.vertex ∉ tail.support) :
    ∃ W' : GraphWalk d.result d.left b,
      W'.support = d.left :: tail.support ∧ W'.edges = d.fresh :: tail.edges := by
  obtain ⟨tail', hs, he⟩ := exists_suppression_walk d tail havoid
  have hl : d.result.IsLink d.fresh d.left d.right :=
    Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  exact ⟨.cons hl tail', congrArg (List.cons d.left) hs, congrArg (List.cons d.fresh) he⟩

end GraphMinor.GM02
