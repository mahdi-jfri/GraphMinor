module

public import GraphMinor.GM02.TopologicalContainment
public import GraphMinor.GM11.Defs
import GraphMinor.GM11.Walks

/-!
# Orienting edge-labelled routes

A pattern edge can be traversed in either direction. Reverse its host
walk when its prescribed ends are in the reverse order. Its interior
and edge lists then reverse together. This preserves all membership,
disjointness, and absence of repetitions needed when routes are glued
through the next suppressed vertex.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- Orient a host route by either ordering of the ends of its pattern edge. -/
theorem exists_oriented_edgeRoute {α : Type u} {β : Type v} {K M : Graph α β}
    {f : β} {a b p q : α} (hab : M.IsLink f a b) (hpq : M.IsLink f p q)
    (inner : List α) (W : GraphWalk K a b)
    (hs : W.support = a :: (inner ++ [b])) :
    ∃ (inner' : List α) (W' : GraphWalk K p q),
      W'.support = p :: (inner' ++ [q]) ∧
      ((inner' = inner ∧ W'.edges = W.edges) ∨
        (inner' = inner.reverse ∧ W'.edges = W.edges.reverse)) := by
  rcases hab.eq_and_eq_or_eq_and_eq hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨inner, W, hs, Or.inl ⟨rfl, rfl⟩⟩
  · refine ⟨inner.reverse, W.reverse, ?_, Or.inr ⟨rfl, GraphWalk.edges_reverse W⟩⟩
    rw [GraphWalk.support_reverse, hs]
    simp

/-- Orientation preserves the route geometry and exact membership in both lists. -/
theorem exists_oriented_edgeRoute_properties {α : Type u} {β : Type v} {K M : Graph α β}
    {f : β} {a b p q : α} (hab : M.IsLink f a b) (hpq : M.IsLink f p q)
    (inner : List α) (W : GraphWalk K a b) (S : Set α)
    (hs : W.support = a :: (inner ++ [b]))
    (hn : inner.Nodup) (hout : ∀ y ∈ inner, y ∈ S)
    (heN : W.edges.Nodup) (heNon : W.edges ≠ []) :
    ∃ (inner' : List α) (W' : GraphWalk K p q),
      W'.support = p :: (inner' ++ [q]) ∧ inner'.Nodup ∧
      (∀ y ∈ inner', y ∈ S) ∧ W'.edges.Nodup ∧ W'.edges ≠ [] ∧
      (∀ y, y ∈ inner' ↔ y ∈ inner) ∧ (∀ e, e ∈ W'.edges ↔ e ∈ W.edges) := by
  obtain ⟨inner', W', hs', hcase⟩ := exists_oriented_edgeRoute hab hpq inner W hs
  refine ⟨inner', W', hs', ?_⟩
  rcases hcase with ⟨rfl, hE⟩ | ⟨rfl, hE⟩
  · exact ⟨hn, hout, hE.symm ▸ heN, hE.symm ▸ heNon, fun _ => Iff.rfl,
      fun e => by rw [hE]⟩
  · refine ⟨List.nodup_reverse.2 hn, ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy
      exact hout y (List.mem_reverse.1 hy)
    · rw [hE]
      exact List.nodup_reverse.2 heN
    · rw [hE]
      intro h
      exact heNon (List.reverse_injective h)
    · intro y
      exact List.mem_reverse
    · intro e
      rw [hE, List.mem_reverse]

/-- Gluing two host routes inserts exactly their common pattern vertex. -/
theorem edgeRoute_append_support {α : Type u} {β : Type v} {K : Graph α β}
    {a x b : α} (l₁ l₂ : List α) (W₁ : GraphWalk K a x) (W₂ : GraphWalk K x b)
    (h₁ : W₁.support = a :: (l₁ ++ [x])) (h₂ : W₂.support = x :: (l₂ ++ [b])) :
    (W₁.append W₂).support = a :: ((l₁ ++ x :: l₂) ++ [b]) := by
  rw [GraphWalk.support_append, h₁, h₂]
  simp [List.append_assoc]

end GraphMinor.GM02
