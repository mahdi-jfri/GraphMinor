module

public import GraphMinor.GM02.TopologicalContainment
public import GraphMinor.Surface.Defs

/-!
# The shortened lists are sublists of the old lists

Removing the first inner vertex leaves a sublist of the old interior.
When the replacement edge reuses the first removed edge's name, the new
edge list is also a sublist. Thus neither shortening introduces repeated
entries or new intersections between different routes.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- The shortened interior of every route is a sublist of its old interior. -/
theorem edgeRoute_inner_sublist {α : Type u} {k : ℕ} (inner : Fin k → List α)
    (i : Fin k) (x : α) (rest : List α) (hi : inner i = x :: rest) (j : Fin k) :
    (if j = i then rest else inner j).Sublist (inner j) := by
  by_cases hji : j = i
  · subst j
    rw [ite_eq_left rfl, hi]
    exact List.Sublist.cons x (List.Sublist.refl rest)
  · rw [ite_eq_right hji]

/-- Reusing the first removed edge name makes every shortened edge list a sublist. -/
theorem edgeRoute_edge_sublist {α : Type u} {β : Type v} {k : ℕ} {K : Graph α β}
    (d : SuppressionData K) (ends : Fin k → α × α)
    (W : ∀ j, GraphWalk K (ends j).1 (ends j).2)
    (W' : ∀ j, GraphWalk d.result (ends j).1 (ends j).2)
    (i : Fin k) (tail : List β) (hkeep : d.fresh = d.first)
    (he : (W i).edges = d.first :: d.second :: tail)
    (he' : (W' i).edges = d.fresh :: tail)
    (hother : ∀ j, j ≠ i → (W' j).edges = (W j).edges) (j : Fin k) :
    (W' j).edges.Sublist (W j).edges := by
  by_cases hji : j = i
  · subst j
    rw [he', he, hkeep]
    exact List.Sublist.cons_cons d.first (List.Sublist.cons d.second (List.Sublist.refl tail))
  · rw [hother j hji]

/-- Pairwise disjointness persists when each list is replaced by a sublist. -/
theorem edgeRoute_disjoint_of_sublist {A : Type*} {k : ℕ} (l l' : Fin k → List A)
    (hsub : ∀ i, (l' i).Sublist (l i))
    (hd : ∀ i j, i ≠ j → Disjoint {a | a ∈ l i} {a | a ∈ l j}) :
    ∀ i j, i ≠ j → Disjoint {a | a ∈ l' i} {a | a ∈ l' j} := by
  intro i j hij
  rw [Set.disjoint_left]
  intro a ha hb
  exact Set.disjoint_left.1 (hd i j hij) ((hsub i).subset ha) ((hsub j).subset hb)

end GraphMinor.GM02
