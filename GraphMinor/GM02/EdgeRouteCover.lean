module

public import GraphMinor.GM02.TopologicalContainment
public import GraphMinor.Surface.Defs

/-!
# Route covers after one suppression

The shortened route retains the replacement edge. Every other retained
edge remains on the same route. For vertices, the only deleted entry is
the suppressed inner vertex. Thus both covers needed by the suppression
induction continue to hold.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- Shortening the selected edge list preserves a cover of all edges of the suppression result. -/
theorem edgeRoute_cover_after_suppression {α : Type u} {β : Type v} {k : ℕ} {K : Graph α β}
    (d : SuppressionData K) (ends : Fin k → α × α)
    (W : ∀ j, GraphWalk K (ends j).1 (ends j).2)
    (W' : ∀ j, GraphWalk d.result (ends j).1 (ends j).2)
    (hcover : ∀ e ∈ E(K), ∃ j, e ∈ (W j).edges)
    (i : Fin k) (tail : List β)
    (he : (W i).edges = d.first :: d.second :: tail)
    (he' : (W' i).edges = d.fresh :: tail)
    (hother : ∀ j, j ≠ i → (W' j).edges = (W j).edges) :
    ∀ e ∈ E(d.result), ∃ j, e ∈ (W' j).edges := by
  intro e heE
  change e ∈ (E(K) \ {d.first, d.second}) ∪ {d.fresh} at heE
  rcases heE with ⟨heK, hne⟩ | heF
  · obtain ⟨j, hej⟩ := hcover e heK
    by_cases hji : j = i
    · subst j
      refine ⟨i, ?_⟩
      rw [he] at hej
      rw [he']
      rcases List.mem_cons.1 hej with h | h
      · exact (hne (Or.inl h)).elim
      · rcases List.mem_cons.1 h with h | h
        · exact (hne (Or.inr h)).elim
        · exact List.mem_cons_of_mem _ h
    · exact ⟨j, (hother j hji).symm ▸ hej⟩
  · exact ⟨i, he'.symm ▸ (Set.mem_singleton_iff.1 heF ▸ List.mem_cons_self)⟩

/-- Removing one inner vertex preserves the vertex cover of the suppression result. -/
theorem edgeRoute_vertex_cover_after_suppression {α : Type u} {β : Type v} {k : ℕ}
    {K H : Graph α β} (d : SuppressionData K) (inner : Fin k → List α)
    (hcover : ∀ y ∈ V(K), y ∈ V(H) ∨ ∃ j, y ∈ inner j)
    (i : Fin k) (rest : List α) (hi : inner i = d.vertex :: rest) :
    ∀ y ∈ V(d.result), y ∈ V(H) ∨ ∃ j, y ∈ (if j = i then rest else inner j) := by
  intro y hy
  change y ∈ V(K) \ {d.vertex} at hy
  rcases hcover y hy.1 with hyH | ⟨j, hyj⟩
  · exact Or.inl hyH
  · right
    refine ⟨j, ?_⟩
    by_cases hji : j = i
    · subst j
      rw [hi] at hyj
      rw [ite_eq_left (show i = i from rfl)]
      rcases List.mem_cons.1 hyj with h | h
      · exact (hy.2 h).elim
      · exact h
    · simpa only [ite_eq_right hji] using hyj

end GraphMinor.GM02
