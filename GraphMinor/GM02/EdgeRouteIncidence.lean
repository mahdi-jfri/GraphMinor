module

public import GraphMinor.GM02.TopologicalContainment
public import GraphMinor.Surface.Defs
import GraphMinor.GM11.Walks

/-!
# The two edges at an inner route vertex

For the suppression argument in II, page 319, retain edge-labelled walks
rather than just vertex paths. A walk whose inner vertices do not repeat
can visit an inner vertex only between its two neighboring route edges.
No other route meets that vertex. If the graph is covered by the route
edges, these are therefore all its incident edges.
-/

set_option backward.isDefEq.respectTransparency.types false

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- Extract the first two links of a route with a nonempty interior. -/
theorem GraphWalk.exists_first_two {α : Type u} {β : Type v} {K : Graph α β}
    {a x b : α} (W : GraphWalk K a b) (rest : List α)
    (hs : W.support = a :: (x :: rest ++ [b])) :
    ∃ (e₁ e₂ : β) (z : α) (tail : GraphWalk K z b),
      K.IsLink e₁ a x ∧ K.IsLink e₂ x z ∧
      W.edges = e₁ :: e₂ :: tail.edges ∧ tail.support = rest ++ [b] := by
  cases W with
  | nil => simp [Surface.GraphWalk.support] at hs
  | @cons a c b e₁ h₁ r =>
    cases r with
    | nil => simp [Surface.GraphWalk.support] at hs
    | @cons c z b e₂ h₂ tail =>
      change a :: c :: tail.support = a :: (x :: rest ++ [b]) at hs
      have hc : c = x := (List.cons.inj (List.cons.inj hs).2).1
      have ht : tail.support = rest ++ [b] := (List.cons.inj (List.cons.inj hs).2).2
      subst c
      exact ⟨e₁, e₂, z, tail, h₁, h₂, rfl, ht⟩

/-- At the first inner vertex, the two neighboring route edges are the only incident edges. -/
theorem edgeRoute_incident_only {α : Type u} {β : Type v} {k : ℕ} (K H : Graph α β)
    (ends : Fin k → α × α) (inner : Fin k → List α)
    (W : ∀ i, GraphWalk K (ends i).1 (ends i).2)
    (hends : ∀ i, (ends i).1 ∈ V(H) ∧ (ends i).2 ∈ V(H))
    (hs : ∀ i, (W i).support = (ends i).1 :: (inner i ++ [(ends i).2]))
    (hn : ∀ i, (inner i).Nodup)
    (hout : ∀ i y, y ∈ inner i → y ∉ V(H))
    (hdis : ∀ i j, i ≠ j → Disjoint {y | y ∈ inner i} {y | y ∈ inner j})
    (hcover : ∀ e ∈ E(K), ∃ i, e ∈ (W i).edges)
    (i : Fin k) (x : α) (rest : List α) (hi : inner i = x :: rest)
    (e₁ e₂ : β) (z : α) (tail : GraphWalk K z (ends i).2)
    (he : (W i).edges = e₁ :: e₂ :: tail.edges)
    (ht : tail.support = rest ++ [(ends i).2]) :
    ∀ e, K.Inc e x → e = e₁ ∨ e = e₂ := by
  have hx : x ∈ inner i := hi ▸ List.mem_cons_self
  have hxH : x ∉ V(H) := hout i x hx
  have hxt : x ∉ tail.support := by
    rw [ht]
    intro hm
    rcases List.mem_append.1 hm with hm | hm
    · have hni : (x :: rest).Nodup := hi ▸ hn i
      exact (List.nodup_cons.1 hni).1 hm
    · have hxb : x = (ends i).2 := by simpa using hm
      exact hxH (hxb ▸ (hends i).2)
  intro e hinc
  obtain ⟨y, hxy⟩ := hinc
  obtain ⟨j, hej⟩ := hcover e hxy.edge_mem
  have hxj := (W j).left_mem_support_of_mem_edges hej hxy
  rw [hs j] at hxj
  have hxin : x ∈ inner j := by
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hxj
    rcases hxj with h | h | h
    · exact (hxH (h ▸ (hends j).1)).elim
    · exact h
    · exact (hxH (h ▸ (hends j).2)).elim
  have hji : j = i := by
    by_contra hji
    exact Set.disjoint_left.1 (hdis i j (Ne.symm hji)) hx hxin
  subst j
  rw [he] at hej
  rcases List.mem_cons.1 hej with h | h
  · exact Or.inl h
  · rcases List.mem_cons.1 h with h | h
    · exact Or.inr h
    · exact (hxt (tail.left_mem_support_of_mem_edges h hxy)).elim

end GraphMinor.GM02
