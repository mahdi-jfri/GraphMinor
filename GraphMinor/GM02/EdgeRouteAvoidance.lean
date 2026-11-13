module

public import GraphMinor.GM02.EdgeRouteIncidence
import GraphMinor.GM11.Walks

/-!
# Routes avoiding a suppressed inner vertex

An inner vertex lies on no other route, since it is outside the branch
set and the interiors are disjoint. It also does not occur in its own
remaining tail, since its interior has no repeated vertex. These are the
avoidance conditions needed to transfer the walks through a suppression.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- An inner vertex of one route is absent from every other route's support. -/
theorem edgeRoute_avoids_other {α : Type u} {β : Type v} {k : ℕ} (K H : Graph α β)
    (ends : Fin k → α × α) (inner : Fin k → List α)
    (W : ∀ i, GraphWalk K (ends i).1 (ends i).2)
    (hends : ∀ i, (ends i).1 ∈ V(H) ∧ (ends i).2 ∈ V(H))
    (hs : ∀ i, (W i).support = (ends i).1 :: (inner i ++ [(ends i).2]))
    (hout : ∀ i y, y ∈ inner i → y ∉ V(H))
    (hdis : ∀ i j, i ≠ j → Disjoint {y | y ∈ inner i} {y | y ∈ inner j})
    (i j : Fin k) (hij : i ≠ j) (x : α) (hx : x ∈ inner i) : x ∉ (W j).support := by
  have hxH := hout i x hx
  rw [hs j]
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
  rintro (he | hm | he)
  · exact hxH (he ▸ (hends j).1)
  · exact Set.disjoint_left.1 (hdis i j hij) hx hm
  · exact hxH (he ▸ (hends j).2)

/-- The first inner vertex is absent from the tail after its two neighboring edges. -/
theorem edgeRoute_avoids_tail {α : Type u} {β : Type v} {K H : Graph α β}
    {x z b : α} (inner rest : List α) (tail : GraphWalk K z b)
    (hb : b ∈ V(H)) (hn : inner.Nodup) (hout : ∀ y ∈ inner, y ∉ V(H))
    (hi : inner = x :: rest) (ht : tail.support = rest ++ [b]) : x ∉ tail.support := by
  rw [ht]
  intro hm
  rcases List.mem_append.1 hm with hm | hm
  · have hn' : (x :: rest).Nodup := hi ▸ hn
    exact (List.nodup_cons.1 hn').1 hm
  · have hxb : x = b := by simpa using hm
    exact hout x (hi ▸ List.mem_cons_self) (hxb ▸ hb)

end GraphMinor.GM02
