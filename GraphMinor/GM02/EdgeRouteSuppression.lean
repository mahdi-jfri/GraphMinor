module

public import GraphMinor.GM02.EdgeRouteIncidence
import GraphMinor.GM11.Walks

/-!
# Suppression at the first inner route vertex

The two neighboring links are not loops, and their edge names differ.
The incidence lemma shows that they are the only edges at the inner
vertex. Reuse the first removed edge's name for the replacement edge.
This works when the two remaining ends coincide or already have other
edges between them, as required for the general patterns in II (4.6).
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- The actual suppression data determined by the first two edges of an inner route. -/
noncomputable def edgeRouteSuppression {α : Type u} {β : Type v} {k : ℕ} (K H : Graph α β)
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
    (he₁ : K.IsLink e₁ (ends i).1 x) (he₂ : K.IsLink e₂ x z)
    (he : (W i).edges = e₁ :: e₂ :: tail.edges)
    (ht : tail.support = rest ++ [(ends i).2])
    (hne : (W i).edges.Nodup) : SuppressionData K where
  vertex := x
  left := (ends i).1
  right := z
  first := e₁
  second := e₂
  fresh := e₁
  first_ne_second := by
    rw [he] at hne
    intro h
    exact (List.nodup_cons.1 hne).1 (by simp [h])
  first_link := he₁.symm
  second_link := he₂
  vertex_ne_left := by
    have hx : x ∉ V(H) := hout i x (hi ▸ List.mem_cons_self)
    intro h
    exact hx (h ▸ (hends i).1)
  vertex_ne_right := by
    have hni : (x :: rest).Nodup := hi ▸ hn i
    have hx : x ∉ V(H) := hout i x (hi ▸ List.mem_cons_self)
    have hz := tail.start_mem_support
    rw [ht] at hz
    intro h
    rcases List.mem_append.1 hz with hz | hz
    · exact (List.nodup_cons.1 hni).1 (h ▸ hz)
    · have hzb : z = (ends i).2 := by simpa using hz
      exact hx ((h.trans hzb) ▸ (hends i).2)
  incident := edgeRoute_incident_only K H ends inner W hends hs hn hout hdis hcover
    i x rest hi e₁ e₂ z tail he ht
  fresh_notMem := fun h => h.2 (Or.inl rfl)

end GraphMinor.GM02
