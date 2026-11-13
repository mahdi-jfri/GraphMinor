module

public import GraphMinor.GM02.EdgeRouteSuppression
public import GraphMinor.GM02.EdgeRouteAvoidance
import GraphMinor.GM02.SuppressionWalk

/-!
# Shortening one route and retaining the others

Suppress the first inner vertex of one route. Its shortened walk starts
with the replacement edge and continues along the old tail. All other
walks avoid that vertex and keep their entire vertex and edge lists.
This is the local construction for the suppression induction in II (4.6).
-/

set_option backward.isDefEq.respectTransparency.types false

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- After one suppression, the selected route loses its first inner vertex and the other walks are unchanged. -/
theorem exists_edgeRoute_shortening {α : Type u} {β : Type v} {k : ℕ} (K H : Graph α β)
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
    (hne : (W i).edges.Nodup) :
    ∃ (d : SuppressionData K) (W' : ∀ j, GraphWalk d.result (ends j).1 (ends j).2),
      d.vertex = x ∧ d.first = e₁ ∧ d.second = e₂ ∧ d.fresh = e₁ ∧
      (∀ j, (W' j).support = (ends j).1 :: ((if j = i then rest else inner j) ++ [(ends j).2])) ∧
      (W' i).edges = e₁ :: tail.edges ∧
      ∀ j, j ≠ i → (W' j).edges = (W j).edges := by
  let d := edgeRouteSuppression K H ends inner W hends hs hn hout hdis hcover
    i x rest hi e₁ e₂ z tail he₁ he₂ he ht hne
  have htail : d.vertex ∉ tail.support :=
    edgeRoute_avoids_tail (inner i) rest tail (hends i).2 (hn i) (hout i) hi ht
  obtain ⟨short, hshort, hshortE⟩ := exists_shortened_suppression_walk d tail htail
  have hother : ∀ j, j ≠ i → ∃ w : GraphWalk d.result (ends j).1 (ends j).2,
      w.support = (W j).support ∧ w.edges = (W j).edges := by
    intro j hji
    apply exists_suppression_walk d (W j)
    exact edgeRoute_avoids_other K H ends inner W hends hs hout hdis i j hji.symm x
      (hi ▸ List.mem_cons_self)
  let W' : ∀ j, GraphWalk d.result (ends j).1 (ends j).2 := fun j =>
    if hji : j = i then hji.symm ▸ short else (hother j hji).choose
  have hWi : W' i = short := by
    dsimp only [W']
    split
    · rfl
    · contradiction
  have hWj : ∀ j (hji : j ≠ i), W' j = (hother j hji).choose := by
    intro j hji
    dsimp only [W']
    simp only [dite_eq_right hji]
  refine ⟨d, W', rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      rw [hWi, ite_eq_left (show i = i from rfl)]
      exact hshort.trans (congrArg (List.cons d.left) ht)
    · rw [hWj j hji, (hother j hji).choose_spec.1, hs j, ite_eq_right hji]
  · rw [hWi]
    exact hshortE
  · intro j hji
    rw [hWj j hji]
    exact (hother j hji).choose_spec.2

end GraphMinor.GM02
