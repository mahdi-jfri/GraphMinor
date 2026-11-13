module

public import GraphMinor.GM02.Section4Suppression
public import GraphMinor.Surface.Defs

/-!
# The final graph when route interiors are empty

Each route is then one actual edge. Edge disjointness makes these edge
names distinct, including for loops or parallel edges of the pattern.
The edge cover makes the map onto the whole graph. Together with equal
vertex sets, this is an isomorphism fixing every vertex.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- A walk whose support has two entries consists of exactly one edge, also when the entries coincide. -/
theorem GraphWalk.exists_single_edge {α : Type u} {β : Type v} {K : Graph α β}
    {a b : α} (W : GraphWalk K a b) (hs : W.support = [a, b]) :
    ∃ e, K.IsLink e a b ∧ W.edges = [e] := by
  cases W with
  | nil => simp [Surface.GraphWalk.support] at hs
  | @cons a c b e h r =>
    cases r with
    | nil => exact ⟨e, h, rfl⟩
    | cons h' tail =>
      have ht : tail.support = [] := (List.cons.inj (List.cons.inj hs).2).2
      cases tail <;> cases ht

/-- Single-edge disjoint routes give the required isomorphism, without any simplicity assumption on the pattern. -/
theorem edgeRoute_isoFix_of_inner_eq_nil {α : Type u} {β : Type v} {k : ℕ}
    (K H : Graph α β) (edge : Fin k ≃ E(H)) (ends : Fin k → α × α)
    (hH : ∀ i, H.IsLink (edge i).val (ends i).1 (ends i).2)
    (W : ∀ i, GraphWalk K (ends i).1 (ends i).2)
    (hs : ∀ i, (W i).support = [(ends i).1, (ends i).2])
    (hV : V(H) = V(K))
    (hcover : ∀ e ∈ E(K), ∃ i, e ∈ (W i).edges)
    (hdis : ∀ i j, i ≠ j → Disjoint {e | e ∈ (W i).edges} {e | e ∈ (W j).edges}) :
    IsoFix H K := by
  choose pick hlink hpick using (fun i => GraphWalk.exists_single_edge (W i) (hs i))
  let σ : β → β := fun f => if hf : f ∈ E(H) then pick (edge.symm ⟨f, hf⟩) else f
  have hσ : ∀ f (hf : f ∈ E(H)), σ f = pick (edge.symm ⟨f, hf⟩) := by
    intro f hf
    simp only [σ, dite_eq_left hf]
  have hσi : ∀ i, σ (edge i).val = pick i := by
    intro i
    rw [hσ _ (edge i).property]
    exact congrArg pick (edge.symm_apply_apply i)
  refine ⟨σ, hV, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    rw [hσ f hf]
    exact (hlink _).edge_mem
  · intro f hf g hg hfg
    have hij : edge.symm ⟨f, hf⟩ = edge.symm ⟨g, hg⟩ := by
      by_contra hij
      have hd := hdis _ _ hij
      have hm₁ : pick (edge.symm ⟨f, hf⟩) ∈ (W (edge.symm ⟨f, hf⟩)).edges := by
        rw [hpick]; exact List.mem_cons_self
      have hm₂ : pick (edge.symm ⟨f, hf⟩) ∈ (W (edge.symm ⟨g, hg⟩)).edges := by
        rw [hpick, ← hσ f hf, hfg, hσ g hg]; exact List.mem_cons_self
      exact Set.disjoint_left.1 hd hm₁ hm₂
    exact congrArg Subtype.val (edge.symm.injective hij)
  · intro e he
    obtain ⟨i, hi⟩ := hcover e he
    rw [hpick i, List.mem_singleton] at hi
    exact ⟨(edge i).val, (edge i).property, (hσi i).trans hi.symm⟩
  · intro f hf a b
    let i := edge.symm ⟨f, hf⟩
    have hHi : H.IsLink f (ends i).1 (ends i).2 := by
      simpa only [i, Equiv.apply_symm_apply] using hH i
    have hKi : K.IsLink (σ f) (ends i).1 (ends i).2 := by
      rw [hσ f hf]
      exact hlink i
    rw [hHi.isLink_iff, hKi.isLink_iff]

end GraphMinor.GM02
