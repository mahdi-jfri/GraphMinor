module

public import GraphMinor.GM02.EdgeRouteOrientation
import GraphMinor.GM11.Walks

/-!
# Gluing two edge-labelled routes at a suppressed vertex

The two routes have disjoint interiors and edge sets. Their common
pattern vertex belongs to neither interior. Inserting that vertex
between the interiors therefore keeps all inner vertices distinct.
The concatenated edge list is also free of repetitions. Every new inner
vertex lies outside the graph after suppression.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- Gluing the routes of the two removed edges preserves the route geometry. -/
theorem edgeRoute_glue_geometry {α : Type u} {β : Type v} {K M : Graph α β}
    (d : SuppressionData M) (hKM : V(M) ⊆ V(K))
    (l₁ l₂ : List α) (W₁ : GraphWalk K d.left d.vertex) (W₂ : GraphWalk K d.vertex d.right)
    (hn₁ : l₁.Nodup) (hn₂ : l₂.Nodup)
    (hout₁ : ∀ y ∈ l₁, y ∈ V(K) \ V(M)) (hout₂ : ∀ y ∈ l₂, y ∈ V(K) \ V(M))
    (hdV : Disjoint {y | y ∈ l₁} {y | y ∈ l₂})
    (heN₁ : W₁.edges.Nodup) (heN₂ : W₂.edges.Nodup)
    (heNon₁ : W₁.edges ≠ [])
    (hdE : Disjoint {e | e ∈ W₁.edges} {e | e ∈ W₂.edges}) :
    (l₁ ++ d.vertex :: l₂).Nodup ∧
      (∀ y ∈ l₁ ++ d.vertex :: l₂, y ∈ V(K) \ V(d.result)) ∧
      (W₁.append W₂).edges.Nodup ∧ (W₁.append W₂).edges ≠ [] := by
  have hxM : d.vertex ∈ V(M) := d.first_link.left_mem
  have hx₁ : d.vertex ∉ l₁ := fun h => (hout₁ _ h).2 hxM
  have hx₂ : d.vertex ∉ l₂ := fun h => (hout₂ _ h).2 hxM
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hn₁, List.nodup_cons.2 ⟨hx₂, hn₂⟩, ?_⟩
    intro y hy z hz hyz
    subst z
    rcases List.mem_cons.1 hz with h | h
    · exact hx₁ (h ▸ hy)
    · exact Set.disjoint_left.1 hdV hy h
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact ⟨(hout₁ y hy).1, fun h => (hout₁ y hy).2 h.1⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨hKM hxM, fun h => h.2 rfl⟩
      · exact ⟨(hout₂ y hy).1, fun h => (hout₂ y hy).2 h.1⟩
  · rw [GraphWalk.edges_append, List.nodup_append]
    refine ⟨heN₁, heN₂, ?_⟩
    intro e he f hf hef
    exact Set.disjoint_left.1 hdE he (hef ▸ hf)
  · rw [GraphWalk.edges_append]
    intro h
    have hlen := congrArg List.length h
    simp only [List.length_append, List.length_nil, Nat.add_eq_zero_iff] at hlen
    exact heNon₁ (List.length_eq_zero_iff.1 hlen.1)

end GraphMinor.GM02
