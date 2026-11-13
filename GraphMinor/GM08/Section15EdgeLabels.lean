module

public import GraphMinor.Statement

/-!
# Assigning the original edge labels to a cut graph

An equivalence from a prescribed edge set to the edges of a graph lets
us use those prescribed labels without changing its vertices or links.
This keeps the original graft's edge type when reconstructing the cut
graft in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set Graph

universe u v w t

/-- Relabel the edges by a prescribed edge-set equivalence, keeping
all vertex labels. This is the edge label transport for the cut graft
in VIII (15.4), page 282. -/
theorem exists_graph_with_edge_equiv {α : Type u} {β : Type v} {δ : Type w}
    (G : Graph α δ) (B : Set β) (e : B ≃ E(G)) :
    ∃ (K : Graph α β) (i : Iso K G), V(K) = V(G) ∧ E(K) = B ∧
      (∀ x : V(K), (i.vertexEquiv x).1 = x.1) ∧
      ∀ (b : B) (x y : α), K.IsLink b.1 x y ↔ G.IsLink (e b).1 x y := by
  let K : Graph α β := {
    vertexSet := V(G)
    edgeSet := B
    IsLink := fun b x y => ∃ hb : b ∈ B, G.IsLink (e ⟨b, hb⟩).1 x y
    isLink_symm := by
      intro b hb
      refine ⟨?_⟩
      rintro x y ⟨h, hl⟩
      exact ⟨h, hl.symm⟩
    eq_or_eq_of_isLink_of_isLink := by
      rintro b x y z v ⟨hb, h⟩ ⟨hb', h'⟩
      exact h.left_eq_or_eq h'
    edge_mem_iff_exists_isLink := by
      intro b
      constructor
      · intro hb
        obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet (e ⟨b, hb⟩).2
        exact ⟨x, y, hb, hl⟩
      · rintro ⟨x, y, hb, _⟩
        exact hb
    left_mem_of_isLink := by
      rintro b x y ⟨_, hl⟩
      exact hl.left_mem }
  let i : Iso K G := {
    vertexEquiv := Equiv.refl _
    edgeEquiv := e
    isLink_iff := by
      intro b x y
      constructor
      · rintro ⟨_, hl⟩
        exact hl
      · intro hl
        exact ⟨b.2, hl⟩ }
  refine ⟨K, i, rfl, rfl, (fun _ => rfl), ?_⟩
  intro b x y
  constructor
  · rintro ⟨_, hl⟩
    exact hl
  · intro hl
    exact ⟨b.2, hl⟩

end GraphMinor.GM08
