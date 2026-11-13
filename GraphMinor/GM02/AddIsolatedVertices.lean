module

public import GraphMinor.GM02.AttachVertexDecomposition
public import Mathlib.Combinatorics.Graph.Delete

/-!
# Adding finitely many isolated vertices preserves a width bound

Induct on the added vertices. A vertex already present changes nothing.
For a new vertex, attach a singleton leaf bag to any old bag. There are
no incident old edges at that vertex, and a singleton has width zero.
This handles unused numeric positions in the split graph of II (4.6).
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

private theorem delete_new_vertex {α : Type u} {β : Type v} (G : Graph α β)
    (S : Set α) (a : α) (ha : a ∉ V(G)) (haS : a ∉ S) :
    (G.induce (V(G) ∪ insert a S)).deleteVerts {a} = G.induce (V(G) ∪ S) := by
  apply Graph.ext
  · ext x
    simp only [Graph.vertexSet_deleteVerts, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx | hx | hx, hne⟩
      · exact Or.inl hx
      · exact False.elim (hne hx)
      · exact Or.inr hx
    · intro hx
      refine ⟨?_, ?_⟩
      · exact hx.elim Or.inl (fun h => Or.inr (Or.inr h))
      · intro heq
        subst x
        exact hx.elim ha haS
  · intro e x y
    rw [Graph.deleteVerts_isLink, Graph.induce_isLink, Graph.induce_isLink]
    constructor
    · rintro ⟨⟨h, _, _⟩, _, _⟩
      exact ⟨h, Or.inl h.left_mem, Or.inl h.right_mem⟩
    · rintro ⟨h, _, _⟩
      refine ⟨⟨h, Or.inl h.left_mem, Or.inl h.right_mem⟩, ?_, ?_⟩
      · intro hxa
        exact ha (hxa ▸ h.left_mem)
      · intro hya
        exact ha (hya ▸ h.right_mem)

/-- Adding finitely many isolated vertices does not increase a natural-number width bound. -/
theorem treeWidthLE_add_isolated_vertices {α : Type u} {β : Type v}
    (G : Graph α β) (w : ℕ) (hW : TreeWidthLE G w) (S : Set α) (hS : S.Finite) :
    TreeWidthLE (G.induce (V(G) ∪ S)) w := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simpa only [Set.union_empty, Graph.induce_vertexSet] using hW
  | @insert a S haS hS ih =>
    by_cases ha : a ∈ V(G)
    · have hsets : V(G) ∪ insert a S = V(G) ∪ S := by
        ext x
        constructor
        · rintro (hx | hx | hx)
          · exact Or.inl hx
          · exact Or.inl (hx ▸ ha)
          · exact Or.inr hx
        · intro hx
          exact hx.elim Or.inl (fun h => Or.inr (Or.inr h))
      rw [hsets]
      exact ih
    · obtain ⟨ι, hι, T, X, hD, hwidth⟩ := ih
      let : Fintype ι := hι
      obtain ⟨t₀⟩ := hD.isTree.connected.nonempty
      have hdel := delete_new_vertex G S a ha haS
      have hDdel : IsTreeDecomposition ((G.induce (V(G) ∪ insert a S)).deleteVerts {a}) T X :=
        hdel.symm ▸ hD
      have hnew := attachVertex_isTreeDecomposition
        (G := G.induce (V(G) ∪ insert a S)) (v := a)
        (Or.inr (Or.inl rfl)) hDdel t₀ ∅ (Set.empty_subset _)
        (by
          intro e x h
          rw [Graph.induce_isLink] at h
          exact False.elim (ha h.1.left_mem))
      refine ⟨Option ι, inferInstance, GM10.attachLeaf T t₀, _, hnew, ?_⟩
      intro t
      cases t with
      | some t => exact hwidth t
      | none =>
        change (insert a (∅ : Set α)).ncard ≤ w + 1
        have hc := Set.ncard_insert_le a (∅ : Set α)
        simp only [Set.ncard_empty] at hc
        omega

end GraphMinor.GM02
