module

public import GraphMinor.Mader.ForestRepresentation
public import GraphMinor.Mader.ApexForest
public import GraphMinor.GM09.Defs

/-!
# Vertices of a forest deletion representation

Index the deleted vertices and represent the remaining forest by ordered
components. Their disjoint union contains every original vertex exactly
once. The resulting vertex equivalence is the vertex part of the graph
representation used in Mader's theorem.
-/

@[expose] public section

namespace GraphMinor.Mader

open Graph Kruskal GM09

variable {α β : Type*} {G : Graph α β} {X : Set α} {k n : ℕ}
    (hX : X ⊆ V(G)) (a : Fin k ≃ X) {t : Fin n → OrderedTree}
    (ψ : treeForest t ≃g (deleteVertices G X).toSimpleGraph)

/-- Send a chosen index or a forest address to its original vertex. -/
def deletionVertexMap : (Fin k ⊕ ForestVertex t) → V(G)
  | .inl i => ⟨(a i).val, hX (a i).property⟩
  | .inr v => ⟨(ψ v).val, (ψ v).property.1⟩

/-- The chosen vertices and forest vertices have disjoint images, and
both component maps are injective. -/
theorem deletionVertexMap_injective : Function.Injective (deletionVertexMap hX a ψ) := by
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      exact congrArg Sum.inl (a.injective (Subtype.ext
        (congrArg (fun v : V(G) ↦ v.val) hxy)))
    | inr v =>
      have he : (a i).val = (ψ v).val := congrArg (fun v : V(G) ↦ v.val) hxy
      exact ((ψ v).property.2 (he ▸ (a i).property)).elim
  | inr v =>
    cases y with
    | inl i =>
      have he : (ψ v).val = (a i).val := congrArg (fun v : V(G) ↦ v.val) hxy
      exact ((ψ v).property.2 (he.symm ▸ (a i).property)).elim
    | inr w =>
      exact congrArg Sum.inr (ψ.injective (Subtype.ext
        (congrArg (fun v : V(G) ↦ v.val) hxy)))

/-- Every original vertex is either chosen or belongs to the represented forest. -/
theorem deletionVertexMap_surjective : Function.Surjective (deletionVertexMap hX a ψ) := by
  classical
  intro v
  by_cases hv : v.val ∈ X
  · obtain ⟨i, hi⟩ := a.surjective ⟨v.val, hv⟩
    refine ⟨.inl i, ?_⟩
    exact Subtype.ext (congrArg (fun v : X ↦ v.val) hi)
  · let w : V(deleteVertices G X) := ⟨v.val, v.property, hv⟩
    obtain ⟨x, hx⟩ := ψ.surjective w
    refine ⟨.inr x, ?_⟩
    exact Subtype.ext (congrArg (fun v : V(deleteVertices G X) ↦ v.val) hx)

/-- The vertex equivalence between the indexed representation and the original graph. -/
noncomputable def deletionVertexEquiv : (Fin k ⊕ ForestVertex t) ≃ V(G) :=
  Equiv.ofBijective (deletionVertexMap hX a ψ)
    ⟨deletionVertexMap_injective hX a ψ, deletionVertexMap_surjective hX a ψ⟩

end GraphMinor.Mader
