module

public import GraphMinor.Mader.DeletionEdges

/-!
# Injectivity of the original edge-name map

Equal original edges have the same pair of ends. The vertex bijection
therefore separates the forest, attachment, and core edge kinds. Within
one kind, either the forest edge bijection or the parallel-edge
enumeration gives equality. Ordering core pairs rules out a second name
obtained by reversing the two ends.
-/

public section

namespace GraphMinor.Mader

open Graph Kruskal GM09 Surface

variable {α β : Type*} {G : Graph α β} {X : Set α} {k n : ℕ}
    (hE : E(G).Finite) (hX : X ⊆ V(G)) (a : Fin k ≃ X)
    {t : Fin n → OrderedTree} (hforest : IsGraphForest (deleteVertices G X))
    (ψ : treeForest t ≃g (deleteVertices G X).toSimpleGraph)

include hX in
private theorem deletionEdgeMap_ends_eq
    {e e' : ApexForestEdge t (deletionAttachmentCounts G a ψ) (deletionCoreCounts G a)}
    (he : deletionEdgeMap hE a hforest ψ e = deletionEdgeMap hE a hforest ψ e') :
    let left := apexForestLeft t (deletionAttachmentCounts G a ψ) (deletionCoreCounts G a)
    let right := apexForestRight t (deletionAttachmentCounts G a ψ) (deletionCoreCounts G a)
    (left e = left e' ∧ right e = right e') ∨ (left e = right e' ∧ right e = left e') := by
  have h := deletionEdgeMap_isLink hE a hforest ψ hX e
  have h' := deletionEdgeMap_isLink hE a hforest ψ hX e'
  rw [he] at h
  rcases h.eq_and_eq_or_eq_and_eq h' with h | h
  · exact Or.inl ⟨deletionVertexMap_injective hX a ψ (Subtype.ext h.1),
      deletionVertexMap_injective hX a ψ (Subtype.ext h.2)⟩
  · exact Or.inr ⟨deletionVertexMap_injective hX a ψ (Subtype.ext h.1),
      deletionVertexMap_injective hX a ψ (Subtype.ext h.2)⟩

private theorem ordered_pair_eq_of_swapped {k : ℕ} {i j i' j' : Fin k}
    (hij : i ≤ j) (hij' : i' ≤ j') (hi : i = j') (hj : j = i') : i = i' ∧ j = j' := by
  subst j'
  subst i'
  have heq := le_antisymm hij hij'
  exact ⟨heq, heq.symm⟩

include hX in
/-- Distinct represented edges have distinct original edge names. -/
theorem deletionEdgeMap_injective : Function.Injective (deletionEdgeMap hE a hforest ψ) := by
  intro e e' he
  have hend := deletionEdgeMap_ends_eq hE hX a hforest ψ he
  cases e with
  | inl q =>
    cases e' with
    | inl q' =>
      have hq : deletionForestEdgeEquiv hforest ψ q = deletionForestEdgeEquiv hforest ψ q' :=
        Subtype.ext (congrArg (fun e : E(G) ↦ e.val) he)
      exact congrArg Sum.inl ((deletionForestEdgeEquiv hforest ψ).injective hq)
    | inr q' => cases q' <;> simp [apexForestLeft, apexForestRight] at hend
  | inr q =>
    cases q with
    | inl q =>
      obtain ⟨v, i, p⟩ := q
      cases e' with
      | inl q' => simp [apexForestLeft, apexForestRight] at hend
      | inr q' =>
        cases q' with
        | inr q' => simp [apexForestLeft, apexForestRight] at hend
        | inl q' =>
          obtain ⟨w, j, p'⟩ := q'
          have hvw : v = w ∧ i = j := by
            simpa only [apexForestLeft, apexForestRight, Sum.inr.injEq, Sum.inl.injEq,
              Sum.inr_ne_inl, false_and, or_false] using hend
          obtain ⟨rfl, rfl⟩ := hvw
          have hp := (deletionAttachmentEnumeration G a ψ hE v i).injective
            (Subtype.ext (congrArg (fun e : E(G) ↦ e.val) he))
          change p = p' at hp
          subst p'
          rfl
    | inr q =>
      obtain ⟨i, j, p⟩ := q
      cases e' with
      | inl q' => simp [apexForestLeft, apexForestRight] at hend
      | inr q' =>
        cases q' with
        | inl q' => simp [apexForestLeft, apexForestRight] at hend
        | inr q' =>
          obtain ⟨i', j', p'⟩ := q'
          have ho := deletionCoreCounts_ordered G a ⟨i, j, p⟩
          have ho' := deletionCoreCounts_ordered G a ⟨i', j', p'⟩
          have hpair : i = i' ∧ j = j' := by
            have hh : (i = i' ∧ j = j') ∨ (i = j' ∧ j = i') := by
              simpa only [apexForestLeft, apexForestRight, Sum.inl.injEq] using hend
            rcases hh with h | ⟨hi, hj⟩
            · exact h
            · exact ordered_pair_eq_of_swapped ho ho' hi hj
          obtain ⟨rfl, rfl⟩ := hpair
          have hp := (deletionCoreEnumeration G a hE i j ho).injective
            (Subtype.ext (congrArg (fun e : E(G) ↦ e.val) he))
          change p = p' at hp
          subst p'
          rfl

end GraphMinor.Mader
