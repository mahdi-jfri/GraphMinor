module

public import GraphMinor.Mader.DeletionForestEdges
public import GraphMinor.Mader.DeletionMultiplicities
public import GraphMinor.GM09.Basic

/-!
# Mapping all represented edges to their original names

Forest edges use the edge bijection of the deletion forest. Attachment
and core edges use the enumerations of parallel edges with those ends.
Every mapped edge has the represented ends, including loops in the core.
-/

@[expose] public section

namespace GraphMinor.Mader

open Graph Kruskal GM09 Surface

variable {α β : Type*} {G : Graph α β} {X : Set α} {k n : ℕ}
    (hE : E(G).Finite) (a : Fin k ≃ X) {t : Fin n → OrderedTree}
    (hforest : IsGraphForest (deleteVertices G X))
    (ψ : treeForest t ≃g (deleteVertices G X).toSimpleGraph)

/-- Map the three kinds of represented edges to actual original edges. -/
noncomputable def deletionEdgeMap :
    ApexForestEdge t (deletionAttachmentCounts G a ψ) (deletionCoreCounts G a) → E(G)
  | .inl e => ⟨(deletionForestEdgeEquiv hforest ψ e).val,
      (deleteVertices_le G X).edgeSet_mono (deletionForestEdgeEquiv hforest ψ e).property⟩
  | .inr (.inl ⟨v, j, p⟩) =>
      ⟨(deletionAttachmentEnumeration G a ψ hE v j p).val,
        (deletionAttachmentEnumeration G a ψ hE v j p).property.edge_mem⟩
  | .inr (.inr e) =>
      ⟨(deletionCoreEnumeration G a hE e.1 e.2.1 (deletionCoreCounts_ordered G a e) e.2.2).val,
        (deletionCoreEnumeration G a hE e.1 e.2.1
          (deletionCoreCounts_ordered G a e) e.2.2).property.edge_mem⟩

/-- Each represented edge has the two vertices specified by its edge kind. -/
theorem deletionEdgeMap_isLink (hX : X ⊆ V(G))
    (e : ApexForestEdge t (deletionAttachmentCounts G a ψ) (deletionCoreCounts G a)) :
    G.IsLink (deletionEdgeMap hE a hforest ψ e).val
      (deletionVertexMap hX a ψ
        (apexForestLeft t (deletionAttachmentCounts G a ψ) (deletionCoreCounts G a) e)).val
      (deletionVertexMap hX a ψ
        (apexForestRight t (deletionAttachmentCounts G a ψ) (deletionCoreCounts G a) e)).val := by
  cases e with
  | inl e =>
    obtain ⟨i, e⟩ := e
    exact deletionForestEdgeEquiv_isLink_original hforest ψ i e
  | inr e =>
    cases e with
    | inl e =>
      obtain ⟨v, j, p⟩ := e
      exact (deletionAttachmentEnumeration G a ψ hE v j p).property
    | inr e =>
      exact (deletionCoreEnumeration G a hE e.1 e.2.1
        (deletionCoreCounts_ordered G a e) e.2.2).property

/-- Every original edge is a forest edge, an attachment edge, or a core edge. -/
theorem deletionEdgeMap_surjective (hX : X ⊆ V(G)) :
    Function.Surjective (deletionEdgeMap hE a hforest ψ) := by
  intro e
  obtain ⟨u, v, he⟩ := G.exists_isLink_of_mem_edgeSet e.property
  obtain ⟨x, hx⟩ := (deletionVertexEquiv hX a ψ).surjective ⟨u, he.left_mem⟩
  obtain ⟨y, hy⟩ := (deletionVertexEquiv hX a ψ).surjective ⟨v, he.right_mem⟩
  have hlink : G.IsLink e.val (deletionVertexMap hX a ψ x).val
      (deletionVertexMap hX a ψ y).val := by
    have hx' : (deletionVertexMap hX a ψ x).val = u :=
      congrArg (fun z : V(G) ↦ z.val) hx
    have hy' : (deletionVertexMap hX a ψ y).val = v :=
      congrArg (fun z : V(G) ↦ z.val) hy
    rw [hx', hy']
    exact he
  cases x with
  | inr w =>
    cases y with
    | inr z =>
      have hK : (deleteVertices G X).IsLink e.val (ψ w).val (ψ z).val :=
        (deleteVertices_isLink G X).mpr ⟨hlink, (ψ w).property.2, (ψ z).property.2⟩
      obtain ⟨q, hq⟩ := (deletionForestEdgeEquiv hforest ψ).surjective ⟨e.val, hK.edge_mem⟩
      refine ⟨.inl q, ?_⟩
      exact Subtype.ext (congrArg (fun z : E(deleteVertices G X) ↦ z.val) hq)
    | inl j =>
      have hl : G.IsLink e.val (ψ w).val (a j).val := hlink
      obtain ⟨p, hp⟩ := (deletionAttachmentEnumeration G a ψ hE w j).surjective ⟨e.val, hl⟩
      refine ⟨.inr (.inl ⟨w, j, p⟩), ?_⟩
      exact Subtype.ext (congrArg (fun z : {q | G.IsLink q (ψ w).val (a j).val} ↦ z.val) hp)
  | inl i =>
    cases y with
    | inr w =>
      have hl : G.IsLink e.val (ψ w).val (a i).val := hlink.symm
      obtain ⟨p, hp⟩ := (deletionAttachmentEnumeration G a ψ hE w i).surjective ⟨e.val, hl⟩
      refine ⟨.inr (.inl ⟨w, i, p⟩), ?_⟩
      exact Subtype.ext (congrArg (fun z : {q | G.IsLink q (ψ w).val (a i).val} ↦ z.val) hp)
    | inl j =>
      have hl : G.IsLink e.val (a i).val (a j).val := hlink
      by_cases hij : i ≤ j
      · obtain ⟨p, hp⟩ := (deletionCoreEnumeration G a hE i j hij).surjective ⟨e.val, hl⟩
        refine ⟨.inr (.inr ⟨i, j, p⟩), ?_⟩
        exact Subtype.ext (congrArg (fun z : {q | G.IsLink q (a i).val (a j).val} ↦ z.val) hp)
      · have hji : j ≤ i := le_of_not_ge hij
        obtain ⟨p, hp⟩ := (deletionCoreEnumeration G a hE j i hji).surjective ⟨e.val, hl.symm⟩
        refine ⟨.inr (.inr ⟨j, i, p⟩), ?_⟩
        exact Subtype.ext (congrArg (fun z : {q | G.IsLink q (a j).val (a i).val} ↦ z.val) hp)

end GraphMinor.Mader
