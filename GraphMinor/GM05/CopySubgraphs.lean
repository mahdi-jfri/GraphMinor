module

public import GraphMinor.GM05.GraphCopies

/-!
# The individual copies as subgraphs

The disjoint-copy graph used in GM V, (8.14), has one subgraph for
each copy index. Its vertex and edge sets have that fixed index, and
the map taking each original name to its tagged name is an isomorphism.
-/

public section
namespace GraphMinor.GM05
open Set Graph

/-- Each disjoint copy is an actual subgraph with the prescribed
vertex and edge tags and an explicit tagging isomorphism. -/
theorem exists_single_copy_subgraph {α β : Type*} (k : ℕ) (H : Graph α β) (i : Fin k) :
    ∃ A : Graph (Fin k × α) (Fin k × β),A≤graphCopies k H ∧
      V(A)={i}×ˢV(H) ∧ E(A)={i}×ˢE(H) ∧ Nonempty (Iso H A) := by
  let A : Graph (Fin k × α) (Fin k × β) := {
    vertexSet := {i}×ˢV(H)
    edgeSet := {i}×ˢE(H)
    IsLink := fun e x y ↦ e.1=i ∧ (graphCopies k H).IsLink e x y
    isLink_symm := fun _ _ ↦ ⟨fun _ _ h ↦ ⟨h.1,h.2.symm⟩⟩
    eq_or_eq_of_isLink_of_isLink := fun _ _ _ _ _ h h' ↦ h.2.left_eq_or_eq h'.2
    edge_mem_iff_exists_isLink := by
      intro e
      constructor
      · intro he
        obtain ⟨x,y,hxy⟩ := H.exists_isLink_of_mem_edgeSet he.2
        exact ⟨(e.1,x),(e.1,y),he.1,rfl,rfl,hxy⟩
      · rintro ⟨x,y,hxy⟩
        exact ⟨hxy.1,hxy.2.edge_mem.2⟩
    left_mem_of_isLink := fun _ _ _ h ↦ ⟨h.2.1.symm.trans h.1,h.2.2.2.left_mem⟩ }
  have hA : A≤graphCopies k H := ⟨fun _ hx ↦ ⟨mem_univ _,hx.2⟩,fun _ _ _ h ↦ h.2⟩
  let ev : V(H) ≃ V(A) := {
    toFun := fun x ↦ ⟨(i,x.val),rfl,x.prop⟩
    invFun := fun x ↦ ⟨x.val.2,x.prop.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun x ↦ Subtype.ext (Prod.ext x.prop.1.symm rfl) }
  let ee : E(H) ≃ E(A) := {
    toFun := fun e ↦ ⟨(i,e.val),rfl,e.prop⟩
    invFun := fun e ↦ ⟨e.val.2,e.prop.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun e ↦ Subtype.ext (Prod.ext e.prop.1.symm rfl) }
  refine ⟨A,hA,rfl,rfl,⟨⟨ev,ee,?_⟩⟩⟩
  intro e x y
  exact ⟨fun h ↦ ⟨rfl,rfl,rfl,h⟩,fun h ↦ h.2.2.2⟩

end GraphMinor.GM05
