module

public import GraphMinor.GM08.Section11Transport
public import GraphMinor.GM12.Section3SubspaceDrawing
import GraphMinor.GM11.Defs

/-!
# Reading a foundation piece in its own disc

A drawing supported in a closed disc can be read as a drawing of that
disc as an ambient space. Inclusion gives a bijection of its drawing
graph with the original graph. This is used to view each foundation
piece as a smaller disc-embeddable graft when assigning the labels of
the derived portrait in VIII, Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface Topology

universe u

/-- A graph bijection gives an isomorphism by restricting its maps to
the vertex and edge sets. This is used for the foundation labels in
the derived portrait of VIII, Section 12. -/
@[expose] noncomputable def IsGraphBij.toIso {α β γ δ : Type*}
    {G : Graph α β} {H : Graph γ δ} {f : α → γ} {g : β → δ}
    (h : IsGraphBij G H f g) : Iso G H where
  vertexEquiv := h.bijV.equiv
  edgeEquiv := h.bijE.equiv
  isLink_iff e x y := h.isLink e.1 e.2 x.1 x.2 y.1 y.2

/-- Inclusion from a closed subspace gives a bijection of drawing
graphs. A foundation piece therefore keeps its graph when read inside
its own disc in the portrait construction on VIII, page 272. -/
theorem isGraphBij_drawingInSubspace {S : Type u} [TopologicalSpace S]
    (D : Drawing S) {B : Set S} (hB : IsClosed B) (hDU : D.U ⊆ B) :
    IsGraphBij (GM12.drawingInSubspace D B hDU).toGraph D.toGraph
      (Subtype.val : B → S) (image (Subtype.val : B → S)) := by
  let J := GM12.drawingInSubspace D B hDU
  let f : B → S := Subtype.val
  have hfi : Function.Injective f := Subtype.val_injective
  have hf : IsClosedEmbedding f := hB.isClosedEmbedding_subtypeVal
  have hV : f '' J.V = D.V := by
    change f '' (GM12.drawingInSubspace D B hDU).V = D.V
    rw [GM12.drawingInSubspace_V]
    apply image_preimage_eq_iff.mpr
    intro x hx
    exact ⟨⟨x, hDU (D.V_subset_U hx)⟩, rfl⟩
  have hE : ∀ e ∈ D.E, f '' (f ⁻¹' e) = e := by
    intro e he
    apply image_preimage_eq_iff.mpr
    intro x hx
    exact ⟨⟨x, hDU (he.2.1 hx).1⟩, rfl⟩
  have hmapE : MapsTo (image f) J.E D.E := by
    intro e he
    rw [GM12.drawingInSubspace_E] at he
    obtain ⟨e', he', rfl⟩ := he
    rw [hE e' he']
    exact he'
  have hviff : ∀ x : B, x ∈ J.V ↔ f x ∈ D.V := by
    intro x
    change x ∈ (GM12.drawingInSubspace D B hDU).V ↔ _
    rw [GM12.drawingInSubspace_V]
    rfl
  refine {
    bijV := ⟨fun x hx => (hviff x).mp hx, hfi.injOn, fun x hx =>
      ⟨⟨x, hDU (D.V_subset_U hx)⟩, (hviff _).mpr hx, rfl⟩⟩
    bijE := ⟨hmapE, (image_injective.mpr hfi).injOn, ?_⟩
    isLink := ?_ }
  · intro e he
    refine ⟨f ⁻¹' e, ?_, hE e he⟩
    change f ⁻¹' e ∈ (GM12.drawingInSubspace D B hDU).E
    rw [GM12.drawingInSubspace_E]
    exact mem_image_of_mem (preimage f) he
  · intro e he x hx y hy
    constructor
    · intro hl
      refine ⟨hmapE he, (hviff x).mp hx, (hviff y).mp hy, ?_⟩
      change closure (f '' e) ∩ D.V = {f x, f y}
      rw [hf.closure_image_eq, ← hV, ← image_inter hfi, hl.2.2.2, image_pair]
    · intro hl
      refine ⟨he, hx, hy, ?_⟩
      apply (image_injective.mpr hfi)
      rw [image_inter hfi, ← hf.closure_image_eq, hV, image_pair]
      exact hl.2.2.2

end GraphMinor.GM08
