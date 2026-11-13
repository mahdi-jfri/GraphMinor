module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM07.Defs
import GraphMinor.GM12.Section3HomeoWalks
import GraphMinor.GM07.Section3

/-!
# Moving a graft drawing by a homeomorphism

The vertex and edge bijections of a graft drawing move with the drawing.
The boundary condition is preserved because homeomorphisms preserve the
boundary. This supports the boundary alignment in VIII (18.1), page 285.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u v w w'

/-- Move a graft drawing by a homeomorphism of its surface. -/
def mapGraftDrawing {S : Type w} {T : Type w'} [TopologicalSpace S] [TopologicalSpace T]
    {α : Type u} {β : Type v} {X : Graft α β} (e : S ≃ₜ T)
    (D : GraftDrawing X.G X.T S) : GraftDrawing X.G X.T T where
  drawing := GM07.mapDrawingHomeo e D.drawing
  iso :=
    { vertexEquiv := D.iso.vertexEquiv.trans
        { toFun := fun v => ⟨e v.1, ⟨v.1, v.2, rfl⟩⟩
          invFun := fun w => ⟨e.symm w.1, by
            obtain ⟨x, hx, hxe⟩ := w.2
            change e.symm w.1 ∈ D.drawing.V
            rw [← hxe, e.symm_apply_apply]
            exact hx⟩
          left_inv := fun v => Subtype.ext (e.symm_apply_apply v.1)
          right_inv := fun w => Subtype.ext (e.apply_symm_apply w.1) }
      edgeEquiv := D.iso.edgeEquiv.trans
        { toFun := fun ed => ⟨e '' ed.1, by
            change e '' ed.1 ∈ (GM07.mapDrawingHomeo e D.drawing).E
            rw [GM12.mapDrawingHomeo_edges]
            exact ⟨ed.1, ed.2, rfl⟩⟩
          invFun := fun fd => ⟨e.symm '' fd.1, by
            have hfd : fd.1 ∈ (GM07.mapDrawingHomeo e D.drawing).E := fd.2
            rw [GM12.mapDrawingHomeo_edges] at hfd
            obtain ⟨ed, hed, h_eq⟩ := hfd
            change e.symm '' fd.1 ∈ D.drawing.E
            have hsymm : e.symm '' fd.1 = ed := by
              rw [← h_eq, image_image]
              simp [e.symm_apply_apply]
            rwa [hsymm]⟩
          left_inv := fun ed => Subtype.ext (show e.symm '' (e '' ed.1) = ed.1 by
            rw [image_image]; simp [e.symm_apply_apply])
          right_inv := fun fd => Subtype.ext (show e '' (e.symm '' fd.1) = fd.1 by
            rw [image_image]; simp [e.apply_symm_apply]) }
      isLink_iff := fun ed x y => by
        rw [D.iso.isLink_iff ed x y]
        constructor
        · exact GM12.isLink_mapDrawingHomeo e D.drawing
        · intro hl
          have hl' := GM12.isLink_mapDrawingHomeo e.symm (GM07.mapDrawingHomeo e D.drawing) hl
          rw [GM12.mapDrawingHomeo_symm] at hl'
          simpa [image_image, e.symm_apply_apply] using hl' }
  isProper := GM07.IsProper.map_homeo e D.isProper
  T_subset_V := D.T_subset_V
  mem_bd_iff v hv := by
    change e (D.iso.vertexEquiv ⟨v, hv⟩).1 ∈ bd T ↔ v ∈ X.T
    rw [← image_bd_homeomorph e, e.injective.mem_set_image]
    exact D.mem_bd_iff v hv

/-- The underlying drawing of the transported graft drawing. -/
theorem mapGraftDrawing_drawing {S : Type w} {T : Type w'}
    [TopologicalSpace S] [TopologicalSpace T] {α : Type u} {β : Type v} {X : Graft α β}
    (e : S ≃ₜ T) (D : GraftDrawing X.G X.T S) :
    (mapGraftDrawing e D).drawing = GM07.mapDrawingHomeo e D.drawing := by rfl

end GraphMinor.GM08
