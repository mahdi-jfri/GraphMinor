module

public import GraphMinor.GM08.Defs
import GraphMinor.GM08.Section18Map
import GraphMinor.GM08.Section18Boundary
import GraphMinor.Surface.InvarianceOfDomain

/-!
# Aligning two graft drawings

When two graft drawings have equal vertex counts on every cuff, move the
target drawing by a cuff-preserving homeomorphism so that their boundary
vertex sets agree. The abstract graft remains the same. This is the
alignment required by VII (9.1) in the proof of VIII (18.1).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- Equal counts on the cuffs let us align the boundary vertices of two
graft drawings by moving the first drawing. -/
theorem exists_graftDrawing_aligned_boundary {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) {α : Type u} {β : Type v} {Y X : Graft α β}
    (DY : GraftDrawing Y.G Y.T S) (DX : GraftDrawing X.G X.T S)
    (hcard : ∀ C ∈ cuffs S, (DY.drawing.V ∩ C).ncard = (DX.drawing.V ∩ C).ncard) :
    ∃ DY' : GraftDrawing Y.G Y.T S,
      DY'.drawing.V ∩ bd S = DX.drawing.V ∩ bd S := by
  have hcounts : ∀ C ∈ cuffs S, ((DY.drawing.V ∩ bd S) ∩ C).ncard =
      ((DX.drawing.V ∩ bd S) ∩ C).ncard := by
    intro C hC
    have hCbd : C ⊆ bd S := by
      obtain ⟨x, hx, rfl⟩ := hC
      exact connectedComponentIn_subset _ _
    rw [inter_assoc, inter_eq_right.mpr hCbd, inter_assoc, inter_eq_right.mpr hCbd]
    exact hcard C hC
  obtain ⟨α, hAB, _⟩ := exists_homeomorph_match_boundary hS
    (DY.drawing.finite_V.inter_of_left (bd S)) (DX.drawing.finite_V.inter_of_left (bd S))
    inter_subset_right inter_subset_right hcounts
  refine ⟨mapGraftDrawing α DY, ?_⟩
  rw [mapGraftDrawing_drawing]
  change α '' DY.drawing.V ∩ bd S = DX.drawing.V ∩ bd S
  calc
    α '' DY.drawing.V ∩ bd S = α '' DY.drawing.V ∩ α '' bd S := by
      rw [image_bd_homeomorph α]
    _ = α '' (DY.drawing.V ∩ bd S) := (image_inter α.injective).symm
    _ = DX.drawing.V ∩ bd S := hAB

end GraphMinor.GM08
