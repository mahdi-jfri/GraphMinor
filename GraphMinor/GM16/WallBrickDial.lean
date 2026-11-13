module

public import GraphMinor.GM16.WallBrickInterior
public import GraphMinor.GM14.Defs
import GraphMinor.GM16.RectangularDisc
import GraphMinor.GM16.LineDial
import Mathlib.Tactic.Linarith

/-!
# Dials for circles in a brick of the sphere wall

The brick's closed rectangle is a disc, and its open rectangle
misses every vertex and edge of the wall. Its image under the
coordinate embedding has the same properties. A circle contained
in it therefore bounds an empty dial. This proves the bounded
one-face case of the rigidity check in XVI (4.2), page 53.
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface GM14

/-- The one-brick case of the rigidity assertion in XVI (4.2), page 53. -/
theorem sphereWall_exists_isDial_of_circle_in_brick {S : Type*}
    [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S) {θ : ℕ}
    (f : (ℝ × ℝ) → S) (hf : IsEmbedding f)
    (Γ : GraphDrawing (sphereWallGraph θ) S)
    (hV : Γ.drawing.V = range (f ∘ @rectangularGridPoint (2*θ+1) θ))
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val =
      f '' rectangularGridLine e.val)
    (i j : ℕ) (hEven : Even (i+j)) {F : Set S} (hF : IsOArc F)
    (hFC : F ⊆ f '' (Icc (i : ℝ) ((i : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1))) :
    ∃ Δ, IsDial Γ.drawing F Δ := by
  have hC : IsClosedDisc
      (f '' (Icc (i : ℝ) ((i : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1))) :=
    isClosedDisc_image_real_rectangle hf (by linarith) (by linarith)
  apply exists_isDial_of_circle_in_empty_disc hS hC hF hFC
  exact ((sphereWall_drawing_disjoint_open_brick f hf.injective Γ hV hE i j hEven).symm).mono_left
    (interior_image_rectangle_subset hf _ _ _ _)

end GraphMinor.GM16
