module

public import GraphMinor.Planar.Defs
public import GraphMinor.GM19.Defs2
import GraphMinor.GM05.MinimalDrawingSurface
import GraphMinor.GM05.MinimalSurfaceIntersection

/-!
# A surface where all drawings of the fixed graph meet

In the proof of GM V, (8.14), choose a minimal drawing surface by the
well-founded genus multiset. It has no unused components for any
drawing. Applying (8.13) therefore makes every pair of drawings meet.
-/

public section
namespace GraphMinor.GM05
open Set Surface GM19
universe u v

/-- The surface choice in the proof of GM V, (8.14), page 113,
from an actual orientable drawing of the nonplanar graph. -/
theorem exists_intersection_surface {α : Type u} {β : Type v}
    {H : Graph α β} (hnp : ¬GraphMinor.IsPlanar H)
    (hex : ∃ (S : Type) (_ : TopologicalSpace S) (_hS : IsClosedSurface S),
      IsOrientableSurface S ∧ Nonempty (GraphDrawing H S)) :
    ∃ (S : Type) (_ : TopologicalSpace S) (_ : IsClosedSurface S),
      IsOrientableSurface S ∧ Nonempty (GraphDrawing H S) ∧
      ∀ Γ Δ : GraphDrawing H S, (Γ.drawing.U ∩ Δ.drawing.U).Nonempty := by
  obtain ⟨S,τ,hS,hO,hD,hmin,hused⟩ := exists_minimal_drawing_surface hnp hex
  refine ⟨S,τ,hS,hO,hD,?_⟩
  intro Γ Δ
  exact theorem_8_13_proof hnp hS hO hmin Γ Δ (fun x _ ↦ hused Δ x)

end GraphMinor.GM05
