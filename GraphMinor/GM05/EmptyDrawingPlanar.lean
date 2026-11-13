module

public import GraphMinor.Planar.Defs
import GraphMinor.GM11.PaintingCells
import GraphMinor.GM11.RadialExists
import GraphMinor.Surface.DrawCarry
import GraphMinor.GM19.Section6a

/-!
# Empty drawing supports are planar

A drawing with empty support has no vertices or edges. Its graph is
isomorphic to the empty point drawing on the sphere. This covers empty
ambient spaces in the drawing argument for GM V, (8.13).
-/

public section
namespace GraphMinor.GM05
open Set Surface
universe u v w

/-- A graph drawn with empty support is planar. -/
theorem isPlanar_of_empty_drawing_support {α : Type u} {β : Type v}
    {H : Graph α β} {S : Type w} [TopologicalSpace S]
    (Γ : GraphDrawing H S) (he : Γ.drawing.U=∅) : GraphMinor.IsPlanar H := by
  let Q := SurfaceModel 0 0 0
  let : T2Space Q := (isClosedSurface_model 0 0).2.1
  let D : Drawing Q := GM11.pointsDrawing (finite_empty : (∅ : Set Q).Finite)
  let : IsEmpty Γ.drawing.toGraph.vertexSet := ⟨fun x ↦ by
    have hx := Γ.drawing.V_subset_U x.prop
    rw [he] at hx
    exact hx⟩
  let : IsEmpty Γ.drawing.toGraph.edgeSet := ⟨fun e ↦ by
    obtain ⟨x,hx⟩ := e.prop.1
    have hh := (e.prop.2.1 hx).1
    rw [he] at hh
    exact hh⟩
  let : IsEmpty D.toGraph.vertexSet := by change IsEmpty (∅ : Set Q); infer_instance
  let : IsEmpty D.toGraph.edgeSet := by
    change IsEmpty (GM11.pointsDrawing (finite_empty : (∅ : Set Q).Finite)).E
    rw [GM11.pointsDrawing_E]
    infer_instance
  let e : Iso Γ.drawing.toGraph D.toGraph := {
    vertexEquiv := Equiv.equivOfIsEmpty _ _
    edgeEquiv := Equiv.equivOfIsEmpty _ _
    isLink_iff := fun e ↦ isEmptyElim e }
  exact IsPlanar.of_graphDrawing (isSurface_model 0 0 0).1 GM19.isSphere_model
    (GraphDrawing.ofIso Γ.iso ⟨D,e⟩)

end GraphMinor.GM05
