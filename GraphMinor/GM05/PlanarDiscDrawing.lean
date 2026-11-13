module

public import GraphMinor.Planar.Defs
import GraphMinor.GM05.DrawingSupportTransport
import GraphMinor.Surface.ModelCriterion
import GraphMinor.Surface.DrawCarry
import GraphMinor.GM19.Section6a

/-!
# A drawing contained in a disc is planar

For GM V, (8.13), use the disc chart, of a closed or an open disc, to embed the support in the
canonical sphere and carry its graph isomorphism along with it.
-/

public section
namespace GraphMinor.GM05
open Set Topology Surface
universe u v

/-- A graph drawing supported by a closed disc is a planar graph. -/
theorem isPlanar_of_drawing_in_disc {α : Type u} {β : Type v}
    {H : Graph α β} {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [Nonempty S] (Γ : GraphDrawing H S) {D : Set S} (hD : IsClosedDisc D)
    (hsub : Γ.drawing.U ⊆ D) : GraphMinor.IsPlanar H := by
  obtain ⟨φ⟩ := hD
  obtain ⟨e⟩ := (GM19.isSphere_model : IsSphere (SurfaceModel 0 0 0))
  let Q := SurfaceModel 0 0 0
  let : T2Space Q := (isClosedSurface_model 0 0).2.1
  let : Nonempty Q := ⟨e.symm (OnePoint.infty)⟩
  let j₀ : Γ.drawing.U → D := fun x ↦ ⟨x.val,hsub x.prop⟩
  have hj₀ : IsEmbedding j₀ := IsEmbedding.subtypeVal.codRestrict _ _
  let j : Γ.drawing.U → Q := fun x ↦ e.symm ((φ.symm (j₀ x)).val : OnePoint EuclideanPlane)
  have hj : IsEmbedding j := e.symm.isEmbedding.comp
    (OnePoint.isOpenEmbedding_coe.isEmbedding.comp
      (IsEmbedding.subtypeVal.comp (φ.symm.isEmbedding.comp hj₀)))
  obtain ⟨Δ⟩ := graphDrawing_of_support_embedding Γ j hj
  exact IsPlanar.of_graphDrawing (isSurface_model 0 0 0).1 GM19.isSphere_model Δ

/-- A graph drawing supported by an open disc is a planar graph. -/
theorem isPlanar_of_drawing_in_open_disc {α : Type u} {β : Type v}
    {H : Graph α β} {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [Nonempty S] (Γ : GraphDrawing H S) {D : Set S} (hD : IsOpenDisc D)
    (hsub : Γ.drawing.U ⊆ D) : GraphMinor.IsPlanar H := by
  obtain ⟨φ⟩ := hD.2
  obtain ⟨e⟩ := (GM19.isSphere_model : IsSphere (SurfaceModel 0 0 0))
  let Q := SurfaceModel 0 0 0
  let : T2Space Q := (isClosedSurface_model 0 0).2.1
  let : Nonempty Q := ⟨e.symm (OnePoint.infty)⟩
  let j₀ : Γ.drawing.U → D := fun x ↦ ⟨x.val,hsub x.prop⟩
  have hj₀ : IsEmbedding j₀ := IsEmbedding.subtypeVal.codRestrict _ _
  let j : Γ.drawing.U → Q := fun x ↦ e.symm ((φ.symm (j₀ x)).val : OnePoint EuclideanPlane)
  have hj : IsEmbedding j := e.symm.isEmbedding.comp
    (OnePoint.isOpenEmbedding_coe.isEmbedding.comp
      (IsEmbedding.subtypeVal.comp (φ.symm.isEmbedding.comp hj₀)))
  obtain ⟨Δ⟩ := graphDrawing_of_support_embedding Γ j hj
  exact IsPlanar.of_graphDrawing (isSurface_model 0 0 0).1 GM19.isSphere_model Δ

end GraphMinor.GM05
