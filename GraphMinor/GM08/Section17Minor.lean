module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM07.Defs
import GraphMinor.GM07.Section9
import GraphMinor.GM08.Section18Drawing
import GraphMinor.GM08.Section18Orient

/-!
# The cylinder minor theorem for graft drawings

The threshold in VII (9.3) depends on the target's vertex and edge
counts. Express it using the abstract graft, so moving the target to
align its boundary vertices does not change the threshold. Orient the
two drawings and transfer the resulting boundary-rooted minor back to
a graft simulation. This is the minor-theorem step in VIII (17.2).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface

universe u v w

/-- The numerical threshold from VII (9.3), expressed using the vertex
and edge counts of the target graft in VIII (17.2), page 284. -/
noncomputable def cylinderMinorThreshold {α : Type u} {β : Type v}
    (Y : Graft α β) : ℕ :=
  let t := V(Y.G).ncard + E(Y.G).ncard
  (84 * (t + 2) * GM07.vModel 0 0 (t + 4) (2 * t + 4)) * 5 ^ t

/-- Moving a graft drawing leaves the cylinder threshold unchanged. -/
theorem cylinderMinorThreshold_eq {S : Type w} [TopologicalSpace S]
    {α : Type u} {β : Type v} {Y : Graft α β}
    (DY : GraftDrawing Y.G Y.T S) :
    cylinderMinorThreshold Y = GM07.rCylinderBound DY.drawing *
      5 ^ (DY.drawing.V.ncard + DY.drawing.E.ncard) := by
  simp only [cylinderMinorThreshold, GM07.rCylinderBound,
    ncard_drawing_vertices_eq DY, ncard_drawing_edges_eq DY]

/-- The application of VII (9.3) within VIII (17.2), page 284.
For aligned boundary vertices, its geometric and linkage conditions
give a simulation of the target graft. -/
theorem isGraftSimulatedIn_of_cylinder_minor_configuration {S : Type w}
    [TopologicalSpace S] [T1Space S] [Nonempty S]
    (hS : IsSurface S) (he : Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    {C₁ C₂ : Set S} (hcuffs : cuffs S = {C₁, C₂}) (hne : C₁ ≠ C₂)
    {α : Type u} {β : Type v} {Y X : Graft α β}
    (DY : GraftDrawing Y.G Y.T S) (DX : GraftDrawing X.G X.T S)
    (hbd : DX.drawing.V ∩ bd S = DY.drawing.V ∩ bd S)
    {F₁ F₂ : Set S} (hN₁ : DX.drawing.IsNormal F₁) (hN₂ : DX.drawing.IsNormal F₂)
    (horder : GM07.CylinderOArcsInOrder C₁ F₂ F₁ C₂)
    (hinside : ∀ x ∈ F₂, GM07.IsPointInsideSurroundingOArc C₁ F₁ x)
    (hoff₁ : Disjoint F₁ (bd S)) (hoff₂ : Disjoint F₂ (bd S))
    (hline : ∀ F : Set S, DX.drawing.IsNormal F → IsLine F →
      (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
      2 * cylinderMinorThreshold Y ≤ (DX.drawing.V ∩ F).ncard)
    (hpaths : cylinderMinorThreshold Y ≤ GM07.maxDisjointPaths DX.drawing F₁ F₂)
    (hc₁ : (DX.drawing.V ∩ C₁).ncard ≤ GM07.maxDisjointPaths DX.drawing F₁ C₁)
    (hc₂ : (DX.drawing.V ∩ C₂).ncard ≤ GM07.maxDisjointPaths DX.drawing F₂ C₂) :
    IsGraftSimulatedIn Y X := by
  obtain ⟨H, hH⟩ := exists_surfaceDigraph_for_surface_reduction DY.drawing
  obtain ⟨G, hG⟩ := exists_surfaceDigraph_for_surface_reduction DX.drawing
  have hbound : GM07.rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard) =
      cylinderMinorThreshold Y := by
    rw [hH]
    exact (cylinderMinorThreshold_eq DY).symm
  have hHproper : H.IsProper := by change H.G.IsProper; rw [hH]; exact DY.isProper
  have hGproper : G.IsProper := by change G.G.IsProper; rw [hG]; exact DX.isProper
  apply isGraftSimulatedIn_of_drawn_boundaryRootedMinor DY DX hH hG
  apply GM07.theorem_9_3_proof hS he hcuffs hne H G hHproper hGproper
  · simpa only [hH, hG] using hbd
  · simpa only [hG] using hN₁
  · simpa only [hG] using hN₂
  · exact horder
  · exact hinside
  · exact hoff₁
  · exact hoff₂
  · simpa only [hG, hbound] using hline
  · simpa only [hG, hbound] using hpaths
  · simpa only [hG] using hc₁
  · simpa only [hG] using hc₂

end GraphMinor.GM08
