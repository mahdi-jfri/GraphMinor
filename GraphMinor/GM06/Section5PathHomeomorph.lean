module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM07.Defs
import GraphMinor.GM07.Section3

/-!
# Transporting a path drawing through a homeomorphism

For the endpoint normalization in VI Reduction 3, page 129, a
homeomorphism transports both the simple graph walk and its injective
curve parametrization. Their vertex and edge sets are the respective
images. Thus the image drawing is again a path drawing with the
corresponding ends.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM07

universe u v

/-- A homeomorphism carries a path drawing to a path drawing, including
its simple walk and its prescribed end parametrization. -/
theorem isPathDrawing_map_homeo
    {S : Type u} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]
    (α : S ≃ₜ T) {P : Drawing S} {s t : S} (hP : IsPathDrawing P s t) :
    IsPathDrawing (mapDrawingHomeo α P) (α s) (α t) := by
  constructor
  · obtain ⟨W, hW, hV, hE⟩ := hP.1
    refine ⟨mapWalkHomeo α W, isSimple_mapWalkHomeo α hW, ?_, ?_⟩
    · change α '' P.V = {x | x ∈ (mapWalkHomeo α W).support}
      rw [hV, support_mapWalkHomeo]
      ext x
      simp
    · rw [mapDrawingHomeo_E, hE, edges_mapWalkHomeo]
      ext e
      simp
  · obtain ⟨f, hf⟩ := hP.2
    let g : C(unitInterval, T) := ⟨α ∘ f, α.continuous.comp f.continuous⟩
    refine ⟨g, α.injective.comp hf.1, ?_, congrArg α hf.2.2.1, congrArg α hf.2.2.2⟩
    change range (α ∘ f) = α '' P.U
    rw [range_comp, hf.2.1]

end GraphMinor.GM06
