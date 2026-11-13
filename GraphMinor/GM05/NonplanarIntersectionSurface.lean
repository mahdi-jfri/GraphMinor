module

public import GraphMinor.Planar.Defs
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM05.HandleDrawingExistence
import GraphMinor.GM05.ComponentHandleModels
import GraphMinor.GM05.MinimalComponentModelSurface
import GraphMinor.GM05.ComponentModelRegions
import GraphMinor.GM05.DisjointDrawingPlanar
import GraphMinor.Surface.ModelCriterion
import GraphMinor.Surface.DrawCarry

/-!
# The intersection surface for a finite nonplanar graph

This closes the surface choice used in GM V, (8.14). Draw the graph
on a closed handle model, minimize the component genus multiset while
retaining the actual handle-model representations, and discard unused
components. The circle-cut argument puts each region in an open disc.
A disjoint second drawing would then be planar, a contradiction.
-/

public section
namespace GraphMinor.GM05
open Set Graph Surface
universe u v

/-- The surface choice and drawing-intersection claim used in GM V,
proof of (8.14), page 113. The hypotheses concern only the given finite
nonplanar graph. Component handle-model homeomorphisms are retained
through the proof's minimal-surface choice and cuts. -/
theorem exists_surface_with_intersecting_drawings {α : Type u} {β : Type v}
    (H : Graph α β) (hV : V(H).Finite) (hE : E(H).Finite) (hnp : ¬GraphMinor.IsPlanar H) :
    ∃ (S : Type) (_ : TopologicalSpace S) (_ : IsClosedSurface S),
      Nonempty (GraphDrawing H S) ∧
      ∀ Γ Δ : GraphDrawing H S,(Γ.drawing.U∩Δ.drawing.U).Nonempty := by
  obtain ⟨a,hdraw⟩ := exists_handle_model_drawing H hV hE
  have hS₀ := isClosedSurface_model a 0
  let : ConnectedSpace (SurfaceModel a 0 0) := (modelCriterion.1 a 0 0).2
  have hmodels₀ := component_handle_models_of_connected (Homeomorph.refl (SurfaceModel a 0 0))
  obtain ⟨S,τ,hS,hmodels,hdraw,hmin,hused⟩ := exists_minimal_component_model_surface hnp
    ⟨SurfaceModel a 0 0,inferInstance,hS₀,hmodels₀,hdraw⟩
  refine ⟨S,τ,hS,hdraw,?_⟩
  intro Γ Δ
  by_contra he
  have hdis : Disjoint Γ.drawing.U Δ.drawing.U :=
    disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp he)
  exact hnp (isPlanar_of_disjoint_disc_regions hS Γ Δ.drawing
    (fun r hr ↦ lemma_8_14_component_model_regions hS hmodels hmin Δ (fun x _ ↦ hused Δ x) hr) hdis)

end GraphMinor.GM05
