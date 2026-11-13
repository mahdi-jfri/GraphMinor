module

public import GraphMinor.GM19.CutMap
public import GraphMinor.Surface.SurfaceGraph
public import GraphMinor.GM19.CutDrawing2
import GraphMinor.GM19.Section6Tri
import GraphMinor.GM19.CutTwo

/-!
# Cutting a finite graph made of circles and lines

A finite graph with no isolated vertices gives a drawing whose edges are
lines. If boundary contacts are vertices and the graph together with the
cuffs is made of the indicated circles and joining lines, the proved
finite-drawing cut construction applies. This is the common construction
for the remaining schism shapes in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- Construct a cut along the graph of a schism from its circles and
joining lines. All inputs describe the graph and its contacts with the
boundary. This is the construction step for VIII (18.2), page 286. -/
theorem exists_cutMap_of_graph_frame {S : Type} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {V : Set S} {E 𝓐 𝓛 : Set (Set S)}
    (hg : IsGraph V E) (hno : V ⊆ ⋃₀ E) (hbd : gr V E ∩ bd S ⊆ V)
    (hframe : GM19.IsCutFrame S 𝓐 𝓛) (hcover : bd S ∪ gr V E = ⋃₀ 𝓐 ∪ ⋃₀ 𝓛) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (ψ : Y → S),
      IsSurface Y ∧ GM19.IsCutMap ψ (gr V E) := by
  have : T2Space S := hS.2.1
  let K := hg.toDrawing
  have hlines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧
      closure e ∩ K.V = {u, v} ∧ IsLineWithEnds (closure e) u v := by
    change ∀ e ∈ arcComponentsIn (gr V E \ V), _
    rw [GM19.IsGraphD.arcComponents_eq hg]
    rintro e ⟨f, hf, rfl⟩
    obtain ⟨u, v, huv, hl, hi⟩ := hg.edge f hf
    rw [GM19.IsGraphD.closure_diff hg hf]
    exact ⟨u, v, huv, hi, hl⟩
  have hKbd : K.U ∩ bd S ⊆ K.V := hbd
  have hKne : K.V ⊆ ⋃ e ∈ arcComponentsIn (K.U \ K.V), closure e := by
    change V ⊆ ⋃ e ∈ arcComponentsIn (gr V E \ V), closure e
    intro x hx
    obtain ⟨e, he, hxe⟩ := hno hx
    apply mem_iUnion₂.mpr
    refine ⟨e \ V, ?_, ?_⟩
    · rw [GM19.IsGraphD.arcComponents_eq hg]
      exact mem_image_of_mem _ he
    · rw [GM19.IsGraphD.closure_diff hg he]
      exact hxe
  obtain ⟨Y, tY, _, ψ, hY, hcut, _⟩ :=
    GM19.exists_cut_drawing hS hlines hKbd hKne hframe hcover
  exact ⟨Y, tY, ψ, hY, hcut⟩

end GraphMinor.GM08
