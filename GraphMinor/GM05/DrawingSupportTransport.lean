module

public import GraphMinor.Surface.Defs
import GraphMinor.Planar.Defs
import GraphMinor.GM14.RigidMap
import GraphMinor.GM14.Section8Core

/-!
# Carrying a graph drawing by an embedding of its support

In GM V, (8.12), the cut circle misses the drawing. The homeomorphism
of complements therefore embeds its compact support in the new
surface. Extend the resulting support homeomorphism to maps on points
and use the library drawing transport, which preserves the graph.
-/

public section
namespace GraphMinor.GM05
open Set Topology Surface GM14.Whitney
universe u v w w'

/-- An embedding of the compact support of a graph drawing carries
that graph to the target space, with the image of the embedding as
the new support. -/
theorem exists_graphDrawing_of_support_embedding {α : Type u} {β : Type v}
    {S : Type w} {T : Type w'} [TopologicalSpace S] [TopologicalSpace T]
    [T2Space S] [T2Space T] [CompactSpace S] [Nonempty S] [Nonempty T]
    {H : Graph α β} (Γ : GraphDrawing H S) (j : Γ.drawing.U → T) (hj : IsEmbedding j) :
    ∃ Δ : GraphDrawing H T, Δ.drawing.U = range j := by
  let e := hj.homeomorphImage univ
  let e' : Γ.drawing.U ≃ₜ range j :=
    (Homeomorph.Set.univ Γ.drawing.U).symm.trans
      (e.trans (Homeomorph.setCongr (image_univ)))
  obtain ⟨f,f',hf,hc,hc',him,hl⟩ := GM14.exists_extensions e'
  have hp : PH Γ.drawing.U (range j) f f' := by
    refine ⟨fun x hx ↦ him ▸ mem_image_of_mem f hx,?_,hl,?_,hc,hc'⟩
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := him.symm ▸ hy
      rw [hl hx]
      exact hx
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := him.symm ▸ hy
      rw [hl hx]
  let D := mapD hp Γ.drawing.isClosed_U.isCompact Γ.drawing (Subset.refl _)
  exact ⟨GraphDrawing.ofIso Γ.iso ⟨D,mapIso hp Γ.drawing.isClosed_U.isCompact Γ.drawing (Subset.refl _)⟩,
    him⟩

/-- An embedding of the compact support of a graph drawing carries
that graph to the target space. -/
theorem graphDrawing_of_support_embedding {α : Type u} {β : Type v}
    {S : Type w} {T : Type w'} [TopologicalSpace S] [TopologicalSpace T]
    [T2Space S] [T2Space T] [CompactSpace S] [Nonempty S] [Nonempty T]
    {H : Graph α β} (Γ : GraphDrawing H S) (j : Γ.drawing.U → T) (hj : IsEmbedding j) :
    Nonempty (GraphDrawing H T) :=
  ⟨(exists_graphDrawing_of_support_embedding Γ j hj).choose⟩

end GraphMinor.GM05
