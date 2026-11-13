module

public import GraphMinor.Compute.GM06Alg34InteriorComponent
public import GraphMinor.GM06.Alg34InducedRep
import GraphMinor.Surface.Classification

/-!
# Interpreting finite component queries in the represented drawing

The supplied vertex and edge bijections transport walks in both
directions. Thus each computed reachable-label list denotes the actual
drawing component through its source. The supplied cuff bijection then
shows that the finite interior-component test is exactly disjointness
of that component from the surface boundary, as required by VI (3.3)(ii).
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06 GM22 Graph

universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- The explicit supplied bijections transport finite endpoint reachability
exactly to walks in the represented drawing. -/
theorem vertex_reachable_iff (h : GM06DrawingRep x G Δ) (a b : Fin x.n) :
    x.vertexGraph.Reachable a b ↔
      Nonempty (GraphWalk G.toGraph (h.vertex a).val (h.vertex b).val) := by
  rw [x.vertexGraph_reachable_iff, ← h.graph_map_eq]
  constructor
  · rintro ⟨W⟩
    obtain ⟨W', _, _⟩ := mapEmbed_walk h.vertexEmbedding h.edgeEmbedding W
    exact ⟨W'⟩
  · rintro ⟨W⟩
    obtain ⟨W', _, _⟩ := comapEmbed_walk h.vertexEmbedding h.edgeEmbedding W
    exact ⟨W'⟩

/-- The computed component labels denote exactly the actual drawing
component through the supplied source vertex. -/
theorem component_vertexImage (h : GM06DrawingRep x G Δ) (a : Fin x.n) :
    h.vertexImage (x.componentVertices a) =
      (GM06.compOf G.toGraph (h.vertex a).val).vertexSet := by
  ext p
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨(h.vertex b).property,
      (h.vertex_reachable_iff a b).mp ((x.mem_componentVertices_iff a b).mp hb)⟩
  · rintro ⟨hpG, hW⟩
    obtain ⟨b, hb⟩ := h.vertex.surjective ⟨p, hpG⟩
    have hbp : (h.vertex b).val = p := congrArg Subtype.val hb
    refine ⟨b, (x.mem_componentVertices_iff a b).mpr ?_, hbp⟩
    exact (h.vertex_reachable_iff a b).mpr (by simpa only [hbp] using hW)

/-- A finite component misses every supplied cuff vertex exactly when
its represented drawing component misses the surface boundary. -/
theorem isInteriorComponent_iff (h : GM06DrawingRep x G Δ) (a : Fin x.n) :
    x.isInteriorComponent a = true ↔
      Disjoint (GM06.compOf G.toGraph (h.vertex a).val).vertexSet (bd S) := by
  rw [x.isInteriorComponent_eq_true_iff]
  constructor
  · intro htest
    apply Set.disjoint_left.mpr
    rintro p ⟨hpG, hW⟩ hpbd
    obtain ⟨C, hC, hpC⟩ := (show p ∈ ⋃₀ cuffs S from (sUnion_cuffs (S := S)).symm ▸ hpbd)
    obtain ⟨i, hi⟩ := h.cuff.surjective ⟨C, hC⟩
    have hpcuff : p ∈ (h.cuff i).val := by simpa only [hi] using hpC
    have hpimage : p ∈ (fun b => (h.vertex b).val) '' GM06DrawingData.block x.cuffs[i] :=
      (h.cuff_vertices i).symm ▸ ⟨hpG, hpcuff⟩
    obtain ⟨b, hb, hbp⟩ := hpimage
    exact htest x.cuffs[i] (List.getElem_mem i.isLt) b hb
      ((h.vertex_reachable_iff a b).mpr (by simpa only [hbp] using hW))
  · intro hdis L hL b hb hreach
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hL
    let j : Fin x.cuffs.length := ⟨i, hi⟩
    have himage : (h.vertex b).val ∈
        (fun b => (h.vertex b).val) '' GM06DrawingData.block x.cuffs[j] :=
      ⟨b, by change b ∈ x.cuffs[j]; rw [show x.cuffs[j] = L from heq]; exact hb, rfl⟩
    have hpcuff : (h.vertex b).val ∈ (h.cuff j).val :=
      ((h.cuff_vertices j) ▸ himage).2
    have hpbd : (h.vertex b).val ∈ bd S :=
      (sUnion_cuffs (S := S)) ▸ (show (h.vertex b).val ∈ ⋃₀ cuffs S from ⟨_, (h.cuff j).property, hpcuff⟩)
    exact Set.disjoint_left.mp hdis
      ⟨(h.vertex b).property, (h.vertex_reachable_iff a b).mp hreach⟩ hpbd

end GraphMinor.Compute.GM06DrawingRep
