module

public import GraphMinor.GM07.Matched
public import GraphMinor.GM08.Section11Transport
import GraphMinor.GM08.Section12Subspace

/-!
# The graph isomorphism into the capped sphere

A matched drawing under an embedding keeps every vertex, edge, and
incidence. Restrict the embedding and its image map to get the graph
bijection. This carries the original graft labels into the adjusted
cylinder in the short-tube construction of VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe u v

/-- An embedding with a matched image drawing gives a graph bijection.
This carries graft labels through the capped-sphere construction of
VIII (15.4), page 282. -/
theorem isGraphBij_of_matched_embedding {S : Type u} {Y : Type v}
    [TopologicalSpace S] [TopologicalSpace Y] [CompactSpace S] [T2Space S] [T2Space Y]
    {f : S → Y} (hf : IsEmbedding f) {G : Drawing S} {G' : Drawing Y}
    (hm : GM07.IsMatched G G' f ∅) :
    IsGraphBij G.toGraph G'.toGraph f (image f) := by
  have hV : f '' G.V = G'.V := by simpa only [sdiff_empty] using hm.image_V
  refine {
    bijV := ⟨fun x hx => (show f x ∈ G'.V from hV ▸ mem_image_of_mem f hx), hf.injective.injOn, ?_⟩
    bijE := ⟨fun e he => (show f '' e ∈ G'.E from hm.image_E.symm ▸ mem_image_of_mem (image f) he),
      (image_injective.mpr hf.injective).injOn, ?_⟩
    isLink := ?_ }
  · intro x hx
    have hx' : x ∈ f '' G.V := hV.symm ▸ hx
    exact hx'
  · intro e he
    change e ∈ G'.E at he
    rw [hm.image_E] at he
    exact he
  · intro e he x hx y hy
    constructor
    · intro hl
      refine ⟨hm.image_E.symm ▸ mem_image_of_mem (image f) he,
        hV ▸ mem_image_of_mem f hx, hV ▸ mem_image_of_mem f hy, ?_⟩
      rw [hm.cap he, hl.2.2.2, image_pair]
    · intro hl
      refine ⟨he, hx, hy, ?_⟩
      apply (image_injective.mpr hf.injective)
      rw [image_pair, ← hm.cap he]
      exact hl.2.2.2

end GraphMinor.GM08
