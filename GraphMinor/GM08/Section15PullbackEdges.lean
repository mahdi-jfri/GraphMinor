module

public import GraphMinor.GM07.Defs
import GraphMinor.GM11.DrawingOps
import GraphMinor.GM11.Walks
import Mathlib.Topology.Maps.Basic

/-!
# The edges of the cut drawing

Each edge of the cut drawing is the preimage of one old edge. Surjectivity
and the underlying-set identities give the converse. A continuous closed
map sends each lifted edge closure onto its old closure, so it also sends
its ends to the old ends. This supplies the graph map in the root
identification step of VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

/-- The edges of a pulled-back drawing correspond bijectively to the
old edges, when its edge construction uses their preimages. This is
used for the short-tube disc cut in VIII (15.4), page 282. -/
theorem pullback_drawing_edges_eq {S Y : Type w} [TopologicalSpace S]
    [TopologicalSpace Y] {ψ : Y → S} (hs : Function.Surjective ψ)
    {G : Drawing S} {G' : Drawing Y} (hp : GM07.IsPullbackDrawing ψ G G')
    (he : ∀ e' ∈ G'.E, ∃ e ∈ G.E, e' = ψ ⁻¹' e) :
    G'.E = (preimage ψ) '' G.E := by
  apply subset_antisymm
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := he e' he'
    exact mem_image_of_mem _ he
  · rintro _ ⟨e, heG, rfl⟩
    obtain ⟨x, hx⟩ := heG.1
    obtain ⟨y, hxy⟩ := hs x
    have hyU : y ∈ G'.U := hp.1 ▸ (show y ∈ ψ ⁻¹' G.U from (show ψ y ∈ G.U from hxy.symm ▸ (heG.2.1 hx).1))
    have hyV : y ∉ G'.V := by
      rw [hp.2]
      exact fun h => (heG.2.1 hx).2 (hxy ▸ h)
    obtain ⟨e', he', hye'⟩ := G'.exists_edge_of_mem hyU hyV
    obtain ⟨d, hd, heq⟩ := he e' he'
    have hxd : x ∈ d := by
      have hy : y ∈ ψ ⁻¹' d := heq ▸ hye'
      exact hxy ▸ hy
    have hde : d = e := G.edge_eq_of_mem hd heG hxd hx
    rw [← hde, ← heq]
    exact he'

/-- The cutting map sends the ends of every lifted edge to the ends of
the old edge, including a loop when the two images coincide. This is
the graph map used in the reconstruction in VIII (15.4), page 282. -/
theorem isLink_image_of_pullback_edge {S Y : Type w} [TopologicalSpace S]
    [TopologicalSpace Y] {ψ : Y → S} (hc : Continuous ψ) (hclosed : IsClosedMap ψ)
    (hs : Function.Surjective ψ) {G : Drawing S} {G' : Drawing Y}
    (hp : GM07.IsPullbackDrawing ψ G G') {e : Set S} (he : e ∈ G.E)
    {x y : Y} (hl : G'.toGraph.IsLink (ψ ⁻¹' e) x y) :
    G.toGraph.IsLink e (ψ x) (ψ y) := by
  have himg : ψ '' closure (ψ ⁻¹' e) = closure e := by
    rw [← hclosed.closure_image_eq_of_continuous hc, hs.image_preimage]
  refine ⟨he, ?_, ?_, ?_⟩
  · have hx : x ∈ G'.V := hl.2.1
    rw [hp.2] at hx
    exact hx
  · have hy : y ∈ G'.V := hl.2.2.1
    rw [hp.2] at hy
    exact hy
  have hcap : ψ '' (closure (ψ ⁻¹' e) ∩ G'.V) = closure e ∩ G.V := by
    rw [hp.2, image_inter_preimage, himg]
  rw [← hcap, hl.2.2.2, image_pair]

end GraphMinor.GM08
