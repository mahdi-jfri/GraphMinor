module

public import GraphMinor.GM07.Defs
public import GraphMinor.Statement
import GraphMinor.GM08.Section15PullbackEdges
import Mathlib.Combinatorics.Graph.Maps

/-!
# Keeping the old edge labels after a cut

Relabel each lifted edge by the old edge of which it is the preimage.
The cutting map then maps the lifted graph exactly onto the original
graph. This gives the graph quotient used to reconstruct a short tube
from its disc cut in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface Graph

universe w

/-- The pulled-back graph, with the old edge labels, maps exactly to the
original graph. This is the quotient graph in the short-tube argument
of VIII (15.4), page 282. -/
theorem exists_cut_graph_with_old_edges {S Y : Type w} [TopologicalSpace S]
    [TopologicalSpace Y] {ψ : Y → S} (hc : Continuous ψ) (hclosed : IsClosedMap ψ)
    (hs : Function.Surjective ψ) {G : Drawing S} {G' : Drawing Y}
    (hp : GM07.IsPullbackDrawing ψ G G')
    (he : ∀ e' ∈ G'.E, ∃ e ∈ G.E, e' = ψ ⁻¹' e) :
    ∃ (K : Graph Y (Set S)) (i : Iso K G'.toGraph),
      V(K) = G'.V ∧ E(K) = G.E ∧
      (∀ v : V(K), (i.vertexEquiv v).1 = v.1) ∧ K.map ψ = G.toGraph := by
  classical
  have hE := pullback_drawing_edges_eq hs hp he
  have hmem : ∀ e ∈ G.E, ψ ⁻¹' e ∈ G'.E := fun e he => hE.symm ▸ mem_image_of_mem _ he
  let K : Graph Y (Set S) := {
    vertexSet := G'.V
    edgeSet := G.E
    IsLink := fun e x y => e ∈ G.E ∧ G'.toGraph.IsLink (ψ ⁻¹' e) x y
    isLink_symm := by
      intro e he
      refine ⟨?_⟩
      intro x y h
      exact ⟨h.1, h.2.symm⟩
    eq_or_eq_of_isLink_of_isLink := by
      intro e x y z w h h'
      exact h.2.left_eq_or_eq h'.2
    edge_mem_iff_exists_isLink := fun e => by
      constructor
      · intro he
        obtain ⟨x, y, hl⟩ := G'.toGraph.exists_isLink_of_mem_edgeSet (hmem e he)
        exact ⟨x, y, he, hl⟩
      · rintro ⟨x, y, he, _⟩
        exact he
    left_mem_of_isLink := by
      intro e x y h
      exact h.2.left_mem }
  have hbij : BijOn (preimage ψ) G.E G'.E := by
    refine ⟨hmem, hs.preimage_injective.injOn, ?_⟩
    intro e he'
    obtain ⟨d, hd, rfl⟩ := he e he'
    exact ⟨d, hd, rfl⟩
  let ee : G.E ≃ G'.E := hbij.equiv _
  let i : Iso K G'.toGraph := by
    refine ⟨Equiv.refl _, ee, ?_⟩
    intro e x y
    change (e.1 ∈ G.E ∧ G'.toGraph.IsLink (ψ ⁻¹' e.1) x.1 y.1) ↔
      G'.toGraph.IsLink (ψ ⁻¹' e.1) x.1 y.1
    exact and_iff_right e.2
  refine ⟨K, i, rfl, rfl, (fun _ => rfl), ?_⟩
  apply Graph.ext
  · change ψ '' G'.V = G.V
    rw [hp.2, hs.image_preimage]
  · intro e x y
    change (∃ a b, (e ∈ G.E ∧ G'.toGraph.IsLink (ψ ⁻¹' e) a b) ∧
      ψ a = x ∧ ψ b = y) ↔ G.toGraph.IsLink e x y
    constructor
    · rintro ⟨a, b, ⟨he, hl⟩, rfl, rfl⟩
      exact isLink_image_of_pullback_edge hc hclosed hs hp he hl
    · intro hl
      obtain ⟨a, b, hab⟩ := G'.toGraph.exists_isLink_of_mem_edgeSet (hmem e hl.edge_mem)
      have him := isLink_image_of_pullback_edge hc hclosed hs hp hl.edge_mem hab
      rcases him.eq_and_eq_or_eq_and_eq hl with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨a, b, ⟨hl.edge_mem, hab⟩, ha, hb⟩
      · exact ⟨b, a, ⟨hl.edge_mem, hab.symm⟩, hb, ha⟩

end GraphMinor.GM08
