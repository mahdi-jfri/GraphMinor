module

public import GraphMinor.GM05.ConnectedTransfer
import GraphMinor.GM01.Basic
import GraphMinor.Minor.Basic
import GraphMinor.GM16.Defs

/-!
# Simple targets in a graph and its simple shadow

A model of a simple target needs only disjoint connected branch sets and an
edge between the appropriate pairs. Taking shadows keeps these conditions.
We first extract the model when the ambient edge type is nonempty, then add
unused edge labels to cover an empty ambient edge type as well.
-/

public section
namespace GraphMinor.GM05
open Graph SimpleGraph Set GM01
variable {α β γ : Type*}

private theorem minor_shadow_of_nonempty [Nonempty β]
    {H : (⊤ : SimpleGraph γ).Subgraph} {G : Graph α β}
    (hH : H.verts.Finite) (hV : V(G).Finite) (hE : E(G).Finite)
    (hm : IsIsoMinor (toGraph H) G) : IsIsoMinor (toGraph H) (toGraph (simpleShadow G)) := by
  classical
  obtain ⟨ηv, ηe, hmodel⟩ := exists_isMinorModel_of_isIsoMinor hV hE hm
  have hbranches : ∀ u : γ, ∃ K : Graph α β,
      u ∈ H.verts → K ≤ G ∧ V(K) = ηv u ∧ GraphConnected K := by
    intro u
    by_cases hu : u ∈ H.verts
    · obtain ⟨K, hK, hv, hc⟩ := hmodel.connected u hu
      exact ⟨K, fun _ => ⟨hK.trans Graph.deleteEdges_le, hv, hc⟩⟩
    · exact ⟨G, fun h => (hu h).elim⟩
  choose K hK using hbranches
  apply isIsoMinor_toGraph_of_connected_subgraphs hH hV (fun u => simpleShadow (K u))
  · intro u hu
    exact simpleShadow_mono (hK u hu).1
  · intro u hu
    exact (graphConnected_iff_simpleShadow_connected _).mp (hK u hu).2.2
  · intro u hu v hv hne
    change Disjoint V(K u) V(K v)
    rw [(hK u hu).2.1, (hK v hv).2.1]
    exact hmodel.vertex_disjoint u hu v hv hne
  · intro u v huv
    have hu := H.edge_vert huv
    have hv := H.edge_vert huv.symm
    let e : Sym2 γ := s(u, v)
    have he : (toGraph H).IsLink e u v := ⟨rfl, huv⟩
    obtain ⟨x, hx, hxe⟩ := (hmodel.inc_iff u hu e he.edge_mem).mp he.inc_left
    obtain ⟨y, hy, hye⟩ := (hmodel.inc_iff v hv e he.edge_mem).mp he.inc_right
    have hxy : x ≠ y := by
      intro h
      exact Set.disjoint_left.mp
        (hmodel.vertex_disjoint u hu v hv (H.adj_sub huv)) hx (h.symm ▸ hy)
    have hother : y = hxe.other := hye.eq_of_isLink_of_ne_left hxe.isLink_other hxy.symm
    have hlink : G.IsLink (ηe e) x y := hother.symm ▸ hxe.isLink_other
    refine ⟨x, ?_, y, ?_, hxy, ηe e, hlink⟩
    · change x ∈ V(K u)
      rw [(hK u hu).2.1]
      exact hx
    · change y ∈ V(K v)
      rw [(hK v hv).2.1]
      exact hy

/-- For a finite simple target, taking the shadow of the finite host
preserves and reflects the existence of a minor. The reverse implication
uses the shadow as a minor of the host and also holds for general targets. -/
theorem isIsoMinor_simpleShadow_iff {H : (⊤ : SimpleGraph γ).Subgraph}
    {G : Graph α β} (hH : H.verts.Finite) (hV : V(G).Finite) (hE : E(G).Finite) :
    IsIsoMinor (toGraph H) (toGraph (simpleShadow G)) ↔ IsIsoMinor (toGraph H) G := by
  constructor
  · intro hm
    exact hm.trans (simpleShadow_isIsoMinor G hV hE)
  · intro hm
    have hmlift := Iso.isIsoMinor_right hm (GM16.iso_liftEdgeInl G)
    have hElift : E(GM16.liftEdgeInl G).Finite := hE.image Sum.inl
    have hs := minor_shadow_of_nonempty (G := GM16.liftEdgeInl G) hH hV hElift hmlift
    have heq : simpleShadow (GM16.liftEdgeInl G) = simpleShadow G := by
      ext x y
      · rfl
      · change (x ≠ y ∧ ∃ e, ∃ e₀, e = Sum.inl e₀ ∧ G.IsLink e₀ x y) ↔
          x ≠ y ∧ G.Adj x y
        constructor
        · rintro ⟨hne, _, e, _, he⟩
          exact ⟨hne, e, he⟩
        · rintro ⟨hne, e, he⟩
          exact ⟨hne, Sum.inl e, e, rfl, he⟩
    exact heq ▸ hs

end GraphMinor.GM05
