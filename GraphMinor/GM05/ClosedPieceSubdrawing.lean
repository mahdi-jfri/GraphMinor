module

public import GraphMinor.GM05.ConnectedDrawingPieces
import GraphMinor.GM11.Walks

/-!
# Closed pieces separated at vertices

For the planarized union in GM V, (8.14), the support of one star
and the union of the other stars are closed, and their intersections
are marked vertices. An open edge cannot pass from one piece to the
other. A connected star is therefore a connected subdrawing.
-/

public section
namespace GraphMinor.GM05
open Set Surface

/-- A connected closed piece of a drawing, separated from its closed
complementary piece at vertices, is a connected subdrawing. -/
theorem exists_connected_subdrawing_of_closed_pieces {S : Type*}
    [TopologicalSpace S] [T2Space S] (D : Drawing S) {K L : Set S}
    (hK : IsClosed K) (hL : IsClosed L) (hU : D.U = K ∪ L)
    (hKL : K ∩ L ⊆ D.V) (hc : IsPreconnected K) (hv : (K ∩ D.V).Nonempty) :
    ∃ B : Drawing S, B.IsSubdrawing D ∧ B.U = K ∧ B.V = K ∩ D.V ∧
      GraphConnected B.toGraph := by
  have hedge : ∀ e ∈ D.E, (e ∩ K).Nonempty → closure e ⊆ K := by
    intro e he hmeet
    apply closure_minimal ?_ hK
    intro x hxe
    by_contra hxK
    have hecov : e ⊆ K ∪ L := fun y hy ↦ hU ▸ (he.2.1 hy).1
    have hxL : x ∈ L := (hecov hxe).resolve_left hxK
    have heconn : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
    obtain ⟨y,hye,hyK,hyL⟩ := isPreconnected_closed_iff.mp heconn K L hK hL hecov
      hmeet ⟨x,hxe,hxL⟩
    exact (he.2.1 hye).2 (hKL ⟨hyK,hyL⟩)
  exact exists_connected_subdrawing_of_edge_closed_piece D
    (fun x hx ↦ hU.symm ▸ Or.inl hx) hc hv hedge

end GraphMinor.GM05
