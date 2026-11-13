module

public import GraphMinor.GM08.Defs6to18
public import GraphMinor.Surface.Defs
import GraphMinor.GM08.Section12LoopReplacement
import GraphMinor.GM08.Section12CellularFaces
import GraphMinor.GM08.Section12CellularIso
import GraphMinor.GM08.Section9DiscContext

/-!
# Choosing cellular drawings for the disc conclusion

Replace all loops by disjoint empty petals at the same vertices.
The resulting drawing is proper and cellular, and the edge replacement
is an isomorphism fixing every vertex position. Composing that
isomorphism with a graft drawing preserves its root positions. This
proves the cellular drawing existence used to derive the portraits in
VIII, Section 12, filling the assertion on page 272.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u v w

/-- A proper disc drawing can be replaced by a cellular drawing of the
same graph, with all vertices fixed. This supplies the cellular drawing
asserted in VIII, Section 11, page 272, and used in Section 12. -/
theorem exists_cellular_drawing {S : Type w} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) (D : Drawing S) (hprop : D.IsProper) :
    ∃ H : Drawing S, H.IsProper ∧ IsCellularDrawing H ∧
      ∃ a : Iso D.toGraph H.toGraph, ∀ x : Graph.vertexSet D.toGraph,
        (a.vertexEquiv x).1 = x.1 := by
  have : T2Space S := (isSurface_of_closedDisc_univ hS).2.1
  obtain ⟨v, E, H, hE, hEE, hV, hEdges, hU, hpropH⟩ := exists_loop_replacement hS D hprop
  have hcell := isCellularDrawing_loop_replacement hS D H v E
    (fun i => ⟨(hE i).2.1, (hE i).2.2.1, (hE i).2.2.2.1, (hE i).2.2.2.2⟩)
    hEE hV hEdges hU
  obtain ⟨a, ha⟩ := exists_iso_loop_replacement D H v E hE hEE hV hEdges
  exact ⟨H, hpropH, hcell, a, ha⟩

/-- A disc-embeddable graft has a cellular graft drawing. The new graph
isomorphism fixes the vertex positions, hence keeps exactly the same
roots on the boundary. This fills the existence assertion on VIII,
page 272, used in the disc induction of Section 12, page 274. -/
theorem exists_cellular_graftDrawing {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] (hS : IsClosedDisc (univ : Set S))
    (X : Graft α β) (hX : EmbedsGraft S X) :
    ∃ gd : GraftDrawing X.G X.T S, IsCellularDrawing gd.drawing := by
  obtain ⟨gd⟩ := hX
  obtain ⟨H, hHp, hHcell, a, ha⟩ := exists_cellular_drawing hS gd.drawing gd.isProper
  let b : Iso X.G H.toGraph := {
    vertexEquiv := gd.iso.vertexEquiv.trans a.vertexEquiv
    edgeEquiv := gd.iso.edgeEquiv.trans a.edgeEquiv
    isLink_iff := fun e x y => (gd.iso.isLink_iff e x y).trans
      (a.isLink_iff (gd.iso.edgeEquiv e) (gd.iso.vertexEquiv x) (gd.iso.vertexEquiv y)) }
  let gd' : GraftDrawing X.G X.T S := {
    drawing := H
    iso := b
    isProper := hHp
    T_subset_V := X.T_subset
    mem_bd_iff := fun v hv => by
      change (a.vertexEquiv (gd.iso.vertexEquiv ⟨v, hv⟩)).1 ∈ bd S ↔ v ∈ X.T
      rw [ha]
      exact gd.mem_bd_iff v hv }
  exact ⟨gd', hHcell⟩

end GraphMinor.GM08
