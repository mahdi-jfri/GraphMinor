module
public import GraphMinor.GM13.Defs
public import GraphMinor.Minor.Model
import GraphMinor.Minor.Basic

/-!
# From minor models to the models of Graph Minors XIII

The connected branch graphs in the minor-model definition give the
non-null connected subgraphs required by XIII, Section 2, p. 68.
Incidence preservation supplies the endpoints of each model edge.
-/

public section
namespace GraphMinor.Thomason
open Graph Set
universe u v u' v'

private theorem walk_of_reachable {α : Type u} {β : Type v} {G : Graph α β}
    {x y : α} (hx : x ∈ V(G)) (h : Relation.ReflTransGen G.Adj x y) :
    Nonempty (GraphMinor.Surface.GraphWalk G x y) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨.nil hx⟩
  | head hxz _ ih =>
    obtain ⟨e, he⟩ := hxz
    obtain ⟨W⟩ := ih he.right_mem
    exact ⟨.cons he W⟩

/-- A minor model gives a model in the precise sense of XIII, p. 68. -/
theorem hasGraphModel_of_isMinorModel {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'} {G : Graph α β} {H : Graph α' β'}
    {ηv : α' → Set α} {ηe : β' → β} (h : IsMinorModel H G ηv ηe) :
    GM13.HasGraphModel H G := by
  classical
  let K : α' → Graph α β := fun v => if hv : v ∈ V(H) then (h.connected v hv).choose
    else Graph.noEdge ∅ β
  have hK (v : α') (hv : v ∈ V(H)) :
      K v ≤ G.deleteEdges (ηe '' E(H)) ∧ V(K v) = ηv v ∧ GraphConnected (K v) := by
    dsimp only [K]
    rw [dite_eq_left hv]
    exact (h.connected v hv).choose_spec
  apply GM13.hasGraphModel_of_isGraphModel (vMap := K) (eMap := ηe)
  refine { sub_of_mem := fun {v} hv => (hK v hv).1.trans Graph.deleteEdges_le
           nonempty_of_mem := fun {v} hv => (hK v hv).2.2.1
           connected_of_mem := ?_
           disjoint_of_ne := ?_
           edge_mem := fun {e} he => h.edge_mem e he
           link_ends_of_ne := ?_
           loop_ends := ?_
           eMap_injOn := h.edge_injOn }
  · intro v hv x hx y hy
    exact walk_of_reachable hx ((hK v hv).2.2.2 x hx y hy)
  · intro u v hu hv huv
    rw [(hK u hu).2.1, (hK v hv).2.1]
    exact h.vertex_disjoint u hu v hv huv
  · intro e u v huv hne
    obtain ⟨x, hx, hincx⟩ := (h.inc_iff u huv.left_mem e huv.edge_mem).mp huv.inc_left
    obtain ⟨y, hy, hincy⟩ := (h.inc_iff v huv.right_mem e huv.edge_mem).mp huv.inc_right
    obtain ⟨z, hl⟩ := hincx
    have hxy : x ≠ y := (h.vertex_disjoint u huv.left_mem v huv.right_mem hne).ne_of_mem hx hy
    have hyz : y = z := hincy.eq_of_isLink_of_ne_left hl hxy.symm
    refine ⟨x, ?_, y, ?_, hyz ▸ hl⟩
    · rwa [(hK u huv.left_mem).2.1]
    · rwa [(hK v huv.right_mem).2.1]
  · intro e u huu
    have hloop := (h.isLoopAt_iff u huu.left_mem e huu.edge_mem).mp huu
    obtain ⟨x, y, hl⟩ := Graph.exists_isLink_of_mem_edgeSet (h.edge_mem e huu.edge_mem)
    refine ⟨?_, x, ?_, y, ?_, hl⟩
    · intro he
      exact ((hK u huu.left_mem).1.edgeSet_mono he).2 (mem_image_of_mem ηe huu.edge_mem)
    · rw [(hK u huu.left_mem).2.1]
      exact hloop x hl.inc_left
    · rw [(hK u huu.left_mem).2.1]
      exact hloop y hl.inc_right

/-- A finite minor gives a model of XIII whenever the target ambient
edge type is nonempty, so the existing minor-model extraction applies. -/
theorem hasGraphModel_of_isIsoMinor {α : Type u} {β : Type v} [Nonempty β]
    {α' : Type u'} {β' : Type v'} {G : Graph α β} {H : Graph α' β'}
    (hV : V(G).Finite) (hE : E(G).Finite) (h : IsIsoMinor H G) :
    GM13.HasGraphModel H G := by
  obtain ⟨ηv, ηe, hm⟩ := exists_isMinorModel_of_isIsoMinor hV hE h
  exact hasGraphModel_of_isMinorModel hm

end GraphMinor.Thomason
