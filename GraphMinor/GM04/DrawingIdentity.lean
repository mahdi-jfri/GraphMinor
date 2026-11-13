module

public import GraphMinor.Surface.Defs
import GraphMinor.GM11.Walks

/-!
# Walks in a drawing with fixed vertices

The drawing in IV (9.2), page 254, represents each vertex by itself.
Its edge bijection transfers walks in both directions, preserving their
vertex lists. Pulling back a simple closed walk shows that the drawing
of a forest is again a forest.
-/

public section

namespace GraphMinor.GM04

open Set Surface Graph

universe u v

open Classical in
private noncomputable def drawingEdgeMap {S : Type u} {β : Type v}
    [TopologicalSpace S] {F : Graph S β} (Γ : GraphDrawing F S) (e : β) : Set S :=
  if he : e ∈ E(F) then (Γ.iso.edgeEquiv ⟨e, he⟩).val else ∅

private theorem drawing_link {S : Type u} {β : Type v} [TopologicalSpace S]
    {F : Graph S β} (Γ : GraphDrawing F S)
    (hID : ∀ v : V(F), (Γ.iso.vertexEquiv v).val = v.val)
    {e : β} {x y : S} (he : F.IsLink e x y) :
    Γ.drawing.toGraph.IsLink (drawingEdgeMap Γ e) x y := by
  have h := (Γ.iso.isLink_iff ⟨e, he.edge_mem⟩ ⟨x, he.left_mem⟩ ⟨y, he.right_mem⟩).mp he
  simpa only [drawingEdgeMap, he.edge_mem, ↓reduceDIte, hID] using h

private theorem inverse_drawing_link {S : Type u} {β : Type v} [TopologicalSpace S]
    {F : Graph S β} (Γ : GraphDrawing F S) (hV : Γ.drawing.V = V(F))
    (hID : ∀ v : V(F), (Γ.iso.vertexEquiv v).val = v.val)
    {e : Set S} {x y : S} (he : Γ.drawing.toGraph.IsLink e x y) :
    F.IsLink (Γ.iso.edgeEquiv.symm ⟨e, he.edge_mem⟩).val x y := by
  apply (Γ.iso.isLink_iff (Γ.iso.edgeEquiv.symm ⟨e, he.edge_mem⟩)
    ⟨x, hV ▸ he.left_mem⟩ ⟨y, hV ▸ he.right_mem⟩).mpr
  simpa only [Γ.iso.edgeEquiv.apply_symm_apply, hID] using he

private theorem inverse_drawing_walk {S : Type u} {β : Type v} [TopologicalSpace S]
    {F : Graph S β} (Γ : GraphDrawing F S) (hV : Γ.drawing.V = V(F))
    (hID : ∀ v : V(F), (Γ.iso.vertexEquiv v).val = v.val)
    {x y : S} (W : GraphWalk Γ.drawing.toGraph x y) :
    ∃ W' : GraphWalk F x y, W'.support = W.support ∧
      W'.edges.map (drawingEdgeMap Γ) = W.edges := by
  induction W with
  | nil hx => exact ⟨.nil (hV ▸ hx), rfl, rfl⟩
  | @cons x z y e he rest ih =>
    obtain ⟨W', hs, ht⟩ := ih
    have he' := inverse_drawing_link Γ hV hID he
    refine ⟨.cons he' W', congrArg (List.cons x) hs, ?_⟩
    change drawingEdgeMap Γ (Γ.iso.edgeEquiv.symm ⟨e, he.edge_mem⟩).val ::
      W'.edges.map (drawingEdgeMap Γ) = e :: rest.edges
    rw [ht]
    congr 1
    simp only [drawingEdgeMap, (Γ.iso.edgeEquiv.symm ⟨e, he.edge_mem⟩).property,
      ↓reduceDIte, Γ.iso.edgeEquiv.apply_symm_apply]

/-- A drawing that represents each vertex by itself preserves all walk
connections. This is used to keep the components in IV (9.2). -/
theorem GraphDrawing.walk_iff_of_vertex_id {S : Type u} {β : Type v} [TopologicalSpace S]
    {F : Graph S β} (Γ : GraphDrawing F S) (hV : Γ.drawing.V = V(F))
    (hID : ∀ v : V(F), (Γ.iso.vertexEquiv v).val = v.val) (x y : S) :
    Nonempty (GraphWalk F x y) ↔ Nonempty (GraphWalk Γ.drawing.toGraph x y) := by
  constructor
  · rintro ⟨W⟩
    induction W with
    | nil hx =>
      refine ⟨.nil ?_⟩
      change _ ∈ Γ.drawing.V
      rw [hV]
      exact hx
    | cons he rest ih =>
      obtain ⟨W'⟩ := ih
      exact ⟨.cons (drawing_link Γ hID he) W'⟩
  · rintro ⟨W⟩
    obtain ⟨W', _, _⟩ := inverse_drawing_walk Γ hV hID W
    exact ⟨W'⟩

/-- A drawing with fixed vertices of a forest has no nontrivial simple
closed walks. This is the forest assertion in IV (9.2), page 254. -/
theorem GraphDrawing.isGraphForest_of_vertex_id {S : Type u} {β : Type v}
    [TopologicalSpace S] {F : Graph S β} (Γ : GraphDrawing F S)
    (hV : Γ.drawing.V = V(F))
    (hID : ∀ v : V(F), (Γ.iso.vertexEquiv v).val = v.val)
    (hF : IsGraphForest F) : IsGraphForest Γ.drawing.toGraph := by
  intro x W hW
  obtain ⟨W', hs, he⟩ := inverse_drawing_walk Γ hV hID W
  have hW' : W'.IsSimpleClosed := by
    refine ⟨hs ▸ hW.1, ?_⟩
    apply List.Nodup.of_map (f := drawingEdgeMap Γ)
    rw [he]
    exact hW.2
  have hlen := hF x W' hW'
  change W.edges.length = 0
  have hlength := congrArg List.length he
  rw [List.length_map] at hlength
  exact hlength.symm.trans hlen

end GraphMinor.GM04
