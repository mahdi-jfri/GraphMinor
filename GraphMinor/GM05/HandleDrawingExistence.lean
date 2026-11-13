module

public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.Statement
import GraphMinor.GM12.Section4DrawnGraph
import GraphMinor.GM20.Draw8
import GraphMinor.Surface.ModelCriterion
public import GraphMinor.Minor.Model
public import GraphMinor.GM17.Defs

/-!
# A finite graph has a drawing in a handle model

The proved finite-graph drawing theorem supplies edge arcs in a model
with sufficiently many handles. Its hypergraph representation has
exactly the incidences of the multigraph. The proved GM XII edge-arc bridge turns
those arcs into a `Surface.GraphDrawing`, retaining loops and isolated
vertices. This is the initial drawing used in GM V, (8.14).
-/

public section
namespace GraphMinor.GM05
open Set Graph Surface GM17
universe u v

/-- The library's drawing representation for a graph hypergraph gives
an abstract graph drawing of the original multigraph. -/
theorem graphDrawing_of_canBeDrawn {α : Type u} {β : Type v}
    (H : Graph α β) (hV : V(H).Finite) (hE : E(H).Finite)
    {S : Type} [TopologicalSpace S] [T2Space S]
    (hdraw : CanBeDrawn S (Hypergraph.ofGraph H hV hE)) : Nonempty (GraphDrawing H S) := by
  let K := Hypergraph.ofGraph H hV hE
  obtain ⟨ν,F,hν,hline,hloop,hmeet,hvertex⟩ := hdraw
  obtain ⟨Γ,-,-⟩ := GM12.exists_graphDrawing_of_edge_curves H hV hE ν F hν
    (fun e he a b hab hne ↦ hline e he a b hab.inc_left hab.inc_right hne)
    (fun e he a haa ↦ hloop e he a (by
      ext b
      constructor
      · rintro ⟨c,hbc⟩
        exact (hbc.left_eq_or_eq haa).elim id id
      · intro hb
        have hba : b=a := hb
        subst b
        exact ⟨a,haa⟩)) hmeet hvertex
  exact ⟨Γ⟩

/-- Every finite multigraph has a drawing in a closed handle model,
by the already proved GM XX finite-graph drawing construction. -/
theorem exists_handle_model_drawing {α : Type u} {β : Type v}
    (H : Graph α β) (hV : V(H).Finite) (hE : E(H).Finite) :
    ∃ a : ℕ, Nonempty (GraphDrawing H (SurfaceModel a 0 0)) := by
  let K := Hypergraph.ofGraph H hV hE
  have hK : K.IsGraph := by
    intro e he
    obtain ⟨x,y,hxy⟩ := H.exists_isLink_of_mem_edgeSet he
    have hsub : K.ends e ⊆ {x,y} := by
      rintro z ⟨w,hzw⟩
      exact hzw.left_eq_or_eq hxy
    refine ⟨⟨x,y,hxy⟩,?_⟩
    exact (ncard_le_ncard hsub (by simp)).trans (ncard_insert_le _ _ |>.trans (by simp))
  obtain ⟨a,ha⟩ := GM20.Draw.exists_canBeDrawn K hK
  let : T2Space (SurfaceModel a 0 0) := (isSurface_model a 0 0).1.2.1
  exact ⟨a,graphDrawing_of_canBeDrawn H hV hE (ha a 0 0 (.inl le_rfl))⟩

end GraphMinor.GM05
