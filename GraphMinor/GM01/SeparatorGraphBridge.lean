module

public import GraphMinor.GM01.SimplePathSeparators
public import GraphMinor.GM01.SeparatorSimplification
public import GraphMinor.GM01.SimplificationMinor
import GraphMinor.GM01.SimplificationConnected
import GraphMinor.GM01.Basic

/-!
# The multigraph bridge for the separator argument

Graph Minors I, (4.2), pages 55–56, uses the simple-graph results of
Section 2 on general graphs. Original separators become separators in
the complete-graph subgraph representation of the underlying simple
graph. A simple separator maps back by subtype inclusion with unchanged
cardinality. Grid exclusion transfers by the proved simplification minor.
Connected induced sets transfer by an explicit bijection of vertex types.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The two representations have the same vertex separators under the
subtype inclusion on the original graph's vertices. -/
theorem graphSeparates_iff_simple_subgraph {α β : Type*} (G : Graph α β) (X A B : Set α) :
    GraphSeparates G X A B ↔
      Separates (SimpleGraph.toSubgraph G.toSimpleGraph le_top)
        (Subtype.val ⁻¹' X) (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' B) :=
  (graphSeparates_iff_simple_paths G X A B).trans
    (separates_toSubgraph_iff_paths G.toSimpleGraph _ _ _).symm

/-- A separator of the underlying simple graph maps to a separator of
the original graph with the same number of vertices. -/
theorem graph_separator_of_simple_separator {α β : Type*} (G : Graph α β)
    (A B : Set α) (S : Set V(G))
    (hS : Separates (SimpleGraph.toSubgraph G.toSimpleGraph le_top) S
      (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' B)) :
    ∃ X ⊆ V(G), X.ncard = S.ncard ∧ GraphSeparates G X A B := by
  let X : Set α := Subtype.val '' S
  refine ⟨X, ?_, Set.ncard_image_of_injective S Subtype.val_injective, ?_⟩
  · rintro x ⟨v, _, rfl⟩
    exact v.property
  · apply (graphSeparates_iff_simple_subgraph G X A B).mpr
    simpa only [X, Set.preimage_image_eq S Subtype.val_injective] using hS

/-- Grid exclusion passes to the simple-graph subgraph representation by
transitivity with the explicit simplification minor. -/
theorem simplification_mem_gridFree {α β : Type*} {θ : ℕ} (G : Graph α β)
    (hG : ¬ IsIsoMinor (gridGraph θ) G) :
    SimpleGraph.toSubgraph G.toSimpleGraph le_top ∈ 𝓕 θ := by
  intro hgrid
  have hminor : IsIsoMinor (gridGraph θ) (Graph.ofSimpleGraph G.toSimpleGraph) := by
    rwa [ofSimpleGraph_eq_toGraph]
  exact hG (hminor.trans (simplification_isIsoMinor G))

/-- The original induced vertex set, viewed in the Section 2 simple-graph
representation. Its vertices are the preimage under subtype inclusion. -/
def simpleInducedVertices {α β : Type*} (G : Graph α β) (D : Set α) :
    (⊤ : SimpleGraph V(G)).Subgraph :=
  (SimpleGraph.toSubgraph G.toSimpleGraph le_top).induce (Subtype.val ⁻¹' D)

/-- The induced simple subgraph stays in the whole simple representation. -/
theorem simpleInducedVertices_le {α β : Type*} (G : Graph α β) (D : Set α) :
    simpleInducedVertices G D ≤ SimpleGraph.toSubgraph G.toSimpleGraph le_top := by
  refine ⟨fun _ _ ↦ mem_univ _, ?_⟩
  intro u v huv
  exact huv.2.2

/-- Connectivity of an original induced graph transfers to the simple
induced subgraph by the explicit subtype bijection. -/
theorem simpleInducedVertices_connected {α β : Type*} (G : Graph α β) (D : Set α)
    (hD : D ⊆ V(G)) (hconn : GraphConnected (G.induce D)) :
    (simpleInducedVertices G D).Connected := by
  let f : V(G.induce D) → (simpleInducedVertices G D).verts :=
    fun v ↦ ⟨⟨v.val, hD v.property⟩, v.property⟩
  let hom : (G.induce D).toSimpleGraph →g (simpleInducedVertices G D).coe :=
    { toFun := f
      map_rel' := by
        intro u v huv
        obtain ⟨e, he⟩ := huv.2
        refine ⟨u.property, v.property, ?_, e, he.1⟩
        intro heq
        exact huv.1 (Subtype.ext (congrArg (fun z : V(G) ↦ z.val) heq)) }
  have hsurj : Function.Surjective hom := by
    intro v
    exact ⟨⟨v.val.val, v.property⟩, Subtype.ext (Subtype.ext rfl)⟩
  exact ⟨(toSimpleGraph_connected hconn).map hom hsurj⟩

end GraphMinor.GM01
