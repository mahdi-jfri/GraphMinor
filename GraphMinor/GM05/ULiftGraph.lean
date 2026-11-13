module

public import GraphMinor.Statement
public import Mathlib.Data.Set.Card

/-!
# Raising the universes of a finite host graph

The Erdős–Pósa property in GM V, Section 8, ranges over arbitrary
vertex and edge label types. Relabel a finite geometric host by
`ULift` on both types. The vertex and edge maps add the wrapper and
the incidence relation is unchanged.
-/

@[expose] public section
namespace GraphMinor.GM05
open Set Graph
universe u v r s

/-- Relabel the two ambient types of a graph by `ULift`. -/
def uliftGraph {α : Type u} {β : Type v} (G : Graph α β) :
    Graph (ULift.{r} α) (ULift.{s} β) where
  vertexSet := {x | x.down ∈ V(G)}
  edgeSet := {e | e.down ∈ E(G)}
  IsLink e x y := G.IsLink e.down x.down y.down
  isLink_symm _ _ := ⟨fun _ _ h ↦ h.symm⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := by
    rcases h.left_eq_or_eq h' with hh | hh
    · exact Or.inl (ULift.down_injective hh)
    · exact Or.inr (ULift.down_injective hh)
  edge_mem_iff_exists_isLink e := by
    constructor
    · intro he
      obtain ⟨x,y,hxy⟩ := G.exists_isLink_of_mem_edgeSet he
      exact ⟨ULift.up x,ULift.up y,hxy⟩
    · rintro ⟨x,y,hxy⟩
      exact hxy.edge_mem
  left_mem_of_isLink _ _ _ h := h.left_mem

/-- The relabelling isomorphism adds `ULift` on each support set. -/
def uliftGraphIso {α : Type u} {β : Type v} (G : Graph α β) : Iso G (uliftGraph.{u,v,r,s} G) where
  vertexEquiv := {
    toFun x := ⟨ULift.up x.val,x.prop⟩
    invFun x := ⟨x.val.down,x.prop⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  edgeEquiv := {
    toFun e := ⟨ULift.up e.val,e.prop⟩
    invFun e := ⟨e.val.down,e.prop⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  isLink_iff _ _ _ := Iff.rfl

/-- Relabelling preserves subgraphs. -/
theorem uliftGraph_mono {α : Type u} {β : Type v} {A G : Graph α β} (h : A ≤ G) :
    uliftGraph.{u,v,r,s} A ≤ uliftGraph.{u,v,r,s} G :=
  ⟨fun _ hx ↦ h.vertexSet_mono hx,fun {_ _ _} hl ↦ h.isLink_mono hl⟩

/-- The raised vertex set is the image under the wrapper map. -/
theorem uliftGraph_vertexSet {α : Type u} {β : Type v} (G : Graph α β) :
    V(uliftGraph.{u,v,r,s} G) = ULift.up '' V(G) := by
  ext x
  constructor
  · intro hx
    exact ⟨x.down,hx,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact hy

/-- The raised edge set is the image under the wrapper map. -/
theorem uliftGraph_edgeSet {α : Type u} {β : Type v} (G : Graph α β) :
    E(uliftGraph.{u,v,r,s} G) = ULift.up '' E(G) := by
  ext e
  constructor
  · intro he
    exact ⟨e.down,he,rfl⟩
  · rintro ⟨f,hf,rfl⟩
    exact hf

/-- Relabelling preserves finite support sets. -/
theorem uliftGraph_finite {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    V(uliftGraph.{u,v,r,s} G).Finite ∧ E(uliftGraph.{u,v,r,s} G).Finite := by
  rw [uliftGraph_vertexSet,uliftGraph_edgeSet]
  exact ⟨hV.image _,hE.image _⟩

end GraphMinor.GM05
