module

public import GraphMinor.Mader.ApexForest
public import GraphMinor.Statement
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card

/-!
# Isomorphisms from prescribed edge ends

A vertex bijection and an edge bijection which preserve the two ends of
each edge give a multigraph isomorphism. We also give a uniform enumeration
of any finite set by its natural cardinality for numbering parallel edges.
-/

public section

namespace GraphMinor.Mader

open Graph

/-- Enumerate a finite set by indices below its cardinality. -/
noncomputable def finiteSetEnumeration {α : Type*} (S : Set α) (hS : S.Finite) :
    Fin S.ncard ≃ S := by
  let := hS.fintype
  exact (Fintype.equivFinOfCardEq (Set.fintypeCard_eq_ncard S)).symm

/-- Vertex and edge bijections preserving prescribed ends give a graph
isomorphism, with both directions of link preservation. -/
def graphOfEndsIso {V E α β : Type*} (left right : E → V) (G : Graph α β)
    (vertices : V ≃ V(G)) (edges : E ≃ E(G))
    (hends : ∀ e, G.IsLink (edges e).val (vertices (left e)).val (vertices (right e)).val) :
    Iso (graphOfEnds left right) G where
  vertexEquiv := (Equiv.Set.univ V).trans vertices
  edgeEquiv := (Equiv.Set.univ E).trans edges
  isLink_iff e x y := by
    change ((x.val = left e.val ∧ y.val = right e.val) ∨
      (x.val = right e.val ∧ y.val = left e.val)) ↔
      G.IsLink (edges e.val).val (vertices x.val).val (vertices y.val).val
    constructor
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      · rw [hx, hy]
        exact hends e.val
      · rw [hx, hy]
        exact (hends e.val).symm
    · intro h
      rcases h.eq_and_eq_or_eq_and_eq (hends e.val) with h | h
      · exact Or.inl ⟨vertices.injective (Subtype.ext h.1), vertices.injective (Subtype.ext h.2)⟩
      · exact Or.inr ⟨vertices.injective (Subtype.ext h.1), vertices.injective (Subtype.ext h.2)⟩

end GraphMinor.Mader
