module

public import GraphMinor.Statement
public import Mathlib.Data.Set.Card

/-!
# Disjoint copies of a finite graph

Graph Minors V, proof of (8.8), page 111, forms the graph consisting of
`k` disjoint copies of `H`. A copy index is attached to each vertex and
each edge. All incidences stay within their copy, including loops and
parallel edges.
-/

@[expose] public section

namespace GraphMinor.GM05

open Graph Set

/-- The graph consisting of `k` disjoint copies of `H`, as in Graph
Minors V, proof of (8.8), page 111. -/
def graphCopies {α β : Type*} (k : ℕ) (H : Graph α β) : Graph (Fin k × α) (Fin k × β) where
  vertexSet := univ ×ˢ V(H)
  edgeSet := univ ×ˢ E(H)
  IsLink e x y := e.1=x.1 ∧ e.1=y.1 ∧ H.IsLink e.2 x.2 y.2
  isLink_symm _ _ := ⟨fun _ _ h ↦ ⟨h.2.1,h.1,h.2.2.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink _ x y z w h h' := by
    rcases h.2.2.left_eq_or_eq h'.2.2 with he|he
    · exact Or.inl (Prod.ext (h.1.symm.trans h'.1) he)
    · exact Or.inr (Prod.ext (h.1.symm.trans h'.2.1) he)
  edge_mem_iff_exists_isLink e := by
    constructor
    · intro he
      obtain ⟨x,y,hxy⟩ := exists_isLink_of_mem_edgeSet he.2
      exact ⟨(e.1,x),(e.1,y),rfl,rfl,hxy⟩
    · rintro ⟨x,y,hxy⟩
      exact ⟨mem_univ e.1,hxy.2.2.edge_mem⟩
  left_mem_of_isLink _ _ _ h := ⟨mem_univ _,h.2.2.left_mem⟩

@[simp] theorem graphCopies_inc {α β : Type*} {k : ℕ} (H : Graph α β)
    (e : Fin k × β) (v : Fin k × α) :
    (graphCopies k H).Inc e v ↔ e.1=v.1 ∧ H.Inc e.2 v.2 := by
  constructor
  · rintro ⟨w,hvw⟩
    exact ⟨hvw.1,⟨w.2,hvw.2.2⟩⟩
  · rintro ⟨h,⟨w,hw⟩⟩
    exact ⟨(e.1,w),h,rfl,hw⟩

@[simp] theorem graphCopies_isLoopAt {α β : Type*} {k : ℕ} (H : Graph α β)
    (e : Fin k × β) (v : Fin k × α) :
    (graphCopies k H).IsLoopAt e v ↔ e.1=v.1 ∧ H.IsLoopAt e.2 v.2 := by
  change (e.1=v.1 ∧ e.1=v.1 ∧ H.IsLink e.2 v.2 v.2) ↔ _
  exact ⟨fun h ↦ ⟨h.1,h.2.2⟩,fun h ↦ ⟨h.1,h⟩⟩

/-- Finite graphs still have finite vertex and edge sets after copying. -/
theorem graphCopies_finite {α β : Type*} (k : ℕ) (H : Graph α β)
    (hV : V(H).Finite) (hE : E(H).Finite) :
    V(graphCopies k H).Finite ∧ E(graphCopies k H).Finite :=
  ⟨finite_univ.prod hV,finite_univ.prod hE⟩

end GraphMinor.GM05
