module

public import GraphMinor.Statement
public import Mathlib.Data.Set.Card

/-!
# Parallel copies with common vertices

For the drawings chosen in GM V, (8.14), first copy every edge while
retaining the original vertices. An edge label records its copy and
its original edge. The later vertex-star replacement separates the
vertices belonging to different copies.
-/

@[expose] public section
namespace GraphMinor.GM05
open Set Graph

/-- The parallel edge copies used in the geometric construction for
GM V, proof of (8.14), page 113, before separating the vertex stars. -/
def parallelGraph {α β : Type*} (m : ℕ) (G : Graph α β) : Graph α (Fin m × β) where
  vertexSet := V(G)
  edgeSet := univ ×ˢ E(G)
  IsLink e x y := G.IsLink e.2 x y
  isLink_symm e _ := ⟨fun _ _ h ↦ h.symm⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.left_eq_or_eq h'
  edge_mem_iff_exists_isLink e := by
    constructor
    · intro he
      exact G.exists_isLink_of_mem_edgeSet he.2
    · rintro ⟨x,y,hxy⟩
      exact ⟨mem_univ _,hxy.edge_mem⟩
  left_mem_of_isLink _ _ _ h := h.left_mem

/-- Parallel copying preserves finiteness of the two support sets. -/
theorem parallelGraph_finite {α β : Type*} (m : ℕ) (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    V(parallelGraph m G).Finite ∧ E(parallelGraph m G).Finite :=
  ⟨hV,finite_univ.prod hE⟩

end GraphMinor.GM05
