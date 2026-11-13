module

public import GraphMinor.GM05.GraphCopies
public import GraphMinor.GM01.Defs
import GraphMinor.GM05.GridCopyEdges
import GraphMinor.Minor.Basic

/-!
# A grid minor containing disjoint grid copies

Use singleton branch sets at the row-block placement of each vertex.
The placement preserves incidence, and its distinct-end calculation
verifies the loop condition of the minor model. Extra host edges between
blocks are simply omitted. This gives the grid obstruction for disjoint
copies in Graph Minors V, (8.8).
-/

public section

namespace GraphMinor.GM05

open Graph Set GM01

/-- A square grid of side `(k+1)*θ` contains `k` disjoint `θ`-grids as
an isomorphic minor, including the empty cases. -/
theorem gridCopies_minor_grid (k θ : ℕ) :
    IsIsoMinor (graphCopies k (gridGraph θ)) (gridGraph ((k+1)*θ)) := by
  classical
  let ηv (p : Fin k × (Fin θ × Fin θ)) := ({gridCopyVertex p} : Set _)
  let ηe := @gridCopyEdge k θ
  have hm : IsMinorModel (graphCopies k (gridGraph θ)) (gridGraph ((k+1)*θ)) ηv ηe := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro p _
      exact singleton_nonempty _
    · intro p _ x _
      exact mem_univ x
    · intro e he
      obtain ⟨u,v,hl⟩ := exists_isLink_of_mem_edgeSet he.2
      exact (gridCopyVertex_link e.1 hl).edge_mem
    · intro p _ q _ hpq
      rw [Set.disjoint_singleton]
      exact fun h ↦ hpq (gridCopyVertex_injective h)
    · exact gridCopyEdge_injective.injOn
    · intro p _ e he
      change (graphCopies k (gridGraph θ)).Inc e p ↔
        ∃ x∈{gridCopyVertex p}, (gridGraph ((k+1)*θ)).Inc (gridCopyEdge e) x
      simpa only [mem_singleton_iff,exists_eq_left] using (gridCopyEdge_inc he p).symm
    · intro p _ e he
      exact gridCopyEdge_loop_iff he p
    · intro p _
      let K := Graph.noEdge {gridCopyVertex p} (Sym2 (Fin ((k+1)*θ) × Fin ((k+1)*θ)))
      refine ⟨K,?_,rfl,?_⟩
      · exact Graph.noEdge_le_iff.mpr (subset_univ _)
      · refine ⟨singleton_nonempty _,?_⟩
        intro x hx y hy
        change x=gridCopyVertex p at hx
        change y=gridCopyVertex p at hy
        have he : x=y := hx.trans hy.symm
        cases he
        exact Relation.ReflTransGen.refl
  exact isIsoMinor_of_isMinorModel _ _ (toFinite _) (toFinite _) (toFinite _) (toFinite _) ηv ηe hm

end GraphMinor.GM05
