module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Red
import GraphMinor.GM11.Walks

/-!
# Extracting a path from a boundary walk

The proof of VI (5.1), page 129, follows a region boundary to obtain
a path. Between any two distinct vertices visited by a walk, reverse
the prefix to the first and follow the prefix to the second. Removing
repeated vertices gives a simple path and adds no vertex or edge.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

universe u

/-- Two distinct vertices visited by a walk are joined by a path
using only vertices and edges of that walk. -/
theorem exists_subpath_of_walk_support
    {S : Type u} [TopologicalSpace S] [T1Space S] (G : Drawing S)
    {s t a b : S} (W : GraphWalk G.toGraph s t)
    (ha : a ∈ W.support) (hb : b ∈ W.support) (hab : a ≠ b) :
    ∃ P : Drawing S, IsSubpathOf G P a b ∧
      P.V ⊆ {x | x ∈ W.support} ∧ P.E ⊆ {e | e ∈ W.edges} := by
  classical
  obtain ⟨Wa, Ra, hWa⟩ := W.exists_append_of_mem ha
  obtain ⟨Wb, Rb, hWb⟩ := W.exists_append_of_mem hb
  have hVa : ∀ x ∈ Wa.support, x ∈ W.support := by
    intro x hx
    rw [hWa, GraphWalk.mem_support_append]
    exact Or.inl hx
  have hVb : ∀ x ∈ Wb.support, x ∈ W.support := by
    intro x hx
    rw [hWb, GraphWalk.mem_support_append]
    exact Or.inl hx
  have hEa : ∀ e ∈ Wa.edges, e ∈ W.edges := by
    intro e he
    rw [hWa, GraphWalk.edges_append, List.mem_append]
    exact Or.inl he
  have hEb : ∀ e ∈ Wb.edges, e ∈ W.edges := by
    intro e he
    rw [hWb, GraphWalk.edges_append, List.mem_append]
    exact Or.inl he
  obtain ⟨R, hR, hRV, hRE⟩ := GM11.GraphWalk.exists_isSimple (Wa.reverse.append Wb)
  have hsub := walkDrawing_isSubdrawing G R
  refine ⟨walkDrawing G R, ⟨hsub, hsub.U_subset,
    isPathDrawing_walkDrawing_of_isSimple G hR hab⟩, ?_, ?_⟩
  · rw [walkDrawing_V]
    intro x hx
    have hxR := hRV x hx
    rw [GraphWalk.mem_support_append, GraphWalk.support_reverse, List.mem_reverse] at hxR
    exact hxR.elim (hVa x) (hVb x)
  · rw [walkDrawing_E]
    intro e he
    have heR := hRE e he
    rw [GraphWalk.edges_append, List.mem_append, GraphWalk.edges_reverse, List.mem_reverse] at heR
    exact heR.elim (hEa e) (hEb e)

end GraphMinor.GM06
