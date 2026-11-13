module

public import GraphMinor.GM09.Basic

/-!
# Removing the final edge of a simple path

The contractions in Graph Minors I, (4.9), page 58, must retain any
specified internal attachment vertex in the branch owning that path.
Remove the last edge using the first edge of the reversed simple walk.
The remaining path contains every vertex except the final one. This
makes the coverage property of the path contraction explicit.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09 GraphMinor.Surface

/-- Removing the final edge of a nontrivial path leaves a path covering
all its vertices except the final end. This is used to assign internal
attachment vertices to branches in the contraction for GM01 (4.9). -/
theorem exists_last_edge_with_vertex_cover {α β : Type*} {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) (hab : a ≠ b) :
    ∃ (e : β) (q : α) (Q : Graph α β), P.IsLink e q b ∧ Q ≤ P ∧
      IsGraphPathWithEnds G Q a q ∧ b ∉ V(Q) ∧ V(P) = insert b V(Q) := by
  obtain ⟨hPG, W, hW, hV, _⟩ := hP.symm
  cases W with
  | nil hb => exact False.elim (hab rfl)
  | @cons _ q _ e he rest =>
    have hrest : rest.IsSimple := (List.nodup_cons.mp hW).2
    have hbNot : b ∉ rest.support := (List.nodup_cons.mp hW).1
    let Q := walkSubgraph rest.reverse
    have hQ : IsGraphPathWithEnds P Q a q :=
      isGraphPathWithEnds_walkSubgraph (by
        change rest.reverse.support.Nodup
        rw [GraphWalk.support_reverse]
        exact List.nodup_reverse.mpr hrest)
    have hQV : V(Q) = {x | x ∈ rest.support} := by
      rw [vertexSet_walkSubgraph, GraphWalk.support_reverse]
      ext x
      exact List.mem_reverse
    refine ⟨e, q, Q, he.symm, hQ.le, hQ.mono hPG, ?_, ?_⟩
    · rw [hQV]
      exact hbNot
    · rw [hV, hQV]
      ext x
      simp only [Set.mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons, Set.mem_insert_iff]

end GraphMinor.GM01
