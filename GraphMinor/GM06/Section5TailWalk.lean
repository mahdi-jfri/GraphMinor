module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM11.Walks
import GraphMinor.GM06.Section5Red

/-!
# The tail after a linkage contact

For VI (5.1), page 129, split the old linkage path at its contact
vertex. The suffix is simple and misses the old initial vertex.
Its drawing is a path unless the contact is terminal, in which case
it is the single terminal vertex. Thus both cases satisfy the same
tail predicate used in Reduction 4.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

universe u v

private theorem isSimple_walk_suffix
    {α : Type u} {β : Type v} {G : Graph α β} {s x t : α}
    (A : GraphWalk G s x) (B : GraphWalk G x t)
    (h : (A.append B).IsSimple) : B.IsSimple := by
  induction A with
  | nil _ => exact h
  | cons hl A ih => exact ih B h.of_cons

private theorem isSection5Tail_walkDrawing
    (P : Drawing ClosedCylinder) {x t : ClosedCylinder}
    (W : GraphWalk P.toGraph x t) (hW : W.IsSimple) :
    IsSection5Tail P (walkDrawing P W) x t := by
  by_cases hxt : x = t
  · subst t
    cases W with
    | nil hv =>
      refine Or.inl ⟨rfl, ?_, ?_⟩
      · ext y
        simp [mem_walkDrawing_U, GraphWalk.support, GraphWalk.edges]
      · ext y
        simp [walkDrawing_V, GraphWalk.support]
    | cons hl R =>
      exact False.elim ((List.nodup_cons.mp hW).1 R.end_mem_support)
  · have hsub := walkDrawing_isSubdrawing P W
    exact Or.inr ⟨hsub, hsub.U_subset, isPathDrawing_walkDrawing_of_isSimple P hW hxt⟩

/-- The suffix used after a noninitial contact in VI (5.1), page 129,
misses the original initial vertex. It may be the single terminal
vertex, as permitted by the corrected Reduction 4 definition. -/
theorem exists_tail_walk_avoiding_start
    {P : Drawing ClosedCylinder} {s t x : ClosedCylinder}
    (hP : IsPathDrawing P s t) (hx : x ∈ P.V) (hxs : x ≠ s) :
    ∃ B : GraphWalk P.toGraph x t, B.IsSimple ∧
      IsSection5Tail P (walkDrawing P B) x t ∧ s ∉ (walkDrawing P B).U := by
  obtain ⟨W, hW, hV, _⟩ := hP.1
  have hxW : x ∈ W.support := by rw [hV] at hx; exact hx
  obtain ⟨A, B, hAB⟩ := W.exists_append_of_mem hxW
  have hsimple : (A.append B).IsSimple := hAB ▸ hW
  have hB := isSimple_walk_suffix A B hsimple
  have hsNotB : s ∉ B.support := by
    cases A with
    | nil _ => exact False.elim (hxs rfl)
    | cons hl R =>
      intro hsB
      exact (List.nodup_cons.mp hsimple).1
        ((GraphWalk.mem_support_append R B).mpr (Or.inr hsB))
  refine ⟨B, hB, isSection5Tail_walkDrawing P B hB, ?_⟩
  intro hsU
  have hsP : s ∈ P.V := by rw [hV]; exact W.start_mem_support
  have hsub := walkDrawing_isSubdrawing P B
  have hsT : s ∈ (walkDrawing P B).V := by
    by_contra hsV
    obtain ⟨e, he, hse⟩ := (walkDrawing P B).exists_edge_of_mem hsU hsV
    exact ((hsub.2 he).2.1 hse).2 hsP
  have hsB : s ∈ B.support := by simpa only [walkDrawing_V, mem_ofPred_eq] using hsT
  exact hsNotB hsB

end GraphMinor.GM06
