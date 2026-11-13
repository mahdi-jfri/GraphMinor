module

public import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.Basic

/-!
# Recovering a path from its internal vertices

The list encoding for II (2.8) deletes just the two endpoints from a path's
vertex list. Because a path has no repeated vertices, the endpoint and
internal-vertex lists recover its whole vertex order.
-/

public section
namespace GraphMinor.GM02
open SimpleGraph
universe u

/-- Filtering precisely the internal vertices of a nontrivial path leaves
a list which recovers its support when the endpoints are restored. -/
theorem support_eq_cons_filter_append {α : Type u} {F : SimpleGraph α}
    {s t : α} (p : F.Walk s t) (hp : p.IsPath) (hst : s ≠ t) (f : α → Bool)
    (hf : ∀ a ∈ p.support, f a = true ↔ a ≠ s ∧ a ≠ t) :
    p.support = s :: (p.support.filter f ++ [t]) := by
  have hfs : f s = false := by
    apply Bool.eq_false_iff.2
    intro h
    exact ((hf s p.start_mem_support).1 h).1 rfl
  have hft : f t = false := by
    apply Bool.eq_false_iff.2
    intro h
    exact ((hf t p.end_mem_support).1 h).2 rfl
  cases p with
  | nil => exact (hst rfl).elim
  | cons hab q =>
    let m := q.support.dropLast
    have htail : m ++ [t] = q.support := by
      have h := List.dropLast_append_getLast q.support_ne_nil
      rw [q.getLast_support] at h
      exact h
    have hsplit : (Walk.cons hab q).support = s :: (m ++ [t]) := by
      change s :: q.support = _
      rw [htail]
    have hnd : (s :: (m ++ [t])).Nodup := hsplit ▸ hp.support_nodup
    have hstart := (List.nodup_cons.1 hnd).1
    have hend := (List.nodup_append.1 hnd.of_cons).2.2
    have hfilter : m.filter f = m := by
      apply List.filter_eq_self.2
      intro x hx
      have hxP : x ∈ (Walk.cons hab q).support := by
        rw [hsplit]
        exact List.mem_cons_of_mem s (List.mem_append_left [t] hx)
      apply (hf x hxP).2
      constructor
      · intro heq
        exact hstart (List.mem_append_left [t] (heq ▸ hx))
      · exact hend x hx t (by simp)
    rw [hsplit]
    simp only [List.filter_cons, hfs, Bool.false_eq_true, ↓reduceIte,
      List.filter_append, hft]
    rw [hfilter]
    simp

end GraphMinor.GM02
