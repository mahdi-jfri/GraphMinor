module

public import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Set.Card

/-!
# Graphs of consecutive list vertices

The path-list count in II (2.8) needs uniqueness of a matching with a fixed
support inside disjoint paths. A graph whose edges lie along one list of
distinct vertices cannot contain a nonempty graph of cycles: its first
vertex has at most one neighbor, and deleting that vertex repeats the
argument on the rest of the list.
-/

@[expose] public section
namespace GraphMinor.GM02
open SimpleGraph Set Classical
universe u

/-- The graph whose edges join consecutive entries of a list. -/
def listEdgeGraph {α : Type u} (l : List α) : SimpleGraph α :=
  SimpleGraph.fromEdgeSet {e | e ∈ List.zipWith (s(·, ·)) l l.tail}

/-- Edges between consecutive list vertices have both endpoints in the list. -/
theorem mem_list_of_mem_list_edges {α : Type u} {l : List α} {e : Sym2 α}
    (he : e ∈ List.zipWith (s(·, ·)) l l.tail) {a : α} (ha : a ∈ e) : a ∈ l := by
  induction l with
  | nil => simp at he
  | cons x xs ih =>
    cases xs with
    | nil => simp at he
    | cons y ys =>
      simp only [List.tail_cons, List.zipWith_cons_cons, List.mem_cons] at he
      rcases he with he | he
      · subst e
        rcases Sym2.mem_iff.1 ha with rfl | rfl
        · simp
        · simp
      · exact List.mem_cons_of_mem x (ih he)

/-- An edge of the list graph has its endpoints in the list. -/
theorem listEdgeGraph_adj_mem {α : Type u} {l : List α} {a b : α}
    (hab : (listEdgeGraph l).Adj a b) : a ∈ l ∧ b ∈ l := by
  have he := ((SimpleGraph.fromEdgeSet_adj _).1 hab).1
  exact ⟨mem_list_of_mem_list_edges he (Sym2.mem_mk_left _ _),
    mem_list_of_mem_list_edges he (Sym2.mem_mk_right _ _)⟩

/-- Removing the first vertex leaves one edge and the remaining list graph. -/
theorem listEdgeGraph_cons_cons {α : Type u} (a b : α) (l : List α) :
    listEdgeGraph (a :: b :: l) = edge a b ⊔ listEdgeGraph (b :: l) := by
  ext x y
  simp only [listEdgeGraph, SimpleGraph.fromEdgeSet_adj, SimpleGraph.sup_adj,
    List.tail_cons, List.zipWith_cons_cons, List.mem_cons, Set.mem_ofPred_eq,
    SimpleGraph.edge_adj]
  rw [Sym2.eq_iff]
  tauto

/-- A graph of cycles lying along a list with distinct vertices has no
edges. This is the leaf-removal argument used for matching uniqueness. -/
theorem isCycles_eq_bot_of_le_listEdgeGraph {α : Type u} {D : SimpleGraph α}
    {l : List α} (hl : l.Nodup) (hc : D.IsCycles) (hle : D ≤ listEdgeGraph l) : D = ⊥ := by
  induction l generalizing D with
  | nil =>
    apply le_bot_iff.1
    simpa [listEdgeGraph] using hle
  | cons a xs ih =>
    cases xs with
    | nil =>
      apply le_bot_iff.1
      simpa [listEdgeGraph] using hle
    | cons b ys =>
      have hnd := List.nodup_cons.1 hl
      have hn : a ∉ b :: ys := hnd.1
      have hsplit := listEdgeGraph_cons_cons a b ys
      have hneigh : D.neighborSet a ⊆ {b} := by
        intro x hx
        have h := hle hx
        rw [hsplit] at h
        rcases h with he | ht
        · rcases ((SimpleGraph.edge_adj _ _ _ _).1 he).1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact hb
          · exact (hn (List.mem_cons.2 (Or.inl ha))).elim
        · exact (hn (listEdgeGraph_adj_mem ht).1).elim
      have hiso : ∀ x, ¬D.Adj a x := by
        intro x hax
        have hcount := hc ⟨x, hax⟩
        have hbound := Set.ncard_le_ncard hneigh (Set.finite_singleton b)
        rw [Set.ncard_singleton] at hbound
        omega
      have htail : D ≤ listEdgeGraph (b :: ys) := by
        intro x y hxy
        have h := hle hxy
        rw [hsplit] at h
        rcases h with he | ht
        · rcases ((SimpleGraph.edge_adj _ _ _ _).1 he).1 with ⟨hx, hy⟩ | ⟨hx, hy⟩
          · subst x
            exact (hiso y hxy).elim
          · subst y
            exact (hiso x hxy.symm).elim
        · exact ht
      exact ih hnd.2 hc htail

end GraphMinor.GM02
