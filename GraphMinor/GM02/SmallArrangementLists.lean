module

public import GraphMinor.GM02.PathListArrangement
public import Mathlib.Data.Set.Card

/-!
# Lists on one or two separator vertices

For the small cases of II (2.8), disjoint lists use at most the vertices
of the separator. On two vertices an even list is empty or lists both
vertices in one of their two orders. An odd list has exactly one vertex.
These elementary bounds supply the finite enumeration after parity has
been fixed by the original terminal sides.
-/

public section
namespace GraphMinor.GM02
open Set Classical
universe u t

/-- A list with no repetitions uses no more vertices than its finite set. -/
theorem length_le_ncard_of_mem {α : Type u} {S : Set α} (hS : S.Finite)
    (l : List α) (hl : l.Nodup) (hmem : ∀ a ∈ l, a ∈ S) : l.length ≤ S.ncard := by
  have hsub : (l.toFinset : Set α) ⊆ S := fun a ha => hmem a (List.mem_toFinset.1 ha)
  have h := Set.ncard_le_ncard hsub hS
  rwa [Set.ncard_coe_finset, List.toFinset_card_of_nodup hl] at h

/-- The lengths of two different path lists add to at most the separator size. -/
theorem PathListArrangement.length_add_le {α : Type u} {S : Set α} {I : Type t}
    (A : PathListArrangement S I) (hS : S.Finite) {i j : I} (hij : i ≠ j) :
    (A.paths i).length + (A.paths j).length ≤ S.ncard := by
  have hnodup : (A.paths i ++ A.paths j).Nodup := List.nodup_append.2
    ⟨A.nodup i, A.nodup j, fun a hai b hbj hab =>
      A.disjoint i j hij a hai (hab.symm ▸ hbj)⟩
  have hbound := length_le_ncard_of_mem hS (A.paths i ++ A.paths j) hnodup
    (fun a ha => (List.mem_append.1 ha).elim (A.vertex_mem i a) (A.vertex_mem j a))
  simpa only [List.length_append] using hbound

/-- A path list individually obeys the separator size bound. -/
theorem PathListArrangement.length_le {α : Type u} {S : Set α} {I : Type t}
    (A : PathListArrangement S I) (hS : S.Finite) (i : I) :
    (A.paths i).length ≤ S.ncard :=
  length_le_ncard_of_mem hS _ (A.nodup i) (A.vertex_mem i)

/-- An even list on two distinct vertices is empty or contains both in
one of the two possible orders. -/
theorem even_list_on_pair {α : Type u} {a b : α} (hab : a ≠ b) (l : List α)
    (hl : l.Nodup) (hmem : ∀ v ∈ l, v ∈ ({a, b} : Set α))
    (heven : l.length % 2 = 0) : l = [] ∨ l = [a, b] ∨ l = [b, a] := by
  have hlen := length_le_ncard_of_mem ((Set.finite_singleton b).insert a) l hl hmem
  rw [Set.ncard_pair hab] at hlen
  cases l with
  | nil => exact Or.inl rfl
  | cons x xs =>
    cases xs with
    | nil => simp at heven
    | cons y ys =>
      have hys : ys.length = 0 := by simp only [List.length_cons] at hlen; omega
      have heq : ys = [] := List.length_eq_zero_iff.1 hys
      subst ys
      have hx := hmem x (by simp)
      have hy := hmem y (by simp)
      have hxy : x ≠ y := fun h => (List.nodup_cons.1 hl).1 (by simp [h])
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact (hxy rfl).elim

/-- An odd list of length at most two contains a single vertex. -/
theorem singleton_of_odd_of_length_le_two {α : Type u} (l : List α)
    (hlen : l.length ≤ 2) (hodd : l.length % 2 = 1) : ∃ a, l = [a] := by
  have hlen1 : l.length = 1 := by omega
  cases l with
  | nil => simp at hlen1
  | cons a xs =>
    have hxs : xs = [] := List.length_eq_zero_iff.1 (by simp only [List.length_cons] at hlen1; omega)
    exact ⟨a, by rw [hxs]⟩

end GraphMinor.GM02
