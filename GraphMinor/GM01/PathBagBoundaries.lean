module

public import GraphMinor.GM01.PathWidth

/-!
# The overlap boundary of one path-decomposition bag

To refine a bag in Graph Minors I, (1.6), page 40, keep throughout
its refinement the vertices it shares with other bags. The interval
condition puts each such vertex in the preceding overlap or the next
overlap. Their sizes are at most `k` each, so this boundary has at
most `2k` vertices.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- The vertices in bags other than the chosen bag, in the deleted
set of GM01 (1.6), page 40. -/
@[expose] def PathDecomposition.otherBags {α β : Type*} {G : Graph α β}
    (D : PathDecomposition G) (i : Fin D.length) : Set α :=
  ⋃ j : Fin D.length, ⋃ (_ : j ≠ i), D.bag j

/-- The part of a bag shared with other bags. In the refinement for
GM01 (1.6), page 40, these vertices are kept in every refined bag. -/
@[expose] def PathDecomposition.boundary {α β : Type*} {G : Graph α β}
    (D : PathDecomposition G) (i : Fin D.length) : Set α :=
  D.bag i ∩ D.otherBags i

/-- A vertex occurring in two different outer bags belongs to the
boundary of each, as used in GM01 (1.6), page 40. -/
theorem PathDecomposition.mem_boundary_of_mem_two_bags {α β : Type*} {G : Graph α β}
    (D : PathDecomposition G) {i j : Fin D.length} (hji : j ≠ i) {x : α}
    (hxi : x ∈ D.bag i) (hxj : x ∈ D.bag j) : x ∈ D.boundary i :=
  ⟨hxi, Set.mem_iUnion₂.mpr ⟨j, hji, hxj⟩⟩

/-- The two neighboring overlaps bound the boundary size in the
refinement proof of GM01 (1.6), page 40. -/
theorem PathDecomposition.boundary_ncard_le {α β : Type*} {G : Graph α β}
    (D : PathDecomposition G) (hfin : V(G).Finite) {k : ℕ}
    (hOverlap : ∀ i j : Fin D.length, j.val = i.val + 1 → (D.bag i ∩ D.bag j).ncard ≤ k)
    (i : Fin D.length) : (D.boundary i).Finite ∧ (D.boundary i).ncard ≤ 2 * k := by
  classical
  let A : Set α := if hi : 0 < i.val then D.bag ⟨i.val - 1, by omega⟩ ∩ D.bag i else ∅
  let B : Set α := if hi : i.val + 1 < D.length then D.bag i ∩ D.bag ⟨i.val + 1, hi⟩ else ∅
  have hA : A.Finite := by
    dsimp only [A]
    split_ifs with hi
    · exact hfin.subset (fun _ hx ↦ D.bag_subset i hx.2)
    · exact Set.finite_empty
  have hB : B.Finite := by
    dsimp only [B]
    split_ifs with hi
    · exact hfin.subset (fun _ hx ↦ D.bag_subset i hx.1)
    · exact Set.finite_empty
  have hAk : A.ncard ≤ k := by
    dsimp only [A]
    split_ifs with hi
    · exact hOverlap ⟨i.val - 1, by omega⟩ i (by change i.val = i.val - 1 + 1; omega)
    · simp only [Set.ncard_empty, Nat.zero_le]
  have hBk : B.ncard ≤ k := by
    dsimp only [B]
    split_ifs with hi
    · exact hOverlap i ⟨i.val + 1, hi⟩ rfl
    · simp only [Set.ncard_empty, Nat.zero_le]
  have hSub : D.boundary i ⊆ A ∪ B := by
    intro x hx
    obtain ⟨j, hji, hxj⟩ := Set.mem_iUnion₂.mp hx.2
    have hne : j.val ≠ i.val := fun h ↦ hji (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hj | hj
    · have hi : 0 < i.val := by omega
      have hxprev := D.interval j ⟨i.val - 1, by omega⟩ i
        (by change j.val ≤ i.val - 1; omega) (by change i.val - 1 ≤ i.val; omega) ⟨hxj, hx.1⟩
      apply Or.inl
      dsimp only [A]
      rw [dite_eq_left hi]
      exact ⟨hxprev, hx.1⟩
    · have hi : i.val + 1 < D.length := by have := j.isLt; omega
      have hxnext := D.interval i ⟨i.val + 1, hi⟩ j
        (by change i.val ≤ i.val + 1; omega) (by change i.val + 1 ≤ j.val; omega) ⟨hx.1, hxj⟩
      apply Or.inr
      dsimp only [B]
      rw [dite_eq_left hi]
      exact ⟨hx.1, hxnext⟩
  refine ⟨(hA.union hB).subset hSub, ?_⟩
  have hn := (Set.ncard_le_ncard hSub (hA.union hB)).trans (Set.ncard_union_le A B)
  omega

end GraphMinor.GM01
