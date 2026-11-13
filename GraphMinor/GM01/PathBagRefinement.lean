module

public import GraphMinor.GM01.PathWidth

/-!
# Refining one bag while keeping its boundary

For Graph Minors I, (1.6), page 40, use a path-decomposition of the
graph obtained by deleting all other outer bags. Restrict its bags
to the chosen outer bag and add the shared boundary to each of them.
Append a boundary bag to allow an empty inner decomposition. Covering
the remaining isolated vertices first ensures that edges from an
exclusive vertex to the boundary are covered as well.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- Refine a chosen vertex set using the width bound after deletion,
keeping its intersection with the deleted set in every new bag.
This is the local construction for GM01 (1.6), page 40. -/
theorem exists_path_bag_refinement {α β : Type*} {G : Graph α β}
    (hfin : V(G).Finite) (S X : Set α) (hS : S ⊆ V(G)) {k : ℕ}
    (h : HasPathWidthLE (G.deleteVerts X) k) :
    ∃ E : PathDecomposition (G.induce S), 0 < E.length ∧
      (∀ i, (E.bag i).Finite ∧ (E.bag i).ncard ≤ k + (S ∩ X).ncard + 1) ∧
      (∀ i, S ∩ X ⊆ E.bag i) ∧ ∀ x ∈ S, ∃ i, x ∈ E.bag i := by
  classical
  have hdel : V(G.deleteVerts X).Finite := by
    rw [G.vertexSet_deleteVerts X]
    exact hfin.sdiff
  obtain ⟨D, hD, hcover⟩ := h.exists_covering hdel
  let T := S ∩ X
  have hTfin : T.Finite := (hfin.subset hS).inter_of_left X
  let bag : Fin (D.length + 1) → Set α := fun i ↦
    if hi : i.val < D.length then (D.bag ⟨i.val, hi⟩ ∩ S) ∪ T else T
  have hbagT (i) : T ⊆ bag i := by
    dsimp only [bag]
    split <;> intro x hx
    · exact Or.inr hx
    · exact hx
  have old (i : Fin D.length) : bag ⟨i.val, by omega⟩ = (D.bag i ∩ S) ∪ T := by
    simp only [bag, i.isLt, ↓reduceDIte]
  have cover {x : α} (hx : x ∈ S) : ∃ i, x ∈ bag i := by
    by_cases hxT : x ∈ T
    · exact ⟨⟨D.length, by omega⟩, hbagT _ hxT⟩
    · have hxX : x ∉ X := fun hX ↦ hxT ⟨hx, hX⟩
      have hxDel : x ∈ V(G.deleteVerts X) := by
        rw [G.vertexSet_deleteVerts X]
        exact ⟨hS hx, hxX⟩
      obtain ⟨i, hi⟩ := hcover x hxDel
      refine ⟨⟨i.val, by omega⟩, ?_⟩
      rw [old i]
      exact Or.inl ⟨hi, hx⟩
  refine ⟨⟨D.length + 1, bag, ?_, ?_, ?_⟩, (by change 0 < D.length + 1; omega), ?_, hbagT, fun _ hx ↦ cover hx⟩
  · intro i x hx
    dsimp only [bag] at hx
    split at hx
    · exact hx.elim And.right And.left
    · exact hx.1
  · intro e x y he
    have hxS : x ∈ S := he.2.1
    have hyS : y ∈ S := he.2.2
    by_cases hxT : x ∈ T
    · obtain ⟨i, hi⟩ := cover hyS
      exact ⟨i, hbagT i hxT, hi⟩
    · by_cases hyT : y ∈ T
      · obtain ⟨i, hi⟩ := cover hxS
        exact ⟨i, hi, hbagT i hyT⟩
      · have hxX : x ∉ X := fun hX ↦ hxT ⟨hxS, hX⟩
        have hyX : y ∉ X := fun hX ↦ hyT ⟨hyS, hX⟩
        obtain ⟨i, hix, hiy⟩ := D.edge_covered e x y
          ((G.deleteVerts_isLink X).2 ⟨he.1, hxX, hyX⟩)
        refine ⟨⟨i.val, by omega⟩, ?_, ?_⟩
        · rw [old i]; exact Or.inl ⟨hix, hxS⟩
        · rw [old i]; exact Or.inl ⟨hiy, hyS⟩
  · intro i j l hij hjl x hx
    by_cases hxT : x ∈ T
    · exact hbagT _ hxT
    · have hi : i.val < D.length := by
        by_contra hi
        exact hxT (by simpa only [bag, hi, ↓reduceDIte] using hx.1)
      have hl : l.val < D.length := by
        by_contra hl
        exact hxT (by simpa only [bag, hl, ↓reduceDIte] using hx.2)
      have hj : j.val < D.length := lt_of_le_of_lt hjl hl
      have hxi : x ∈ D.bag ⟨i.val, hi⟩ ∩ S := by
        simpa only [bag, hi, ↓reduceDIte, Set.mem_union, hxT, or_false] using hx.1
      have hxl : x ∈ D.bag ⟨l.val, hl⟩ ∩ S := by
        simpa only [bag, hl, ↓reduceDIte, Set.mem_union, hxT, or_false] using hx.2
      have hxj := D.interval ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨l.val, hl⟩ hij hjl ⟨hxi.1, hxl.1⟩
      simp only [bag, hj, ↓reduceDIte]
      exact Or.inl ⟨hxj, hxi.2⟩
  · intro i
    dsimp only [bag]
    split
    · rename_i hi
      have hcapfin := (hD ⟨i.val, hi⟩).1.inter_of_left S
      have hcapcard := Set.ncard_le_ncard (inter_subset_left : D.bag ⟨i.val, hi⟩ ∩ S ⊆ D.bag ⟨i.val, hi⟩)
        (hD ⟨i.val, hi⟩).1
      refine ⟨hcapfin.union hTfin, (Set.ncard_union_le _ _).trans ?_⟩
      have := (hD ⟨i.val, hi⟩).2
      change (D.bag ⟨i.val, hi⟩ ∩ S).ncard + T.ncard ≤ k + T.ncard + 1
      omega
    · exact ⟨hTfin, by change T.ncard ≤ k + T.ncard + 1; omega⟩

end GraphMinor.GM01
