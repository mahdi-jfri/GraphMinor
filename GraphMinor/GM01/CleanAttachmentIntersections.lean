module

public import GraphMinor.GM09.Basic

/-!
# Exact intersections of clean attachment paths

The paths in (2.9), used on page 60 of Graph Minors I, have no
internal vertex in the root support or the selected arm supports.
Their ends lie in disjoint supports. Hence a path meets the root
support only at its root end, its own arm only at its arm end, and
no other arm. These exact intersections are the conditions used in
the proved comb contraction.
-/

public section

namespace GraphMinor.GM01

open Set Graph Function GraphMinor.GM09

/-- The clean-interior condition of GM01 (2.9) gives all intersections
needed for the page-60 attachment contraction. -/
theorem attachment_intersections_of_clean_interiors {α β I : Type*} {G : Graph α β}
    (S : Set α) (B : I → Graph α β) (a b : I → α) (P : I → Graph α β)
    (hA : ∀ i, a i ∈ S) (hB : ∀ i, b i ∈ V(B i))
    (hP : ∀ i, IsGraphPathWithEnds G (P i) (a i) (b i))
    (hDis : ∀ i, Disjoint S V(B i))
    (hBD : Pairwise fun i j ↦ Disjoint V(B i) V(B j))
    (hClean : ∀ i x, x ∈ V(P i) → x ≠ a i → x ≠ b i → x ∉ S ∪ ⋃ j, V(B j)) :
    (∀ i, V(P i) ∩ S = {a i}) ∧ (∀ i, V(P i) ∩ V(B i) = {b i}) ∧
      (∀ i j, i ≠ j → Disjoint V(P i) V(B j)) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    apply Subset.antisymm
    · rintro x ⟨hxP,hxS⟩
      by_cases hxa : x = a i
      · exact hxa
      · have hxb : x ≠ b i := by
          intro heq
          exact disjoint_left.mp (hDis i) hxS (heq.symm ▸ hB i)
        exact False.elim (hClean i x hxP hxa hxb (Or.inl hxS))
    · exact singleton_subset_iff.mpr ⟨(hP i).left_mem,hA i⟩
  · intro i
    apply Subset.antisymm
    · rintro x ⟨hxP,hxB⟩
      by_cases hxb : x = b i
      · exact hxb
      · have hxa : x ≠ a i := by
          intro heq
          exact disjoint_left.mp (hDis i) (heq.symm ▸ hA i) hxB
        exact False.elim (hClean i x hxP hxa hxb (Or.inr (mem_iUnion.mpr ⟨i,hxB⟩)))
    · exact singleton_subset_iff.mpr ⟨(hP i).right_mem,hB i⟩
  · intro i j hij
    apply disjoint_left.mpr
    intro x hxP hxB
    have hxa : x ≠ a i := by
      intro heq
      exact disjoint_left.mp (hDis j) (heq.symm ▸ hA i) hxB
    have hxb : x ≠ b i := by
      intro heq
      exact disjoint_left.mp (hBD hij) (heq.symm ▸ hB i) hxB
    exact hClean i x hxP hxa hxb (Or.inr (mem_iUnion.mpr ⟨j,hxB⟩))

end GraphMinor.GM01
