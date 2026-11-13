module

public import GraphMinor.GM01.PathWidth

/-!
# Repeating the last bag of a path-decomposition

To concatenate the refinements in Graph Minors I, (1.6), page 40,
we may give all refinements the same length. Repeat their last bags.
The bag index is the minimum of the new index and the old last index.
This map is nondecreasing and preserves every old index, so edge
coverage and the interval condition are unchanged.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- Repeat the final bag to reach a specified longer length in the
refinement construction for GM01 (1.6), page 40. -/
@[expose] def PathDecomposition.pad {α β : Type*} {G : Graph α β}
    (D : PathDecomposition G) (hD : 0 < D.length) (N : ℕ) (hN : D.length ≤ N) :
    PathDecomposition G where
  length := N
  bag i := D.bag ⟨min i.val (D.length - 1), by omega⟩
  bag_subset i := D.bag_subset _
  edge_covered e x y he := by
    obtain ⟨i, hix, hiy⟩ := D.edge_covered e x y he
    refine ⟨⟨i.val, by omega⟩, ?_, ?_⟩
    · have hi : (⟨min i.val (D.length - 1), by omega⟩ : Fin D.length) = i :=
        Fin.ext (Nat.min_eq_left (by have := i.isLt; omega))
      simpa only [hi] using hix
    · have hi : (⟨min i.val (D.length - 1), by omega⟩ : Fin D.length) = i :=
        Fin.ext (Nat.min_eq_left (by have := i.isLt; omega))
      simpa only [hi] using hiy
  interval i j k hij hjk := D.interval _ _ _
    (min_le_min_right (D.length - 1) (show i.val ≤ j.val from hij))
    (min_le_min_right (D.length - 1) (show j.val ≤ k.val from hjk))

end GraphMinor.GM01
