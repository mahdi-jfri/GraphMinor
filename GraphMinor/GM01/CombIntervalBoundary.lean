module

public import GraphMinor.GM01.CombSpineCuts

/-!
# The unique edge across a comb interval boundary

In the contraction proving Graph Minors I, (4.12), page 59, the
second end is separated from the other cells by a single spine edge.
An edge between distinct cell intervals cannot belong to an attached
binary tree. Checking the spine adjacency then identifies both ends.
-/

public section

namespace GraphMinor.GM01

open SimpleGraph

/-- A comb edge crossing the boundary at cell `k` is precisely the
spine edge between cells `k - 1` and `k`. -/
theorem pathComb_adj_crosses_interval_boundary {γ L k : ℕ}
    (hk : 0 < k) (hkL : k < L) {a b : PathCombVertex L}
    (hab : (pathComb γ L).Adj a b)
    (ha : (pathCombSpineIndex a).val < k)
    (hb : k ≤ (pathCombSpineIndex b).val) :
    a = Sum.inl ⟨k - 1, by omega⟩ ∧ b = Sum.inl ⟨k, hkL⟩ := by
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      change i.val < k at ha
      change k ≤ j.val at hb
      rcases pathGraph_adj.mp hab with h | h
      · exact ⟨congrArg Sum.inl (Fin.ext (by change i.val = k - 1; omega)),
          congrArg Sum.inl (Fin.ext (by change j.val = k; omega))⟩
      · omega
    | inr p =>
      have heq := congrArg Fin.val hab.1
      change i.val < k at ha
      change k ≤ p.1.val at hb
      omega
  | inr p =>
    cases b with
    | inl j =>
      have heq := congrArg Fin.val hab.1
      change p.1.val < k at ha
      change k ≤ j.val at hb
      omega
    | inr p' =>
      have heq := congrArg Fin.val hab.1
      change p.1.val < k at ha
      change k ≤ p'.1.val at hb
      omega

end GraphMinor.GM01
