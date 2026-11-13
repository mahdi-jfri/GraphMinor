module

public import GraphMinor.GM01.PathCombs
import Lean.Elab.Tactic.Omega

/-!
# Cuts along the comb spine

On page 55 of Graph Minors I, the spine order determines the nested
regions used for blocks. In the source comb, assign each vertex to its
spine vertex. An edge crossing from strictly after a spine position to
that position or earlier must end at the spine vertex itself. Binary
copies cannot create another crossing because all their edges retain
the same spine index.
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph

/-- The spine position of a spine vertex or a vertex in its attached
binary copy (Graph Minors I, page 55). -/
def pathCombSpineIndex {δ : ℕ} : PathCombVertex δ → Fin δ
  | .inl i => i
  | .inr (i, _) => i

/-- An edge from after a spine cut to its earlier side must use the cut
vertex. This follows by checking spine edges and edges within attached
binary copies. -/
theorem pathComb_adj_crosses_spine_cut {γ δ : ℕ} {i : Fin δ}
    {x y : PathCombVertex δ} (hxy : (pathComb γ δ).Adj x y)
    (hx : i.val < (pathCombSpineIndex x).val)
    (hy : (pathCombSpineIndex y).val ≤ i.val) : y = Sum.inl i := by
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      have ha : i.val < a.val := hx
      have hb : b.val ≤ i.val := hy
      rcases pathGraph_adj.mp hxy with hforward | hback
      · omega
      · have hbi : b = i := Fin.ext (by omega)
        exact congrArg Sum.inl hbi
    | inr p =>
      rcases p with ⟨b, word⟩
      have hab : a = b := hxy.1
      have ha : i.val < a.val := hx
      have hb : b.val ≤ i.val := hy
      subst b
      omega
  | inr p =>
    rcases p with ⟨a, word⟩
    cases y with
    | inl b =>
      have hab : a = b := hxy.1
      have ha : i.val < a.val := hx
      have hb : b.val ≤ i.val := hy
      subst b
      omega
    | inr q =>
      rcases q with ⟨b, word'⟩
      have hab : a = b := hxy.1
      have ha : i.val < a.val := hx
      have hb : b.val ≤ i.val := hy
      subst b
      omega

/-- Deleting a spine vertex closes its later side under adjacency. This
is the source-side cut property to be transferred to the subdivision. -/
theorem pathComb_after_cut_adj_closed {γ δ : ℕ} {i : Fin δ}
    {x y : PathCombVertex δ} (hxy : (pathComb γ δ).Adj x y)
    (hx : i.val < (pathCombSpineIndex x).val) (hy : y ≠ Sum.inl i) :
    i.val < (pathCombSpineIndex y).val := by
  by_contra h
  exact hy (pathComb_adj_crosses_spine_cut hxy hx (by omega))

end GraphMinor.GM01
