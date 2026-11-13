module

public import GraphMinor.GM01.ForestTrees
public import GraphMinor.GM01.PathWidth
import GraphMinor.GM01.ThreeBranchWidthLowerBound
import GraphMinor.GM01.BinaryTreeInForestBranch
import GraphMinor.GM01.ForestBinaryMinor
import GraphMinor.GM01.PathWidthMinors
import GraphMinor.GM01.Basic
import GraphMinor.Minor.Basic
import Lean.Elab.Tactic.Omega

/-!
# Forest trees have unbounded path-width

This supplies observation (b) in Graph Minors I, page 40. At odd
height `2k+1`, the tree `Y` cannot have width `k`. The base contains
an edge. For the step, each of the three branches contains the
previous `Y` as a minor, by (3.3) inside its binary subtree. The
three-branch bag argument then forces one more unit of width.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The edge in `Y_1` rules out width zero, the base of the page-40
unbounded-tree-width observation. -/
theorem forestTree_one_not_width_zero : ¬ HasPathWidthLE (forestTreeGraph 1) 0 := by
  rintro ⟨D, hD⟩
  have he : (forestTreeGraph 1).IsLink s(none, some (0, [])) none (some (0, [])) :=
    ⟨rfl, by exact ⟨(by change 0 ≤ 1; decide), (by change 1 ≤ 1; decide), Or.inl ⟨(by intro hn; cases hn), rfl⟩⟩⟩
  obtain ⟨i, hx, hy⟩ := D.edge_covered _ _ _ he
  have hpair : ({none, some (0, [])} : Set ForestTreeVertex) ⊆ D.bag i := by
    intro x h
    rcases h with h | h
    · exact h ▸ hx
    · exact h ▸ hy
  have hcard := Set.ncard_le_ncard hpair (hD i).1
  have hp : ({none, some (0, [])} : Set ForestTreeVertex).ncard = 2 := by simp
  rw [hp] at hcard
  have hbound := (hD i).2
  omega

/-- Observation (b) for GM01 (1.2), page 40: the odd-height trees
`Y_(2k+1)` have path-width greater than `k`. The proof follows the
three branches and their connected complements. -/
theorem forestTree_odd_not_hasPathWidthLE (k : ℕ) :
    ¬ HasPathWidthLE (forestTreeGraph (2 * k + 1)) k := by
  induction k with
  | zero => exact forestTree_one_not_width_zero
  | succ k ih =>
    let lam := 2 * (k + 1) + 1
    let G := forestTreeGraph lam
    let K (i : Fin 3) := G.induce (forestTreeBranchVertices lam i)
    let C (i : Fin 3) := G.induce (forestTreeBranchComplement lam i)
    have hKG : ∀ i, K i ≤ G := fun _ ↦ G.induce_le (fun _ hv ↦ hv.1)
    have hNo : ∀ i, ¬ HasPathWidthLE (K i) k := by
      intro i hWidth
      have hMinor := (theorem_3_3_proof (2 * k + 1) (by omega)).trans
        (binaryTree_isIsoMinor_forestTreeBranch (2 * k + 2) i)
      have hlevel : 2 * k + 2 + 1 = lam := by omega
      rw [hlevel] at hMinor
      exact ih (hWidth.of_isIsoMinor (forestTree_vertices_finite (2 * k + 1))
        ((forestTree_vertices_finite lam).subset (hKG i).vertexSet_mono)
        ((finite_edgeSet_of_finite_verts (forestTree_vertices_finite lam)).subset (hKG i).edgeSet_mono)
        hMinor)
    exact not_hasPathWidthLE_of_three_branches (Nat.zero_lt_succ k) K C hKG
      (forestTreeBranchVertices_disjoint lam)
      (fun i ↦ by simpa only [Nat.add_sub_cancel] using hNo i)
      (fun _ ↦ G.induce_le (fun _ hv ↦ hv.1))
      (forestTreeBranchComplement_connected lam)
      (fun _ _ h ↦ forestTreeBranchVertices_subset_complement h)
      (forestTreeBranchComplement_disjoint lam)

end GraphMinor.GM01
