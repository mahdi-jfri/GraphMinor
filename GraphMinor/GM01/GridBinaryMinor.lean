module

public import GraphMinor.GM01.BinaryTrees
public import GraphMinor.GM01.Defs
import GraphMinor.GM01.GridDiagramInduction
import GraphMinor.GM01.RootedSubgraphModelMinor
import Lean.Elab.Tactic.Omega

/-!
# Binary trees as grid minors

This proves Graph Minors I, (3.2), page 51, by the two-level
induction shown in Figure 3. Forget the root of the constructed
model and restore the unused grid vertices. The printed exponent
is a misprint: the diagram for height six has side fifteen, and
the one-vertex base has side one. The corrected exponent is
`λ / 2 + 1` for even `λ`. See the correction to (3.2) in
`corrections/GM01.md`.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- Forgetting the root of the closed diagram construction gives the
ordinary grid minor at every even binary-tree height. -/
theorem binaryTree_isIsoMinor_grid (n : ℕ) :
    IsIsoMinor (toGraph (binaryTree (2 * n))) (gridGraph (2 ^ (n + 1) - 1)) := by
  obtain ⟨M⟩ := exists_rootedBinaryTreeModelInGrid n
  let a := 2 ^ n - 1
  let G : RootedGraph (Fin (2 * a + 1) × Fin (2 * a + 1))
      (Sym2 (Fin (2 * a + 1) × Fin (2 * a + 1))) :=
    ⟨gridGraph (2 * a + 1), ⟨gridDiagramRoot a, mem_univ _⟩⟩
  have hle : (rootedGridDiagram a).graph ≤ G.graph :=
    (gridGraph (2 * a + 1)).induce_le (fun _ _ ↦ mem_univ _)
  let L := M.mono hle rfl
  have hminor := L.isIsoMinor_of_subgraph_source (binaryTree_vertices_finite (2 * n))
    (binaryRootedTree (2 * n)).root G (Set.toFinite _) (Set.toFinite _)
  change IsIsoMinor (toGraph (binaryTree (2 * n))) (gridGraph (2 * (2 ^ n - 1) + 1)) at hminor
  have hpos : 0 < 2 ^ n := Nat.pow_pos (by decide)
  have hsize : 2 * (2 ^ n - 1) + 1 = 2 ^ (n + 1) - 1 := by
    rw [pow_succ]
    omega
  rw [hsize] at hminor
  exact hminor

/-- Graph Minors I, (3.2), page 51: "For any even $\lambda \ge 0$, the
$(2^{(\lambda+1)/2}-1)$-grid has a minor isomorphic to $\mathbf{H}_\lambda$."
The printed exponent is corrected to `λ / 2 + 1`. This is the smallest
correction consistent with the one-vertex base and Figure 3's height-six
subdivision in the fifteen-grid. The proof follows that diagram's
induction, adding two levels at each step. -/
theorem theorem_3_2_proof (lam : ℕ) (heven : Even lam) :
    IsIsoMinor (toGraph (binaryTree lam)) (gridGraph (2 ^ (lam / 2 + 1) - 1)) := by
  obtain ⟨n, hn⟩ := heven
  have hheight : lam = 2 * n := by omega
  rw [hheight]
  have hdiv : 2 * n / 2 = n := by omega
  rw [hdiv]
  exact binaryTree_isIsoMinor_grid n

end GraphMinor.GM01
