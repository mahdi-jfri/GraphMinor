module

public import GraphMinor.GM01.RootedGridDiagrams
public import GraphMinor.GM01.BinaryTrees
import GraphMinor.GM01.GridDiagramInductionStep
import GraphMinor.GM01.RootedSubgraphBranchModels
import Lean.Elab.Tactic.Omega

/-!
# Closing the grid diagram induction

The one-vertex diagram starts the construction of Graph Minors I,
(3.2), pages 51–52. Each step doubles the square's radius and adds
one, while adding two binary-tree levels. The resulting radius is
`2^n - 1` at height `2n`. This proves the diagram construction without
leaving its recursive existence as a hypothesis.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The diagram of height zero consists of its single root. -/
noncomputable def rootedBinaryTreeModelInGrid_zero :
    RootedMinorModel (binaryRootedTree 0) (rootedGridDiagram 0) := by
  let G := rootedGridDiagram 0
  have huniq : ∀ x : (binaryTree 0).verts, x.val = [] := by
    intro x
    exact (Set.ext_iff.mp binaryTree_zero_verts x.val).mp x.property
  refine rootedModelOfSubgraphBranchSets (binaryTree 0) G
    (fun _ ↦ {G.root.val}) (fun _ ↦ singleton_subset_iff.mpr G.root.property) ?_ ?_ ?_
    ⟨[], binaryTree_root_mem 0⟩ rfl
  · intro x y hxy
    exact False.elim (hxy (Subtype.ext ((huniq x).trans (huniq y).symm)))
  · intro x
    refine ⟨⟨G.root.val, rfl⟩, ?_⟩
    intro u hu v hv
    have hu' : u = G.root.val := hu
    have hv' : v = G.root.val := hv
    subst u
    subst v
    exact .refl
  · intro x y hxy
    exact False.elim (hxy.ne (Subtype.ext ((huniq x).trans (huniq y).symm)))

/-- The closed two-level induction behind Figure 3 and GM01 (3.2),
pages 51–52. Its support retains the free central column. -/
theorem exists_rootedBinaryTreeModelInGrid (n : ℕ) :
    Nonempty (RootedMinorModel (binaryRootedTree (2 * n))
      (rootedGridDiagram (2 ^ n - 1))) := by
  induction n with
  | zero => exact ⟨rootedBinaryTreeModelInGrid_zero⟩
  | succ n ih =>
    obtain ⟨M⟩ := ih
    have L := rootedBinaryTreeModelInGrid_step M
    have hheight : 2 * n + 2 = 2 * (n + 1) := by omega
    have hpos : 0 < 2 ^ n := Nat.pow_pos (by decide)
    have hradius : 2 * (2 ^ n - 1) + 1 = 2 ^ (n + 1) - 1 := by
      rw [pow_succ]
      omega
    rw [hheight, hradius] at L
    exact ⟨L⟩

end GraphMinor.GM01
