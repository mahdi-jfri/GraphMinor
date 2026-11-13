module

public import GraphMinor.GM01.RootedGridDiagrams
public import GraphMinor.GM01.BinaryTrees
import GraphMinor.GM01.GridDiagramSideModels
import GraphMinor.GM01.BinaryModelsOfTwoArms
import Lean.Elab.Tactic.Omega

/-!
# The two-level induction in the grid diagram

Graph Minors I proves (3.2), pages 51–52, by repeating the construction
in Figure 3. Four smaller diagrams give two side arms. Joining these
to the singleton central root adds two levels to the binary tree.
The free centre column is retained for the next repetition.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- The two-level recursive construction in Figure 3, proving the
induction step for GM01 (3.2), pages 51–52. -/
noncomputable def rootedBinaryTreeModelInGrid_step {a h : ℕ}
    (M : RootedMinorModel (binaryRootedTree h) (rootedGridDiagram a)) :
    RootedMinorModel (binaryRootedTree (h + 2)) (rootedGridDiagram (2 * a + 1)) := by
  let G := rootedGridDiagram (2 * a + 1)
  let B := rootedGridDiagramSide a
  have hB : ∀ side, (B side).graph ≤ G.graph := by
    intro side
    have hs := gridDiagramSideSupport_subset a side
    exact ⟨hs, fun e x y he ↦ ⟨he.1, hs he.2.1, hs he.2.2⟩⟩
  refine rootedBinaryTreeModelOfTwoArms G {G.root.val}
    (singleton_subset_iff.mpr G.root.property) ?_ (by rfl) B hB
    (fun side ↦ by
      have hh : h + 2 - 1 = h + 1 := by omega
      rw [hh]
      exact rootedBinaryTreeModelInGridSide M side)
    ?_ ?_ ?_
  · refine ⟨⟨G.root.val, rfl⟩, ?_⟩
    intro x hx y hy
    have hx' : x = G.root.val := hx
    have hy' : y = G.root.val := hy
    subst x
    subst y
    exact .refl
  · intro side
    apply Set.disjoint_singleton_left.mpr
    exact gridDiagramSideSupport_not_centre a side
  · intro side side' hne
    cases side <;> cases side'
    · exact False.elim (hne rfl)
    · exact gridDiagramSideSupport_disjoint a
    · exact (gridDiagramSideSupport_disjoint a).symm
    · exact False.elim (hne rfl)
  · intro side
    obtain ⟨e, he⟩ := gridDiagramRoot_adj_side a side
    refine ⟨e, G.root.val, rfl, he, G.root.property, ?_⟩
    exact (hB side).vertexSet_mono (B side).root.property

end GraphMinor.GM01
