module

public import GraphMinor.GM01.RootedGridDiagrams
public import GraphMinor.GM01.BinaryTrees
import GraphMinor.GM01.GridRegionModels
import GraphMinor.GM01.RootedModelComposition
import GraphMinor.GM01.BinaryModelsOfTwoArms

/-!
# The first level of the recursive grid construction

For each side of Figure 3, Graph Minors I, page 52, translate two
smaller rooted models into the top and bottom corner regions. Their
roots are adjacent to the side cross. Contract the cross to the new
root branch, using the proved separation and connectivity facts.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- Two smaller copies joined to a side cross give the next binary
height in the diagram proof of GM01 (3.2), pages 51–52. -/
noncomputable def rootedBinaryTreeModelInGridSide {a h : ℕ}
    (M : RootedMinorModel (binaryRootedTree h) (rootedGridDiagram a))
    (right : Bool) :
    RootedMinorModel (binaryRootedTree (h + 1)) (rootedGridDiagramSide a right) := by
  let B (bottom : Bool) : RootedGraph
      (Fin (2 * (2 * a + 1) + 1) × Fin (2 * (2 * a + 1) + 1))
      (Sym2 (Fin (2 * (2 * a + 1) + 1) × Fin (2 * (2 * a + 1) + 1))) :=
    ⟨(gridGraph _).induce (gridDiagramQuadrantRegion a bottom right),
      ⟨gridDiagramQuadrantMap a bottom right (gridDiagramRoot a),
        ⟨gridDiagramRoot a, gridDiagramRegion_root a, rfl⟩⟩⟩
  have hB : ∀ bottom, (B bottom).graph ≤ (rootedGridDiagramSide a right).graph := by
    intro bottom
    have hs : gridDiagramQuadrantRegion a bottom right ⊆ gridDiagramSideSupport a right := by
      intro v hv
      cases bottom
      · exact Or.inr (Or.inl hv)
      · exact Or.inr (Or.inr hv)
    exact ⟨hs, fun e x y he ↦ ⟨he.1, hs he.2.1, hs he.2.2⟩⟩
  let MB : ∀ bottom, RootedMinorModel (binaryRootedTree h) (B bottom) := fun bottom ↦
    M.trans (rootedModelOfGridRegionEmbedding (gridDiagramRegion a)
      (gridDiagramQuadrantRegion a bottom right)
      ⟨gridDiagramQuadrantMap a bottom right, gridDiagramQuadrantMap_injective a bottom right⟩
      (gridDiagramQuadrantMap_adj bottom right)
      (fun x hx ↦ ⟨x, hx, rfl⟩) ⟨gridDiagramRoot a, gridDiagramRegion_root a⟩)
  refine rootedBinaryTreeModelOfTwoArms (rootedGridDiagramSide a right)
    (gridDiagramSideRegion a right) (fun _ hv ↦ Or.inl hv) ?_
    (gridDiagramSideRoot_mem a right) B hB
    (fun bottom ↦ by simpa only [Nat.add_sub_cancel] using MB bottom) ?_ ?_ ?_
  · have hc := gridDiagramSideRegion_connected a right
    refine ⟨hc.1, ?_⟩
    intro x hx y hy
    apply Relation.ReflTransGen.mono ?_ x y (hc.2 x hx y hy)
    intro u v huv
    obtain ⟨e, he⟩ := huv
    exact ⟨e, ⟨he.1, Or.inl he.2.1, Or.inl he.2.2⟩, he.2⟩
  · intro bottom
    exact gridDiagramSideRegion_disjoint_quadrant a right bottom right
  · intro b b' hbb'
    exact gridDiagramQuadrantRegion_disjoint (fun he ↦ hbb' (congrArg Prod.fst he))
  · intro bottom
    obtain ⟨x, hx, e, he⟩ := gridDiagramQuadrantRoot_adj_side a bottom right
    refine ⟨e, x, hx, he, Or.inl hx, ?_⟩
    have hr : (B bottom).root.val ∈ gridDiagramSideSupport a right :=
      (hB bottom).vertexSet_mono (B bottom).root.property
    exact hr

end GraphMinor.GM01
