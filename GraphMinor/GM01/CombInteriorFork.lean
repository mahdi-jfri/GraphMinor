module

public import GraphMinor.GM01.RootedForkAssembly
public import GraphMinor.GM01.CombShiftRanges
import GraphMinor.GM01.BinaryCombModel
import GraphMinor.GM01.Basic
import GraphMinor.GM01.ConnectedGraphImages
import GraphMinor.GM01.PathCombTrees
import GraphMinor.GM01.RootedEmbeddings
import GraphMinor.GM01.RootedModelComposition

/-!
# The fork contraction on an interior-rooted comb

In Graph Minors I, (4.9), page 58, the first two cells provide the
binary arm when the root is beyond them and enough cells remain on
the other side. Contract the middle cells to the fork root and retain
the following cells as its comb arm. The actual edges at the two
interval boundaries join these arms. Reflection handles the other
orientation in the full end-location argument.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function

/-- The first orientation of the source contraction in GM01 (4.9),
page 58. The root lies after the first two cells and leaves at least
`δ-1` cells to its right for the comb arm. -/
noncomputable def rootedForkModelOfCombInteriorRight {γ δ L : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (v : (pathComb (γ - 1) L).verts)
    (hv : 2 ≤ (pathCombSpineIndex v.val).val)
    (hlong : (pathCombSpineIndex v.val).val + δ ≤ L) :
    RootedMinorModel (rootedForkGraph γ δ hγ hδ)
      (⟨toGraph (pathComb (γ - 1) L), v⟩ : RootedGraph (PathCombVertex L) (Sym2 (PathCombVertex L))) := by
  let q := (pathCombSpineIndex v.val).val
  let S := pathComb (γ - 1) L
  let G : RootedGraph (PathCombVertex L) (Sym2 (PathCombVertex L)) := ⟨toGraph S, v⟩
  have hBbound : 0 + 2 ≤ L := by omega
  have hCbound : 2 + (q - 1) ≤ L := by dsimp [q]; omega
  have hPbound : (q + 1) + (δ - 1) ≤ L := by dsimp [q]; omega
  let fB : (pathComb (γ - 1) 2).verts ↪ PathCombVertex L :=
    (combShiftEmbedding 0 hBbound).trans ⟨Subtype.val, Subtype.val_injective⟩
  let fC : (pathComb (γ - 1) (q - 1)).verts ↪ PathCombVertex L :=
    (combShiftEmbedding 2 hCbound).trans ⟨Subtype.val, Subtype.val_injective⟩
  let fP : (pathComb (γ - 1) (δ - 1)).verts ↪ PathCombVertex L :=
    (combShiftEmbedding (q + 1) hPbound).trans ⟨Subtype.val, Subtype.val_injective⟩
  let B := range fB
  let C := range fC
  let A := range fP
  let KB := S.induce B
  let KP := S.induce A
  let b : (pathComb (γ - 1) 2).verts := ⟨Sum.inl (1 : Fin 2), pathComb_spine_mem _ _ _⟩
  let p := (rootedPathComb (γ - 1) (δ - 1) (by omega)).root
  let GB : RootedGraph (PathCombVertex L) (Sym2 (PathCombVertex L)) :=
    ⟨toGraph KB, ⟨fB b, mem_range_self b⟩⟩
  let GP : RootedGraph (PathCombVertex L) (Sym2 (PathCombVertex L)) :=
    ⟨toGraph KP, ⟨fP p, mem_range_self p⟩⟩
  have hBsub : B ⊆ S.verts := by
    rintro x ⟨w, rfl⟩
    exact (combShiftEmbedding 0 hBbound w).property
  have hCsub : C ⊆ S.verts := by
    rintro x ⟨w, rfl⟩
    exact (combShiftEmbedding 2 hCbound w).property
  have hAsub : A ⊆ S.verts := by
    rintro x ⟨w, rfl⟩
    exact (combShiftEmbedding (q + 1) hPbound w).property
  have hGB : GB.graph ≤ G.graph := toGraph_mono
    ⟨hBsub, fun _ _ h ↦ h.2.2⟩
  have hGP : GP.graph ≤ G.graph := toGraph_mono
    ⟨hAsub, fun _ _ h ↦ h.2.2⟩
  let MBsmall := rootedModelOfSubgraphEmbedding (pathComb (γ - 1) 2) KB fB
    (fun w ↦ mem_range_self w)
    (fun {u w} huw ↦ ⟨mem_range_self u, mem_range_self w, combShiftEmbedding_adj 0 hBbound huw⟩) b
  let MB : RootedMinorModel (binaryRootedTree (γ - 1)) GB :=
    (binaryTree_model_in_two_cell_comb_at (γ - 1) 1).trans MBsmall
  let MP : RootedMinorModel (rootedPathComb (γ - 1) (δ - 1) (by omega)) GP :=
    rootedModelOfSubgraphEmbedding (pathComb (γ - 1) (δ - 1)) KP fP
      (fun w ↦ mem_range_self w)
      (fun {u w} huw ↦ ⟨mem_range_self u, mem_range_self w,
        combShiftEmbedding_adj (q + 1) hPbound huw⟩) p
  have hCconn : GraphConnected (G.graph.induce C) := by
    apply graphConnected_image_of_simpleMap (pathComb (γ - 1) (q - 1)).coe
      (pathComb_connected (γ := γ - 1) (by dsimp [q]; omega)).coe
      (rootedPathComb (γ - 1) (q - 1) (by dsimp [q]; omega)).root fC
    intro a b hab
    exact ⟨s(fC a,fC b), rfl, combShiftEmbedding_adj 2 hCbound hab⟩
  have hroot : G.root.val ∈ C := by
    apply (mem_range_combShiftEmbedding_val_iff 2 hCbound v.val).mpr
    exact ⟨v.property, hv, by dsimp [q]; omega⟩
  have hCB : Disjoint C B :=
    (disjoint_combShiftEmbedding_val_ranges 0 2 hBbound hCbound (by omega)).symm
  have hCP : Disjoint C A :=
    disjoint_combShiftEmbedding_val_ranges 2 (q + 1) hCbound hPbound (by dsimp [q]; omega)
  have hPB : Disjoint A B :=
    (disjoint_combShiftEmbedding_val_ranges 0 (q + 1) hBbound hPbound (by dsimp [q]; omega)).symm
  have hjoinP : ∃ e x, x ∈ C ∧ G.graph.IsLink e x GP.root.val := by
    let u : PathCombVertex L := Sum.inl ⟨q, (pathCombSpineIndex v.val).isLt⟩
    have hu : u ∈ C := by
      apply (mem_range_combShiftEmbedding_val_iff 2 hCbound u).mpr
      exact ⟨pathComb_spine_mem _ _ _, hv, by change q < 2 + (q - 1); dsimp [q]; omega⟩
    refine ⟨s(u,GP.root.val), u, hu, rfl, ?_⟩
    apply pathComb_spine_adj (γ := γ - 1)
    apply pathGraph_adj.mpr
    exact Or.inl (by change q + 1 = (q + 1) + 0; omega)
  have hjoinB : ∃ e x, x ∈ C ∧ G.graph.IsLink e x GB.root.val := by
    let u : PathCombVertex L := Sum.inl ⟨2, by omega⟩
    have hu : u ∈ C := by
      apply (mem_range_combShiftEmbedding_val_iff 2 hCbound u).mpr
      exact ⟨pathComb_spine_mem _ _ _, le_rfl, by change 2 < 2 + (q - 1); dsimp [q]; omega⟩
    refine ⟨s(u,GB.root.val), u, hu, rfl, ?_⟩
    apply pathComb_spine_adj (γ := γ - 1)
    apply pathGraph_adj.mpr
    exact Or.inr (by change (0 + 1) + 1 = 2; omega)
  exact rootedForkModelOfArms hγ hδ G C hCsub hCconn hroot hGP hGB MP MB
    hCP hCB hPB hjoinP hjoinB

end GraphMinor.GM01
