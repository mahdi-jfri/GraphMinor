module

public import GraphMinor.GM01.OneCellCombModels
import GraphMinor.GM01.Basic
import GraphMinor.GM01.BinaryCombModel
import GraphMinor.GM01.CombShiftRanges
import GraphMinor.GM01.RootedModelComposition

/-!
# Raising the height of one comb cell

At the start of Graph Minors I, Part 3, page 59, the first three
cells of the lower-height comb provide one cell at the next height.
Keep its first spine vertex as the root piece. The last two cells
supply the binary-tree arm by the proved two-cell contraction.
The first spine edge joins them.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function

/-- Contract the last two of three lower-height cells to the binary
arm of one cell, as used in the initial source contractions of GM01
Part 3, page 59. -/
noncomputable def rootedOneCellCombModelInLowerThree {γ : ℕ} (hγ : 0 < γ) :
    RootedMinorModel (rootedPathComb γ 1 (by decide)) (rootedPathComb (γ - 1) 3 (by decide)) := by
  let S := pathComb (γ - 1) 3
  let G := rootedPathComb (γ - 1) 3 (by decide)
  let f : (pathComb (γ - 1) 2).verts ↪ PathCombVertex 3 :=
    (combShiftEmbedding 1 (by decide : 1 + 2 ≤ 3)).trans ⟨Subtype.val, Subtype.val_injective⟩
  let B := range f
  let KB := S.induce B
  let r := (rootedPathComb (γ - 1) 2 (by decide)).root
  let GB : RootedGraph (PathCombVertex 3) (Sym2 (PathCombVertex 3)) :=
    ⟨toGraph KB, ⟨f r, mem_range_self r⟩⟩
  have hBsub : B ⊆ S.verts := by
    rintro x ⟨v, rfl⟩
    exact (combShiftEmbedding 1 (by decide : 1 + 2 ≤ 3) v).property
  have hGB : GB.graph ≤ G.graph := toGraph_mono ⟨hBsub, fun _ _ h ↦ h.2.2⟩
  let small := rootedModelOfSubgraphEmbedding (pathComb (γ - 1) 2) KB f
    (fun v ↦ mem_range_self v)
    (fun {u v} huv ↦ ⟨mem_range_self u, mem_range_self v,
      combShiftEmbedding_adj 1 (by decide : 1 + 2 ≤ 3) huv⟩) r
  let MB : RootedMinorModel (binaryRootedTree (γ - 1)) GB :=
    (binaryTree_model_in_two_cell_comb (γ - 1)).trans small
  have hC : ({G.root.val} : Set (PathCombVertex 3)) ⊆ V(G.graph) := singleton_subset_iff.mpr G.root.property
  have hconn : GraphConnected (G.graph.induce {G.root.val}) := by
    refine ⟨⟨G.root.val, rfl⟩, ?_⟩
    intro x hx y hy
    have hx' : x = G.root.val := hx
    have hy' : y = G.root.val := hy
    subst x
    subst y
    exact .refl
  have hdis : Disjoint ({G.root.val} : Set (PathCombVertex 3)) V(GB.graph) := by
    apply Set.disjoint_left.mpr
    intro x hx hxB
    have hx' : x = G.root.val := hx
    subst x
    obtain ⟨v, hv⟩ := hxB
    have hi := congrArg (fun z : PathCombVertex 3 ↦ (pathCombSpineIndex z).val) hv
    change (pathCombSpineIndex (combShiftEmbedding 1 (by decide : 1 + 2 ≤ 3) v).val).val = 0 at hi
    rw [combShiftEmbedding_spineIndex] at hi
    omega
  have hjoin : ∃ e x, x ∈ ({G.root.val} : Set (PathCombVertex 3)) ∧ G.graph.IsLink e x GB.root.val := by
    refine ⟨s(G.root.val,GB.root.val), G.root.val, rfl, rfl, ?_⟩
    exact pathComb_spine_adj (γ := γ - 1) (pathGraph_adj.mpr (Or.inl rfl))
  exact rootedOneCellCombModelOfBinaryArm hγ G {G.root.val} hC hconn rfl GB hGB MB hdis hjoin

end GraphMinor.GM01
