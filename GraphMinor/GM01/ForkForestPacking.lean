module

public import GraphMinor.GM01.RootedForestFamilies
public import GraphMinor.GM01.RootedForks
import GraphMinor.GM01.ForkPackingRoot
import GraphMinor.GM01.RootedSubgraphModelMinor
import GraphMinor.GM01.ForestCombMinor
import GraphMinor.GM01.Basic

/-!
# The disjoint forest family in a large fork

Graph Minors I, (5.2), page 61, extracts one rooted binary support
and `Ω+1` disjoint forest-tree supports from `Q(γ,3Ω+6)`. Use the
proved initial root support, which takes only the first two comb
cells. Group the remaining `3Ω+3` comb cells into triples. Each
triple retains its ordinary `Y_(γ−1)` minor by the proved three-cell
contraction. The actual interval bounds give all disjointness.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The actual source packing asserted in GM01 (5.2), page 61.
All sets satisfy (X1)/(X2), and exactly `Ω+1` other sets are constructed. -/
theorem exists_forest_family_in_large_fork {γ : ℕ} (hγ : 0 < γ) (Ω : ℕ) :
    Nonempty (RootedForestFamily (rootedForkGraph γ (3 * Ω + 6) hγ (by omega)) γ (Ω + 1)) := by
  classical
  let δ := 3 * Ω + 6
  have hδ : 3 ≤ δ := by dsimp [δ]; omega
  let G := rootedForkGraph γ δ hγ (by omega)
  have hVfin : V(G.graph).Finite := rootedFork_vertices_finite γ δ (by omega)
  have hEfin : E(G.graph).Finite := finite_edgeSet_of_finite_verts hVfin
  have hbound : ∀ i : Fin (Ω + 1), 2 + 3 * i.val + 3 ≤ δ - 1 := by
    intro i
    have hi := i.isLt
    dsimp [δ]
    omega
  let B := fun i : Fin (Ω + 1) ↦
    rootedForkCombSegment γ δ (by omega) 3 (by decide) (2 + 3 * i.val) (hbound i)
  have hBG : ∀ i, (B i).graph ≤ G.graph := fun i ↦
    rootedForkCombSegment_le hγ (by omega) 3 (by decide) (2 + 3 * i.val) (hbound i)
  have hOther : ∀ i, IsIsoMinor (forestTreeGraph (γ - 1)) (G.graph.induce V((B i).graph)) := by
    intro i
    let M := rootedForkCombSegmentModel γ δ (by omega) 3 (by decide) (2 + 3 * i.val) (hbound i)
    have hComb : IsIsoMinor (toGraph (pathComb (γ - 1) 3)) (B i).graph :=
      M.isIsoMinor_of_subgraph_source (pathComb_vertices_finite (γ - 1) 3)
        (rootedPathComb (γ - 1) 3 (by decide)).root (B i)
        (hVfin.subset (hBG i).vertexSet_mono) (hEfin.subset (hBG i).edgeSet_mono)
    have hForest := (forestTree_isIsoMinor_pathComb (γ - 1)).trans hComb
    have hOwn : (B i).graph ≤ G.graph.induce V((B i).graph) :=
      ⟨Subset.rfl,fun _ _ _ he ↦ ⟨he.mono (hBG i),he.left_mem,he.right_mem⟩⟩
    obtain ⟨K,hKB,edges,hEdges,hIso⟩ := hForest
    exact ⟨K,hKB.trans hOwn,edges,hEdges,hIso⟩
  have hBD : Pairwise fun i j : Fin (Ω + 1) ↦ Disjoint V((B i).graph) V((B j).graph) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · apply forkCombSegment_ranges_disjoint (hbound i) (hbound j)
      change i.val < j.val at hlt
      omega
    · apply Disjoint.symm
      apply forkCombSegment_ranges_disjoint (hbound j) (hbound i)
      change j.val < i.val at hlt
      omega
  refine ⟨{
    rootSet := forkPackingRootSet γ δ hδ
    otherSet := fun i ↦ V((B i).graph)
    root_subset := forkPackingRootSet_subset hγ hδ
    other_subset := fun i ↦ (hBG i).vertexSet_mono
    other_disjoint := hBD
    root_disjoint := fun i ↦ forkPackingRootSet_disjoint_segment hδ (by decide) (hbound i) (by omega)
    root_mem := Or.inl (Or.inl rfl)
    root_minor := ⟨rootedBinaryTreeModelInForkPackingRoot hγ hδ⟩
    other_minor := hOther }⟩

end GraphMinor.GM01
