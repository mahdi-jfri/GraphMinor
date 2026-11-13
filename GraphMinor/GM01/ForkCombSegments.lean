module

public import GraphMinor.GM01.ForkArmEmbeddings
public import GraphMinor.GM01.CombShifts
import GraphMinor.GM01.CombShiftRanges
import GraphMinor.GM01.Basic

/-!
# Consecutive comb intervals inside the fork

Graph Minors I, (5.2), page 61, packs forest minors in disjoint
three-cell intervals after the initial two comb cells. Shift the
small comb into its specified interval, then include it in the
fork's comb arm. Its induced support has the actual inclusion model.
Disjoint index intervals give disjoint supports, all avoiding the
fork root and its binary arm.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- Include a consecutive comb interval in the actual fork labels. -/
def forkCombSegmentEmbedding (γ δ m offset : ℕ) (hbound : offset + m ≤ δ - 1) :
    (pathComb (γ - 1) m).verts ↪ RootedForkVertex δ :=
  (combShiftEmbedding offset hbound).trans (forkCombEmbedding γ δ)

/-- The selected comb interval, rooted at its first spine vertex. -/
def rootedForkCombSegment (γ δ : ℕ) (hδ : 2 ≤ δ) (m : ℕ) (hm : 0 < m)
    (offset : ℕ) (hbound : offset + m ≤ δ - 1) :
    RootedGraph (RootedForkVertex δ) (Sym2 (RootedForkVertex δ)) :=
  ⟨toGraph ((rootedFork γ δ hδ).induce (range (forkCombSegmentEmbedding γ δ m offset hbound))),
    ⟨forkCombSegmentEmbedding γ δ m offset hbound (rootedPathComb (γ - 1) m hm).root,
      mem_range_self _⟩⟩

/-- The actual inclusion model of a selected comb interval, used in
the packing of GM01 (5.2), page 61. -/
noncomputable def rootedForkCombSegmentModel (γ δ : ℕ) (hδ : 2 ≤ δ) (m : ℕ) (hm : 0 < m)
    (offset : ℕ) (hbound : offset + m ≤ δ - 1) :
    RootedMinorModel (rootedPathComb (γ - 1) m hm)
      (rootedForkCombSegment γ δ hδ m hm offset hbound) :=
  rootedModelOfSubgraphEmbedding (pathComb (γ - 1) m)
    ((rootedFork γ δ hδ).induce (range (forkCombSegmentEmbedding γ δ m offset hbound)))
    (forkCombSegmentEmbedding γ δ m offset hbound) (fun v ↦ mem_range_self v)
    (fun {u v} huv ↦ ⟨mem_range_self u,mem_range_self v,combShiftEmbedding_adj offset hbound huv⟩)
    (rootedPathComb (γ - 1) m hm).root

/-- A selected interval is an actual subgraph of the full fork. -/
theorem rootedForkCombSegment_le {γ δ : ℕ} (hγ : 0 < γ) (hδ : 2 ≤ δ)
    (m : ℕ) (hm : 0 < m) (offset : ℕ) (hbound : offset + m ≤ δ - 1) :
    (rootedForkCombSegment γ δ hδ m hm offset hbound).graph ≤ (rootedForkGraph γ δ hγ hδ).graph := by
  apply toGraph_mono
  refine ⟨?_,fun _ _ h ↦ h.2.2⟩
  rintro x ⟨v,rfl⟩
  exact (combShiftEmbedding offset hbound v).property

/-- The selected interval lies in the full comb arm's vertex support. -/
theorem forkCombSegment_range_subset {γ δ m offset : ℕ} (hbound : offset + m ≤ δ - 1) :
    range (forkCombSegmentEmbedding γ δ m offset hbound) ⊆ range (forkCombEmbedding γ δ) := by
  rintro x ⟨v,rfl⟩
  exact ⟨combShiftEmbedding offset hbound v,rfl⟩

/-- Two disjoint consecutive intervals have disjoint fork supports. -/
theorem forkCombSegment_ranges_disjoint {γ δ m m' offset offset' : ℕ}
    (hbound : offset + m ≤ δ - 1) (hbound' : offset' + m' ≤ δ - 1)
    (hgap : offset + m ≤ offset') :
    Disjoint (range (forkCombSegmentEmbedding γ δ m offset hbound))
      (range (forkCombSegmentEmbedding γ δ m' offset' hbound')) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨u,rfl⟩ ⟨v,hv⟩
  have heq := Sum.inl.inj (Option.some.inj hv)
  exact Set.disjoint_left.mp (disjoint_combShiftEmbedding_val_ranges (γ := γ - 1)
    offset offset' hbound hbound' hgap) ⟨u,rfl⟩ ⟨v,heq⟩

/-- Every selected comb interval avoids the fork root and binary arm. -/
theorem rootedFork_root_binary_disjoint_segment {γ δ : ℕ} (hδ : 2 ≤ δ)
    (m : ℕ) (hm : 0 < m) (offset : ℕ) (hbound : offset + m ≤ δ - 1) :
    Disjoint V((rootedForkRootBinaryPiece γ δ hδ).graph)
      V((rootedForkCombSegment γ δ hδ m hm offset hbound).graph) :=
  (rootedFork_root_binary_disjoint_comb γ δ hδ).mono_right (forkCombSegment_range_subset hbound)

end GraphMinor.GM01
