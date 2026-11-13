module

public import GraphMinor.GM01.ForkCombSegments
import GraphMinor.GM01.BinaryModelsOfTwoArms
import GraphMinor.GM01.BinaryCombModel
import GraphMinor.GM01.RootedModelComposition

/-!
# The root support in the fork packing

For Graph Minors I, (5.2), page 61, keep the fork root, its binary
arm, and the first two comb cells. Those two cells contain a binary
minor of the same height as the binary arm. Join these two models
to the fork root to obtain the next-height rooted binary minor.
All later three-cell intervals are disjoint from this root support.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The fork root, its binary arm, and the first two comb cells. -/
@[expose] def forkPackingRootSet (γ δ : ℕ) (hδ : 3 ≤ δ) : Set (RootedForkVertex δ) :=
  V((rootedForkRootBinaryPiece γ δ (by omega)).graph) ∪
    V((rootedForkCombSegment γ δ (by omega) 2 (by decide) 0 (by omega)).graph)

/-- The induced root support for the packing in GM01 (5.2). -/
@[expose] def rootedForkPackingRoot (γ δ : ℕ) (hγ : 0 < γ) (hδ : 3 ≤ δ) :
    RootedGraph (RootedForkVertex δ) (Sym2 (RootedForkVertex δ)) :=
  ⟨(rootedForkGraph γ δ hγ (by omega)).graph.induce (forkPackingRootSet γ δ hδ),
    ⟨none,Or.inl (Or.inl rfl)⟩⟩

/-- The root support lies in the actual fork vertex set. -/
theorem forkPackingRootSet_subset {γ δ : ℕ} (hγ : 0 < γ) (hδ : 3 ≤ δ) :
    forkPackingRootSet γ δ hδ ⊆ V((rootedForkGraph γ δ hγ (by omega)).graph) :=
  union_subset (rootedForkRootBinaryPiece_le γ δ hγ (by omega)).vertexSet_mono
    (rootedForkCombSegment_le hγ (by omega) 2 (by decide) 0 (by omega)).vertexSet_mono

/-- Two initial comb cells suffice for the rooted binary minor in the
root support of the packing in GM01 (5.2), page 61. -/
noncomputable def rootedBinaryTreeModelInForkPackingRoot {γ δ : ℕ}
    (hγ : 0 < γ) (hδ : 3 ≤ δ) :
    RootedMinorModel (binaryRootedTree γ) (rootedForkPackingRoot γ δ hγ hδ) := by
  let F := rootedForkGraph γ δ hγ (by omega)
  let G := rootedForkPackingRoot γ δ hγ hδ
  let C : Set (RootedForkVertex δ) := {none}
  let B : Bool → RootedGraph (RootedForkVertex δ) (Sym2 (RootedForkVertex δ)) := fun bit ↦
    if bit then rootedForkBinaryArm γ δ (by omega)
    else rootedForkCombSegment γ δ (by omega) 2 (by decide) 0 (by omega)
  have hBF : ∀ bit, (B bit).graph ≤ F.graph := by
    intro bit
    cases bit
    · exact rootedForkCombSegment_le hγ (by omega) 2 (by decide) 0 (by omega)
    · exact (rootedForkBinaryArm_le_root_piece γ δ (by omega)).trans
        (rootedForkRootBinaryPiece_le γ δ hγ (by omega))
  have hBS : ∀ bit, V((B bit).graph) ⊆ forkPackingRootSet γ δ hδ := by
    intro bit
    cases bit
    · exact subset_union_right
    · exact (rootedForkBinaryArm_le_root_piece γ δ (by omega)).vertexSet_mono.trans subset_union_left
  have hBG : ∀ bit, (B bit).graph ≤ G.graph := by
    intro bit
    refine ⟨hBS bit,?_⟩
    intro e x y he
    exact ⟨he.mono (hBF bit),hBS bit he.left_mem,hBS bit he.right_mem⟩
  let MB : ∀ bit, RootedMinorModel (binaryRootedTree (γ - 1)) (B bit) := fun bit ↦ by
    cases bit
    · exact (binaryTree_model_in_two_cell_comb (γ - 1)).trans
        (rootedForkCombSegmentModel γ δ (by omega) 2 (by decide) 0 (by omega))
    · exact rootedForkBinaryArmModel γ δ (by omega)
  have hC : C ⊆ V(G.graph) := singleton_subset_iff.mpr G.root.property
  have hCC : GraphConnected (G.graph.induce C) := by
    refine ⟨⟨none,rfl⟩,?_⟩
    intro x hx y hy
    have hx' : x = none := hx
    have hy' : y = none := hy
    subst x
    subst y
    exact .refl
  have hDis : ∀ bit, Disjoint C V((B bit).graph) := by
    intro bit
    apply Set.disjoint_left.mpr
    intro x hx hxB
    have hxnone : x = none := hx
    subst x
    cases bit
    · obtain ⟨v,hv⟩ := hxB
      cases hv
    · obtain ⟨v,hv⟩ := hxB
      cases hv
  have hBD : Pairwise fun a b ↦ Disjoint V((B a).graph) V((B b).graph) := by
    intro a b hab
    have h := (rootedFork_root_binary_disjoint_segment (γ := γ) (by omega)
      2 (by decide) 0 (by omega)).mono_left
        (rootedForkBinaryArm_le_root_piece γ δ (by omega)).vertexSet_mono
    cases a <;> cases b
    · exact False.elim (hab rfl)
    · exact h.symm
    · exact h
    · exact False.elim (hab rfl)
  have hEdge : ∀ bit, F.graph.Adj none (B bit).root.val := by
    intro bit
    refine ⟨s(none,(B bit).root.val),rfl,?_⟩
    cases bit <;> rfl
  have hJoin : ∀ bit, ∃ e x, x ∈ C ∧ G.graph.IsLink e x (B bit).root.val := by
    intro bit
    obtain ⟨e,he⟩ := hEdge bit
    exact ⟨e,none,rfl,he,G.root.property,(hBG bit).vertexSet_mono (B bit).root.property⟩
  exact rootedBinaryTreeModelOfTwoArms G C hC hCC rfl B hBG MB hDis hBD hJoin

/-- Later comb intervals avoid the entire root support in the packing. -/
theorem forkPackingRootSet_disjoint_segment {γ δ m offset : ℕ} (hδ : 3 ≤ δ)
    (hm : 0 < m) (hbound : offset + m ≤ δ - 1) (hgap : 2 ≤ offset) :
    Disjoint (forkPackingRootSet γ δ hδ)
      V((rootedForkCombSegment γ δ (by omega) m hm offset hbound).graph) :=
  (rootedFork_root_binary_disjoint_segment (γ := γ) (by omega) m hm offset hbound).union_left
    (forkCombSegment_ranges_disjoint (γ := γ) (δ := δ) (m := 2) (offset := 0)
      (by omega) hbound hgap)

end GraphMinor.GM01
