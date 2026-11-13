module

public import GraphMinor.GM01.RootedForks
public import GraphMinor.GM01.RootedEmbeddings
import GraphMinor.GM01.Basic

/-!
# The two copies in a rooted fork

Graph Minors I, page 53, constructs `Q(γ,δ)` from a comb copy, a
binary-tree copy, and a new root joined to both roots. We select the
two actual copies and the piece consisting of the new root and the
binary copy. Their inclusion maps give rooted models, and their
vertex sets prove disjointness for the initial contractions in Part 3.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The comb-copy map in the page-53 definition of `Q(γ,δ)`. -/
def forkCombEmbedding (γ δ : ℕ) : (pathComb (γ - 1) (δ - 1)).verts ↪ RootedForkVertex δ where
  toFun v := some (Sum.inl v.val)
  inj' := fun _ _ h ↦ Subtype.ext (Sum.inl.inj (Option.some.inj h))

/-- The binary-copy map in the page-53 definition of `Q(γ,δ)`. -/
def forkBinaryEmbedding (γ δ : ℕ) : (binaryTree (γ - 1)).verts ↪ RootedForkVertex δ where
  toFun v := some (Sum.inr v.val)
  inj' := fun _ _ h ↦ Subtype.ext (Sum.inr.inj (Option.some.inj h))

/-- The comb copy of the fork, rooted at its original first spine vertex. -/
def rootedForkCombArm (γ δ : ℕ) (hδ : 2 ≤ δ) : RootedGraph (RootedForkVertex δ) (Sym2 (RootedForkVertex δ)) :=
  ⟨toGraph ((rootedFork γ δ hδ).induce (range (forkCombEmbedding γ δ))),
    ⟨forkCombEmbedding γ δ (rootedPathComb (γ - 1) (δ - 1) (by omega)).root,
      mem_range_self _⟩⟩

/-- The binary copy of the fork, rooted at its original empty word. -/
def rootedForkBinaryArm (γ δ : ℕ) (hδ : 2 ≤ δ) : RootedGraph (RootedForkVertex δ) (Sym2 (RootedForkVertex δ)) :=
  ⟨toGraph ((rootedFork γ δ hδ).induce (range (forkBinaryEmbedding γ δ))),
    ⟨forkBinaryEmbedding γ δ (binaryRootedTree (γ - 1)).root, mem_range_self _⟩⟩

/-- The new fork root and its attached binary copy, used as the first
one-cell piece in Part 3, page 59. -/
def rootedForkRootBinaryPiece (γ δ : ℕ) (hδ : 2 ≤ δ) : RootedGraph (RootedForkVertex δ) (Sym2 (RootedForkVertex δ)) :=
  ⟨toGraph ((rootedFork γ δ hδ).induce (insert none (range (forkBinaryEmbedding γ δ)))),
    ⟨none, Or.inl rfl⟩⟩

/-- The inclusion model of the fork's actual comb copy. -/
noncomputable def rootedForkCombArmModel (γ δ : ℕ) (hδ : 2 ≤ δ) :
    RootedMinorModel (rootedPathComb (γ - 1) (δ - 1) (by omega)) (rootedForkCombArm γ δ hδ) :=
  rootedModelOfSubgraphEmbedding (pathComb (γ - 1) (δ - 1))
    ((rootedFork γ δ hδ).induce (range (forkCombEmbedding γ δ))) (forkCombEmbedding γ δ)
    (fun v ↦ mem_range_self v) (fun {u v} huv ↦ ⟨mem_range_self u, mem_range_self v, huv⟩)
    (rootedPathComb (γ - 1) (δ - 1) (by omega)).root

/-- The inclusion model of the fork's actual binary copy. -/
noncomputable def rootedForkBinaryArmModel (γ δ : ℕ) (hδ : 2 ≤ δ) :
    RootedMinorModel (binaryRootedTree (γ - 1)) (rootedForkBinaryArm γ δ hδ) :=
  rootedModelOfSubgraphEmbedding (binaryTree (γ - 1))
    ((rootedFork γ δ hδ).induce (range (forkBinaryEmbedding γ δ))) (forkBinaryEmbedding γ δ)
    (fun v ↦ mem_range_self v) (fun {u v} huv ↦ ⟨mem_range_self u, mem_range_self v, huv⟩)
    (binaryRootedTree (γ - 1)).root

/-- The comb copy is a subgraph of the full fork. -/
theorem rootedForkCombArm_le (γ δ : ℕ) (hγ : 0 < γ) (hδ : 2 ≤ δ) :
    (rootedForkCombArm γ δ hδ).graph ≤ (rootedForkGraph γ δ hγ hδ).graph := by
  apply toGraph_mono
  refine ⟨?_, fun _ _ h ↦ h.2.2⟩
  rintro x ⟨v, rfl⟩
  exact v.property

/-- The root and binary piece is a subgraph of the full fork. -/
theorem rootedForkRootBinaryPiece_le (γ δ : ℕ) (hγ : 0 < γ) (hδ : 2 ≤ δ) :
    (rootedForkRootBinaryPiece γ δ hδ).graph ≤ (rootedForkGraph γ δ hγ hδ).graph := by
  apply toGraph_mono
  refine ⟨?_, fun _ _ h ↦ h.2.2⟩
  rintro x (rfl | ⟨v, rfl⟩)
  · exact True.intro
  · exact v.property

/-- The binary copy lies in the piece containing the new root. -/
theorem rootedForkBinaryArm_le_root_piece (γ δ : ℕ) (hδ : 2 ≤ δ) :
    (rootedForkBinaryArm γ δ hδ).graph ≤ (rootedForkRootBinaryPiece γ δ hδ).graph := by
  apply toGraph_mono
  exact ⟨subset_insert _ _, fun _ _ h ↦ ⟨Or.inr h.1, Or.inr h.2.1, h.2.2⟩⟩

/-- The new root and binary piece is disjoint from the comb copy. -/
theorem rootedFork_root_binary_disjoint_comb (γ δ : ℕ) (hδ : 2 ≤ δ) :
    Disjoint V((rootedForkRootBinaryPiece γ δ hδ).graph) V((rootedForkCombArm γ δ hδ).graph) := by
  apply Set.disjoint_left.mpr
  rintro x (rfl | ⟨v, rfl⟩) ⟨w, hw⟩
  · cases hw
  · cases hw

end GraphMinor.GM01
