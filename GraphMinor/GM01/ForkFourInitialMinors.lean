module

public import GraphMinor.GM01.ForkArmEmbeddings
public import GraphMinor.GM01.OneCellCombInLowerThree
import GraphMinor.GM01.BinaryCombModel
import GraphMinor.GM01.CombJoinModels
import GraphMinor.GM01.RootedModelComposition
import GraphMinor.GM09.Basic

/-!
# The two initial rooted minors of the four-fork

Graph Minors I, Part 3, page 59, uses rooted copies of `P(γ,2)` and
`H_γ` in `Q(γ,4)`. The new root with its binary arm gives the first
cell. The three-cell lower-height arm gives the second cell, by the
proved height-raising contraction. Join them along the fork's comb
edge. Contracting the two-cell spine then gives `H_γ`.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09 GraphMinor.Surface

/-- The rooted minor `P(γ,2)` of `Q(γ,4)` used at the start of GM01
Part 3, page 59, constructed by joining two actual one-cell pieces. -/
theorem rooted_two_cell_comb_minor_of_fork_four {γ : ℕ} (hγ : 0 < γ) :
    HasRootedMinor (rootedPathComb γ 2 (by decide)) (rootedForkGraph γ 4 hγ (by decide)) := by
  let G := rootedForkGraph γ 4 hγ (by decide)
  let G₁ := rootedForkRootBinaryPiece γ 4 (by decide)
  let G₂ := rootedForkCombArm γ 4 (by decide)
  let GB := rootedForkBinaryArm γ 4 (by decide)
  have hG₁ : G₁.graph ≤ G.graph := rootedForkRootBinaryPiece_le γ 4 hγ (by decide)
  have hG₂ : G₂.graph ≤ G.graph := rootedForkCombArm_le γ 4 hγ (by decide)
  have hGB : GB.graph ≤ G₁.graph := rootedForkBinaryArm_le_root_piece γ 4 (by decide)
  have hdis := rootedFork_root_binary_disjoint_comb γ 4 (by decide)
  have hC : ({G₁.root.val} : Set (RootedForkVertex 4)) ⊆ V(G₁.graph) := singleton_subset_iff.mpr G₁.root.property
  have hconn : GraphConnected (G₁.graph.induce {G₁.root.val}) := by
    refine ⟨⟨G₁.root.val, rfl⟩, ?_⟩
    intro x hx y hy
    have hx' : x = G₁.root.val := hx
    have hy' : y = G₁.root.val := hy
    subst x
    subst y
    exact .refl
  have hCdis : Disjoint ({G₁.root.val} : Set (RootedForkVertex 4)) V(GB.graph) := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨v, hv⟩
    have hx' : x = none := hx
    rw [hx'] at hv
    cases hv
  have hjoin : ∃ e x, x ∈ ({G₁.root.val} : Set (RootedForkVertex 4)) ∧
      G₁.graph.IsLink e x GB.root.val := by
    exact ⟨s(G₁.root.val,GB.root.val), G₁.root.val, rfl, rfl,
      Or.inl rfl, Or.inr (mem_range_self (binaryRootedTree (γ - 1)).root), rfl⟩
  let M₁ := rootedOneCellCombModelOfBinaryArm hγ G₁ {G₁.root.val} hC hconn rfl GB hGB
    (rootedForkBinaryArmModel γ 4 (by decide)) hCdis hjoin
  let M₂ : RootedMinorModel (rootedPathComb γ 1 (by decide)) G₂ :=
    (rootedOneCellCombModelInLowerThree hγ).trans (rootedForkCombArmModel γ 4 (by decide))
  have he : G.graph.IsLink s(G₁.root.val,G₂.root.val) G₁.root.val G₂.root.val :=
    ⟨rfl, rootedFork_root_adj_comb γ 4 (by decide)⟩
  let W : GraphWalk G.graph G₁.root.val G₂.root.val :=
    .cons he (.nil (hG₂.vertexSet_mono G₂.root.property))
  obtain ⟨P, hP, hPV, _⟩ := exists_isGraphPathWithEnds_of_walk W
  have hEnds : V(P) ⊆ {G₁.root.val,G₂.root.val} := by
    intro x hx
    simpa only [W, GraphWalk.support, List.mem_cons, List.mem_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.not_mem_nil, or_false] using hPV hx
  have hP₁ : V(P) ∩ V(G₁.graph) = {G₁.root.val} := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases hEnds hx.1 with h | h
      · exact h
      · exact False.elim (Set.disjoint_left.mp hdis hx.2 (h.symm ▸ G₂.root.property))
    · intro x hx
      have hx' : x = G₁.root.val := hx
      subst x
      exact ⟨hP.left_mem, G₁.root.property⟩
  have hP₂ : V(P) ∩ V(G₂.graph) = {G₂.root.val} := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases hEnds hx.1 with h | h
      · exact False.elim (Set.disjoint_left.mp hdis (h.symm ▸ G₁.root.property) hx.2)
      · exact h
    · intro x hx
      have hx' : x = G₂.root.val := hx
      subst x
      exact ⟨hP.right_mem, G₂.root.property⟩
  have hlast : G₁.root.val ∈ M₁.branch (pathCombLastSpine γ 1 (by decide)) := M₁.root_mem
  exact ⟨rootedModelOfCombJoin (by decide : 0 < 1) (by decide : 0 < 1) G G₁ G₂ hG₁ hG₂ rfl hdis
    M₁ M₂ hlast hP hP₁ hP₂⟩

/-- Choose the actual two-cell model from its proved existence. -/
noncomputable def rootedTwoCellCombModelOfForkFour {γ : ℕ} (hγ : 0 < γ) :
    RootedMinorModel (rootedPathComb γ 2 (by decide)) (rootedForkGraph γ 4 hγ (by decide)) :=
  Classical.choice (rooted_two_cell_comb_minor_of_fork_four hγ)

/-- The rooted `H_γ` minor of `Q(γ,4)` used at the start of GM01
Part 3, page 59. Contract the two-cell comb's spine to its binary root. -/
noncomputable def rootedBinaryTreeModelOfForkFour {γ : ℕ} (hγ : 0 < γ) :
    RootedMinorModel (binaryRootedTree γ) (rootedForkGraph γ 4 hγ (by decide)) :=
  (binaryTree_model_in_two_cell_comb γ).trans (rootedTwoCellCombModelOfForkFour hγ)

/-- The rooted binary-tree containment used on page 59 of GM01. -/
theorem rooted_binary_tree_minor_of_fork_four {γ : ℕ} (hγ : 0 < γ) :
    HasRootedMinor (binaryRootedTree γ) (rootedForkGraph γ 4 hγ (by decide)) :=
  ⟨rootedBinaryTreeModelOfForkFour hγ⟩

end GraphMinor.GM01
