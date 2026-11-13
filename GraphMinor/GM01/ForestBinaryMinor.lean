module

public import GraphMinor.GM01.ForestTrees
public import GraphMinor.GM01.BinaryTrees
import GraphMinor.GM01.ForestBinaryEdges
import GraphMinor.GM01.Basic
import Lean.Elab.Tactic.Omega

/-!
# Contracting a binary tree to the three-branch tree

Graph Minors I, (3.3), page 51, contracts the binary root and its two
children to the centre of `Y`. Three retained grandchild subtrees
supply the three branches, and the fourth is deleted. The centre is
a connected three-vertex branch, and every other branch is a singleton.
-/

public section

namespace GraphMinor.GM01

open Set SimpleGraph

private def forestBinaryBranch : ForestTreeVertex →
    (⊤ : SimpleGraph (List Bool)).Subgraph
  | none => binaryTree 1
  | some p => (⊤ : SimpleGraph (List Bool)).singletonSubgraph (forestBinaryAddress p)

private theorem forestBinaryBranch_verts (v : ForestTreeVertex) :
    (forestBinaryBranch v).verts = match v with
      | none => (binaryTree 1).verts
      | some p => {forestBinaryAddress p} := by
  cases v <;> rfl

/-- Graph Minors I, (3.3), page 51: "For any $\lambda \ge 1$,
$\mathbf{Y}_\lambda$ is isomorphic to a minor of $\mathbf{H}_{\lambda+1}$."
Contract the first two binary levels to the centre and retain three
of the four grandchild subtrees. -/
theorem theorem_3_3_proof (lam : ℕ) (hlam : 1 ≤ lam) :
    IsIsoMinor (forestTreeGraph lam) (toGraph (binaryTree (lam + 1))) := by
  have hParent : ∀ v, v ≠ none → v ∈ (forestTree lam).verts →
      ∃ x ∈ (forestBinaryBranch (forestTreeParent v)).verts,
        ∃ y ∈ (forestBinaryBranch v).verts, (binaryTree (lam + 1)).Adj x y := by
    intro v hv hmem
    cases v with
    | none => exact False.elim (hv rfl)
    | some p =>
      rcases p with ⟨i, word⟩
      cases word with
      | nil =>
        obtain ⟨x, hx, he⟩ := forestBinarySuffix_adj_centre hlam i
        exact ⟨x, hx, forestBinarySuffix i, rfl, he⟩
      | cons bit word =>
        exact ⟨forestBinaryAddress (i, word), rfl,
          forestBinaryAddress (i, bit :: word), rfl,
          forestBinaryAddress_parent_adj i word bit hmem⟩
  apply isIsoMinor_toGraph_of_connected_subgraphs (forestTree_vertices_finite lam)
    (binaryTree_vertices_finite (lam + 1)) forestBinaryBranch
  · intro v hv
    cases v with
    | none => exact binaryTree_mono (by omega)
    | some p =>
      apply (singletonSubgraph_le_iff _ _).mpr
      exact forestBinaryAddress_mem hv
  · intro v _
    cases v with
    | none => exact binaryTree_connected 1
    | some p => exact Subgraph.singletonSubgraph_connected
  · intro v _ w _ hne
    rw [forestBinaryBranch_verts, forestBinaryBranch_verts]
    have hnot : ∀ p, forestBinaryAddress p ∉ (binaryTree 1).verts := by
      intro p hp
      change (forestBinaryAddress p).length ≤ 1 at hp
      rw [forestBinaryAddress_length] at hp
      omega
    cases v with
    | none =>
      cases w with
      | none => exact False.elim (hne rfl)
      | some p => exact disjoint_singleton_right.mpr (hnot p)
    | some p =>
      cases w with
      | none => exact disjoint_singleton_left.mpr (hnot p)
      | some q =>
        exact disjoint_singleton.mpr (fun h ↦ hne (congrArg some (forestBinaryAddress_injective h)))
  · intro v w h
    rcases h.2.2 with ⟨hwne, hp⟩ | ⟨hvne, hp⟩
    · obtain ⟨x, hx, y, hy, he⟩ := hParent w hwne h.2.1
      rw [hp] at hx
      exact ⟨x, hx, y, hy, he⟩
    · obtain ⟨x, hx, y, hy, he⟩ := hParent v hvne h.1
      rw [hp] at hx
      exact ⟨y, hy, x, hx, he.symm⟩

end GraphMinor.GM01
