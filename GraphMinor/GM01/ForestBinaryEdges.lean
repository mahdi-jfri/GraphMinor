module

public import GraphMinor.GM01.ForestBinaryAddresses
public import GraphMinor.GM01.BinaryTrees
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Joining the retained grandchild subtrees

The contraction proving Graph Minors I, (3.3), page 51, joins each
retained grandchild to its parent in the contracted central piece.
Inside each retained subtree, adding a first bit is exactly the
binary-tree parent edge. These lemmas verify both kinds of edge.
-/

public section

namespace GraphMinor.GM01

/-- An arm vertex of `Y` fits in the corresponding grandchild subtree
of the binary tree one level taller. -/
theorem forestBinaryAddress_mem {lam : ℕ} {p : Fin 3 × List Bool}
    (hp : p.2.length + 1 ≤ lam) :
    forestBinaryAddress p ∈ (binaryTree (lam + 1)).verts := by
  change (forestBinaryAddress p).length ≤ lam + 1
  rw [forestBinaryAddress_length]
  omega

/-- Parent edges within an arm survive in its grandchild subtree. -/
theorem forestBinaryAddress_parent_adj {lam : ℕ} (i : Fin 3) (word : List Bool)
    (bit : Bool) (hw : (bit :: word).length + 1 ≤ lam) :
    (binaryTree (lam + 1)).Adj (forestBinaryAddress (i, word))
      (forestBinaryAddress (i, bit :: word)) := by
  refine ⟨forestBinaryAddress_mem (by change word.length + 1 ≤ lam; simp only [List.length_cons] at hw; omega),
    forestBinaryAddress_mem hw, Or.inl ⟨bit, rfl⟩⟩

/-- Every chosen grandchild has its parent in the three-vertex
central branch that will be contracted. -/
theorem forestBinarySuffix_adj_centre {lam : ℕ} (hlam : 1 ≤ lam) (i : Fin 3) :
    ∃ x ∈ (binaryTree 1).verts,
      (binaryTree (lam + 1)).Adj x (forestBinarySuffix i) := by
  fin_cases i
  · refine ⟨[false], by change 1 ≤ 1; exact le_rfl, ?_⟩
    exact ⟨by change 1 ≤ lam + 1; omega, by change 2 ≤ lam + 1; omega,
      Or.inl ⟨false, rfl⟩⟩
  · refine ⟨[true], by change 1 ≤ 1; exact le_rfl, ?_⟩
    exact ⟨by change 1 ≤ lam + 1; omega, by change 2 ≤ lam + 1; omega,
      Or.inl ⟨false, rfl⟩⟩
  · refine ⟨[false], by change 1 ≤ 1; exact le_rfl, ?_⟩
    exact ⟨by change 1 ≤ lam + 1; omega, by change 2 ≤ lam + 1; omega,
      Or.inl ⟨true, rfl⟩⟩

end GraphMinor.GM01
