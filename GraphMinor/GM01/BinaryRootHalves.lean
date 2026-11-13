module

public import GraphMinor.GM01.BinaryTrees
import GraphMinor.GM01.Basic

/-!
# The connected root half of a binary tree

The half contracted in Graph Minors I, (5.1), pages 60–61, includes
the binary root and all words with one chosen last bit. Parent steps
stay in this set, so it is connected. The other last bit supplies
the binary arm that is retained. This describes the source half
before transferring its contraction through the rooted model.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The binary root together with the half selected by a last bit. -/
def binaryRootHalf (γ : ℕ) (bit : Bool) : Set (List Bool) :=
  {word | word ∈ (binaryTree γ).verts ∧ (word = [] ∨ ∃ stem, word = stem ++ [bit])}

/-- The binary root lies in either chosen root half. -/
theorem binaryRootHalf_root_mem (γ : ℕ) (bit : Bool) : [] ∈ binaryRootHalf γ bit :=
  ⟨binaryTree_root_mem γ,Or.inl rfl⟩

/-- Removing the first bit stays in a chosen root half. -/
theorem binaryRootHalf_tail_mem {γ : ℕ} {bit head : Bool} {word : List Bool}
    (hw : head :: word ∈ binaryRootHalf γ bit) : word ∈ binaryRootHalf γ bit := by
  refine ⟨?_,?_⟩
  · have hlen := hw.1
    change (head :: word).length ≤ γ at hlen
    change word.length ≤ γ
    simp only [List.length_cons] at hlen
    omega
  · rcases hw.2 with heq | ⟨stem,heq⟩
    · exact False.elim (List.cons_ne_nil _ _ heq)
    · cases stem with
      | nil => exact Or.inl (List.cons.inj heq).2
      | cons b stem => exact Or.inr ⟨stem,(List.cons.inj heq).2⟩

/-- Parent paths connect every vertex of the root half to the root. -/
theorem binaryRootHalf_reachable_root {γ : ℕ} {bit : Bool} {word : List Bool}
    (hw : word ∈ binaryRootHalf γ bit) :
    Relation.ReflTransGen ((binaryRootedTree γ).graph.induce (binaryRootHalf γ bit)).Adj word [] := by
  induction word with
  | nil => exact .refl
  | cons head word ih =>
    have htail := binaryRootHalf_tail_mem hw
    have hadj : (binaryTree γ).Adj (head :: word) word := ⟨hw.1,htail.1,Or.inr ⟨head,rfl⟩⟩
    have hedge : ((binaryRootedTree γ).graph.induce (binaryRootHalf γ bit)).Adj
        (head :: word) word := by
      obtain ⟨e,he⟩ := (adj_toGraph (binaryTree γ) _ _).mpr hadj
      exact ⟨e,he,hw,htail⟩
    exact (Relation.ReflTransGen.single hedge).trans (ih htail)

/-- The half contracted into the new spine root in GM01 (5.1) is
connected, because every parent path stays within it. -/
theorem binaryRootHalf_connected (γ : ℕ) (bit : Bool) :
    GraphConnected ((binaryRootedTree γ).graph.induce (binaryRootHalf γ bit)) := by
  refine ⟨⟨[],binaryRootHalf_root_mem γ bit⟩,?_⟩
  intro x hx y hy
  exact (binaryRootHalf_reachable_root hx).trans (Std.Symm.symm _ _ (binaryRootHalf_reachable_root hy))

/-- A nonempty word lies in the root half given by its last bit. -/
theorem binaryRootHalf_mem_of_nonempty {γ : ℕ} (v : (binaryTree γ).verts) (hv : v.val ≠ []) :
    v.val ∈ binaryRootHalf γ (v.val.getLast hv) :=
  ⟨v.property,Or.inr ⟨v.val.dropLast,(List.dropLast_append_getLast hv).symm⟩⟩

end GraphMinor.GM01
