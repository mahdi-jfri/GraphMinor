module

public import GraphMinor.GM01.BinaryTrees
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pi

/-!
# Leaf chains in the binary tree

For the root-to-leaf cover used in Graph Minors I, page 60, label
leaves by binary words of the full height. There are exactly `2^γ`
such words. Every vertex is a suffix of one of them, and both ends
of every edge are suffixes of one common leaf. These are the source
chains whose replacing paths cover the binary subdivision.
-/

public section

namespace GraphMinor.GM01

open Set

/-- The binary tree of height `γ` has `2^γ` full-height words,
the leaves indexing the cover on page 60 of GM01. -/
theorem binaryTree_full_height_ncard (γ : ℕ) :
    {word : List Bool | word.length = γ}.ncard = 2 ^ γ := by
  have hRange : {word : List Bool | word.length = γ} =
      range (List.ofFn : (Fin γ → Bool) → List Bool) := by
    ext word
    constructor
    · intro h
      change word.length = γ at h
      subst γ
      exact ⟨word.get, List.ofFn_get word⟩
    · rintro ⟨f, rfl⟩
      exact List.length_ofFn
  rw [hRange, ncard_range_of_injective List.ofFn_injective]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Adding zero bits at the far end of a root chain extends each
binary-tree vertex to a full-height leaf, GM01 page 60. -/
theorem binaryTree_vertex_suffix_leaf {γ : ℕ} {word : List Bool}
    (hw : word ∈ (binaryTree γ).verts) :
    ∃ leaf : List Bool, leaf.length = γ ∧ word <:+ leaf := by
  refine ⟨List.replicate (γ - word.length) false ++ word, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]
    exact Nat.sub_add_cancel hw
  · exact ⟨_, rfl⟩

/-- Every source edge belongs to the chain of suffixes of one leaf.
Thus lifting all leaf chains also covers all replacing edge paths. -/
theorem binaryTree_edge_suffix_leaf {γ : ℕ} {a b : List Bool}
    (hab : (binaryTree γ).Adj a b) :
    ∃ leaf : List Bool, leaf.length = γ ∧ a <:+ leaf ∧ b <:+ leaf := by
  rcases hab.2.2 with ⟨bit, rfl⟩ | ⟨bit, rfl⟩
  · obtain ⟨leaf, hlen, hs⟩ := binaryTree_vertex_suffix_leaf hab.2.1
    exact ⟨leaf, hlen, (show a <:+ bit :: a from ⟨[bit], rfl⟩).trans hs, hs⟩
  · obtain ⟨leaf, hlen, hs⟩ := binaryTree_vertex_suffix_leaf hab.1
    exact ⟨leaf, hlen, hs, (show b <:+ bit :: b from ⟨[bit], rfl⟩).trans hs⟩

end GraphMinor.GM01
