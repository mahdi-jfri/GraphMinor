module

public import GraphMinor.GM01.BinaryTrees
public import GraphMinor.GM01.RootedEmbeddings
import Mathlib.Data.List.Basic

/-!
# The two rooted halves of a binary tree

For Graph Minors I, (5.1), pages 60–61, a suitably chosen half of
`B_0` is contracted into the new spine root. Label each source half
by its last bit. Appending that bit embeds `H_(γ−1)` in `H_γ`.
The two image sets are disjoint, and every nonroot vertex belongs
to one of them. Parent edges stay within the chosen half.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set SimpleGraph Function

/-- Append the bit that selects a binary half. -/
def binaryChildEmbedding {γ : ℕ} (hγ : 0 < γ) (bit : Bool) :
    (binaryTree (γ - 1)).verts ↪ (binaryTree γ).verts where
  toFun v := ⟨v.val ++ [bit], by
    change (v.val ++ [bit]).length ≤ γ
    have hv := v.property
    change v.val.length ≤ γ - 1 at hv
    simp only [List.length_append,List.length_singleton]
    omega⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    exact List.append_cancel_right (congrArg Subtype.val h)

/-- Source edges are retained within the selected half. -/
theorem binaryChildEmbedding_adj {γ : ℕ} (hγ : 0 < γ) (bit : Bool)
    {u v : (binaryTree (γ - 1)).verts} (huv : (binaryTree (γ - 1)).coe.Adj u v) :
    (binaryTree γ).coe.Adj (binaryChildEmbedding hγ bit u) (binaryChildEmbedding hγ bit v) := by
  refine ⟨(binaryChildEmbedding hγ bit u).property,(binaryChildEmbedding hγ bit v).property,?_⟩
  rcases huv.2.2 with ⟨b,hv⟩ | ⟨b,hu⟩
  · exact Or.inl ⟨b, by change v.val ++ [bit] = b :: (u.val ++ [bit]); rw [hv]; rfl⟩
  · exact Or.inr ⟨b, by change u.val ++ [bit] = b :: (v.val ++ [bit]); rw [hu]; rfl⟩

/-- Distinct last bits select disjoint binary halves. -/
theorem binaryChildEmbedding_ranges_disjoint {γ : ℕ} (hγ : 0 < γ) {a b : Bool}
    (hab : a ≠ b) : Disjoint (range (binaryChildEmbedding hγ a)) (range (binaryChildEmbedding hγ b)) := by
  apply Set.disjoint_left.mpr
  rintro v ⟨u,rfl⟩ ⟨w,heq⟩
  have hlast := congrArg (fun v : (binaryTree γ).verts ↦ v.val.getLast?) heq
  change (w.val ++ [b]).getLast? = (u.val ++ [a]).getLast? at hlast
  have hba : b = a := by simpa using hlast
  exact hab hba.symm

/-- Every nonroot source vertex lies in the half selected by its last bit. -/
theorem binaryTree_nonroot_mem_child_range {γ : ℕ} (hγ : 0 < γ)
    (v : (binaryTree γ).verts) (hv : v.val ≠ []) :
    v ∈ range (binaryChildEmbedding hγ (v.val.getLast hv)) := by
  have hdrop : v.val.dropLast.length ≤ γ - 1 := by
    have hlen := v.property
    change v.val.length ≤ γ at hlen
    have heq := congrArg List.length (List.dropLast_append_getLast hv)
    simp only [List.length_append,List.length_singleton] at heq
    omega
  exact ⟨⟨v.val.dropLast,hdrop⟩,Subtype.ext (List.dropLast_append_getLast hv)⟩

/-- The source root does not belong to either half. -/
theorem binaryTree_root_not_mem_child_range {γ : ℕ} (hγ : 0 < γ) (bit : Bool) :
    (⟨[],binaryTree_root_mem γ⟩ : (binaryTree γ).verts) ∉ range (binaryChildEmbedding hγ bit) := by
  rintro ⟨v,hv⟩
  have heq := congrArg (fun v : (binaryTree γ).verts ↦ v.val.length) hv
  change (v.val ++ [bit]).length = 0 at heq
  simp only [List.length_append,List.length_singleton] at heq
  omega

end GraphMinor.GM01
