module

public import GraphMinor.GM01.BinaryForestEmbedding
public import GraphMinor.GM01.ForestTreeArms
import GraphMinor.GM01.RootedPathAttachment
import GraphMinor.GM01.BinaryCombLocations
import Mathlib.Data.Fin.Embedding

/-!
# Rooting the binary minor at an arbitrary three-branch-tree vertex

For the contraction on page 60 of Graph Minors I, root `Y_γ` at the
attachment vertex. Use the two branches not containing that vertex
for the binary tree, and join the attachment to the centre through
the third branch. That path misses every nonroot model branch.
Adding it to the root branch gives a rooted `H_γ` model, including
height zero with the one-vertex convention for `Y_0`.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

/-- Use the third arm as the root path, disjoint from the nonroot
branches of the binary embedding, in the GM01 page-60 contraction. -/
theorem rootedBinaryTree_of_forestTreeArm {γ : ℕ} {k : Fin 3}
    (e : Bool ↪ Fin 3) (he : ∀ bit, e bit ≠ k)
    (v : (forestTree γ).verts) (hv : v.val ∈ forestTreeArm γ k) :
    HasRootedMinor (binaryRootedTree γ)
      (⟨forestTreeGraph γ, v⟩ : RootedGraph ForestTreeVertex (Sym2 ForestTreeVertex)) := by
  let M := binaryTreeModelInForest γ e
  obtain ⟨R,hR,hRV⟩ := exists_path_in_forestTreeArm hv
  have hDisj : ∀ w : (binaryTree γ).verts, w ≠ (binaryRootedTree γ).root →
      Disjoint (M.branch w) V(R) := by
    intro w hw
    apply Set.disjoint_left.mpr
    intro x hx hxR
    rw [binaryTreeModelInForest_branch] at hx
    have hxEq : x = binaryForestVertex e w.val := hx
    subst x
    have hword : w.val ≠ [] := fun h ↦ hw (Subtype.ext h)
    have hArm := (hRV hxR).2
    simp only [binaryForestVertex, hword, ↓reduceDIte] at hArm
    rcases hArm with hnone | ⟨word,heq⟩
    · exact Option.some_ne_none _ hnone
    · exact he _ (congrArg Prod.fst (Option.some.inj heq))
  let L := M.attachRootPathOfDisjointBranches le_rfl v.val hR hDisj
  exact ⟨L.mono (subgraphUnion_le le_rfl hR.le) rfl⟩

/-- Rooting `Y_γ` at any vertex still gives the rooted binary minor
needed for each selected attachment in GM01, page 60. -/
theorem rootedBinaryTree_of_forestTree {γ : ℕ} (v : (forestTree γ).verts) :
    HasRootedMinor (binaryRootedTree γ)
      (⟨forestTreeGraph γ, v⟩ : RootedGraph ForestTreeVertex (Sym2 ForestTreeVertex)) := by
  let k : Fin 3 := match v.val with | none => 0 | some p => p.1
  let e : Bool ↪ Fin 3 :=
    ⟨fun b ↦ k.succAbove (binaryCombIndex b),
      (Fin.succAboveEmb k).injective.comp binaryCombIndex_injective⟩
  have he : ∀ bit, e bit ≠ k := fun bit ↦ Fin.succAbove_ne k (binaryCombIndex bit)
  have hv : v.val ∈ forestTreeArm γ k := by
    refine ⟨v.property, ?_⟩
    rcases v with ⟨value,hvalue⟩
    cases value with
    | none => exact Or.inl rfl
    | some p => exact Or.inr ⟨p.2,rfl⟩
  exact rootedBinaryTree_of_forestTreeArm e he v hv

end GraphMinor.GM01
