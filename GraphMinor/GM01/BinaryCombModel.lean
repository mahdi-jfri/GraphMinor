module

public import GraphMinor.GM01.BinaryCombLocations
public import GraphMinor.GM01.RootedBranchModels
import GraphMinor.GM01.PathCombTrees
import GraphMinor.GM01.RootedEmbeddings
import GraphMinor.GM01.Basic

/-!
# The binary tree minor in two consecutive comb cells

For the skipped-block construction in Graph Minors I, (4.1), page 55,
contract the two spine vertices to the root of a binary tree. Every
nonroot binary vertex is a singleton in the copy selected by its last
bit. Parent edges at the root become the two attachment edges, and all
other parent edges stay inside their binary copy. This gives the actual
rooted model, including when the binary tree has depth zero.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

private def binaryCombBranch (γ : ℕ) (v : (binaryTree γ).verts) : Set (PathCombVertex 2) :=
  if h : v.val = [] then (pathComb 0 2).verts else {binaryCombLocation v.val h}

private theorem binaryCombBranch_subset (γ : ℕ) (v : (binaryTree γ).verts) :
    binaryCombBranch γ v ⊆ (pathComb γ 2).verts := by
  by_cases hv : v.val = []
  · simp only [binaryCombBranch, hv, ↓reduceDIte]
    exact (pathComb_mono (Nat.zero_le γ)).1
  · simp only [binaryCombBranch, hv, ↓reduceDIte]
    exact singleton_subset_iff.mpr (binaryCombLocation_mem hv v.property)

private theorem binaryCombBranch_disjoint (γ : ℕ) :
    Pairwise fun u v : (binaryTree γ).verts ↦ Disjoint (binaryCombBranch γ u) (binaryCombBranch γ v) := by
  intro u v huv
  by_cases hu : u.val = []
  · have hv : v.val ≠ [] := fun hv ↦ huv (Subtype.ext (hu.trans hv.symm))
    simp only [binaryCombBranch, hu, hv, ↓reduceDIte]
    apply disjoint_singleton_right.mpr
    rw [pathComb_zero_verts]
    rintro ⟨i, hi⟩
    cases hi
  · by_cases hv : v.val = []
    · simp only [binaryCombBranch, hu, hv, ↓reduceDIte]
      apply disjoint_singleton_left.mpr
      rw [pathComb_zero_verts]
      rintro ⟨i, hi⟩
      cases hi
    · simp only [binaryCombBranch, hu, hv, ↓reduceDIte]
      apply disjoint_singleton.mpr
      exact fun heq ↦ huv (Subtype.ext (binaryCombLocation_injective hu hv heq))

private theorem binaryCombBranch_connected (γ : ℕ) (v : (binaryTree γ).verts) :
    GraphConnected ((toGraph (pathComb γ 2)).induce (binaryCombBranch γ v)) := by
  by_cases hv : v.val = []
  · simp only [binaryCombBranch, hv, ↓reduceDIte]
    have hK := (graphConnected_toGraph_iff (pathComb 0 2)).mpr (pathComb_connected (by decide))
    have hle := toGraph_mono (pathComb_mono (γ' := γ) (δ := 2) (Nat.zero_le γ))
    refine ⟨hK.1, ?_⟩
    intro x hx y hy
    apply Relation.ReflTransGen.mono ?_ x y (hK.2 x hx y hy)
    intro a b hab
    obtain ⟨e, he⟩ := hab
    exact ⟨e, he.mono hle, he.left_mem, he.right_mem⟩
  · simp only [binaryCombBranch, hv, ↓reduceDIte]
    refine ⟨⟨binaryCombLocation v.val hv, rfl⟩, ?_⟩
    intro x hx y hy
    have hx' : x = binaryCombLocation v.val hv := hx
    have hy' : y = binaryCombLocation v.val hv := hy
    subst x
    subst y
    exact .refl

private theorem binaryCombBranch_parent_edge (γ : ℕ) (u v : (binaryTree γ).verts)
    (bit : Bool) (hv : v.val = bit :: u.val) :
    ∃ e x, x ∈ binaryCombBranch γ u ∧ ∃ y, y ∈ binaryCombBranch γ v ∧
      (toGraph (pathComb γ 2)).IsLink e x y := by
  have hvne : v.val ≠ [] := by rw [hv]; exact List.cons_ne_nil _ _
  by_cases hu : u.val = []
  · have hvbit : v.val = [bit] := by rw [hv, hu]
    have hγ : 0 < γ := by
      have hw := v.property
      change v.val.length ≤ γ at hw
      rw [hvbit] at hw
      simp only [List.length_singleton] at hw
      omega
    let x : PathCombVertex 2 := Sum.inl (binaryCombIndex bit)
    let y := binaryCombLocation v.val hvne
    have hy : y = Sum.inr (binaryCombIndex bit, []) := by
      dsimp only [y]
      simpa only [hvbit] using binaryCombLocation_singleton bit
    refine ⟨s(x,y), x, ?_, y, ?_, ?_⟩
    · simp only [binaryCombBranch, hu, ↓reduceDIte]
      exact pathComb_spine_mem 0 2 _
    · simp only [binaryCombBranch, hvne, ↓reduceDIte]
      exact mem_singleton _
    · refine ⟨rfl, ?_⟩
      rw [hy]
      exact pathComb_attachment_adj hγ _
  · let x := binaryCombLocation u.val hu
    let y := binaryCombLocation v.val hvne
    have hxmem := binaryCombLocation_mem hu u.property
    have hymem := binaryCombLocation_mem hvne v.property
    change x ∈ (pathComb γ 2).verts at hxmem
    change y ∈ (pathComb γ 2).verts at hymem
    have hy : y = Sum.inr (binaryCombIndex (u.val.getLast hu), bit :: u.val.dropLast) := by
      dsimp only [y]
      simpa only [hv] using binaryCombLocation_cons bit u.val hu
    refine ⟨s(x,y), x, ?_, y, ?_, ?_⟩
    · simp only [binaryCombBranch, hu, ↓reduceDIte]
      exact mem_singleton _
    · simp only [binaryCombBranch, hvne, ↓reduceDIte]
      exact mem_singleton _
    · refine ⟨rfl, ?_⟩
      rw [hy] at hymem ⊢
      exact ⟨rfl, hxmem, hymem, Or.inl ⟨bit, rfl⟩⟩

/-- The same contraction works with either spine vertex as target root:
both belong to the whole-spine root branch. In GM01 (4.9), page 58,
this roots the binary arm at the last spine vertex of the first end. -/
noncomputable def binaryTree_model_in_two_cell_comb_at (γ : ℕ) (i : Fin 2) :
    RootedMinorModel (binaryRootedTree γ) (⟨toGraph (pathComb γ 2), ⟨Sum.inl i, pathComb_spine_mem γ 2 i⟩⟩ :
      RootedGraph (PathCombVertex 2) (Sym2 (PathCombVertex 2))) := by
  let S := (binaryTree γ).coe
  let r : (binaryTree γ).verts := (binaryRootedTree γ).root
  let M := rootedModelOfBranchSets S (⟨toGraph (pathComb γ 2), ⟨Sum.inl i, pathComb_spine_mem γ 2 i⟩⟩ :
      RootedGraph (PathCombVertex 2) (Sym2 (PathCombVertex 2))) (binaryCombBranch γ)
    (binaryCombBranch_subset γ) (binaryCombBranch_disjoint γ) (binaryCombBranch_connected γ)
    (by
      intro u v huv
      rcases huv.2.2 with ⟨bit, hv⟩ | ⟨bit, hu⟩
      · exact binaryCombBranch_parent_edge γ u v bit hv
      · obtain ⟨e, y, hy, x, hx, hyx⟩ := binaryCombBranch_parent_edge γ v u bit hu
        exact ⟨e, x, hx, y, hy, hyx.symm⟩) r
    (by exact pathComb_spine_mem 0 2 _)
  let e := subgraphSimpleGraphIso (binaryTree γ)
  let e' : GraphMinor.Iso (toGraph (binaryTree γ)) (Graph.ofSimpleGraph S) :=
    { vertexEquiv := e.vertexEquiv.symm
      edgeEquiv := e.edgeEquiv.symm
      isLink_iff := fun edge x y ↦ by
        simpa only [Equiv.apply_symm_apply] using
          (e.isLink_iff (e.edgeEquiv.symm edge) (e.vertexEquiv.symm x)
            (e.vertexEquiv.symm y)).symm }
  exact M.comapSource e' rfl

/-- The rooted binary tree `H_γ` is a rooted minor of the two-cell comb
`P(γ,2)`, rooted at its first spine vertex. The root branch is the whole
spine, and all other branches are the specified singletons. This is the
binary-tree construction for the skipped block in GM01 (4.1), page 55. -/
noncomputable def binaryTree_model_in_two_cell_comb (γ : ℕ) :
    RootedMinorModel (binaryRootedTree γ) (rootedPathComb γ 2 (by decide)) := by
  exact binaryTree_model_in_two_cell_comb_at γ 0

end GraphMinor.GM01
