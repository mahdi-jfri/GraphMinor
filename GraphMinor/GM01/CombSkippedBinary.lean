module

public import GraphMinor.GM01.CombSkippedPaths
public import GraphMinor.GM01.BinaryCombModel
public import GraphMinor.GM01.RootedSubdivisionRestriction
public import GraphMinor.GM01.RootedModelComposition
import GraphMinor.GM01.SubgraphIso
import Lean.Elab.Tactic.Omega

/-!
# The rooted binary tree in the skipped block

For Graph Minors I, (4.1), page 55, retain the two-cell subdivision in the
skipped block, preserving its first spine centre as root. Compose its
rooted model with the binary-tree contraction of the two source cells.
The target support is still exactly the selected centres and replacing
paths, so the boundary attachment can later be kept disjoint from every
other model branch.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The skipped block contains the required rooted binary tree on the
support of its selected two-cell subdivision. The first source spine
centre is the specified target root. -/
theorem exists_skipped_block_binary_model {α β : Type*} {γ L n : ℕ}
    (hL : 0 < L) (htail : 2 * n ≤ L) {G N R : Graph α β} (hN : N ≤ G)
    {c : (pathComb γ L).verts → α} (hc : Injective c) (hcentres : ∀ v, c v ∈ V(N))
    (P : (pathComb γ L).coe.edgeSet → Graph α β) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (root : α) (hR : IsGraphPathWithEnds G R root (c (rootedPathComb γ L hL).root))
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (j : Fin n) (hj0 : 0 < j.val) (hjn : j.val + 1 < n) :
    ∃ K : Graph α β, K ≤ N ∧
      K ≤ N.induce (combBlock hL (subgraphUnion G N R) c j) ∧
      V(K) = range (fun v : (pathComb γ 2).verts ↦
        c (combShiftEmbedding (2 * j.val) (by omega : 2 * j.val + 2 ≤ L) v)) ∪
        ⋃ e : (pathComb γ 2).coe.edgeSet,
          V(P (combShiftEdges (2 * j.val) (by omega : 2 * j.val + 2 ≤ L) e)) ∧
      ∃ hroot : c (combShiftEmbedding (2 * j.val) (by omega : 2 * j.val + 2 ≤ L)
          (rootedPathComb γ 2 (by decide)).root) ∈ V(K),
        HasRootedMinor (binaryRootedTree γ)
          (⟨K, ⟨c (combShiftEmbedding (2 * j.val) (by omega : 2 * j.val + 2 ≤ L)
            (rootedPathComb γ 2 (by decide)).root), hroot⟩⟩ : RootedGraph α β) := by
  let : Finite (pathComb γ 2).verts := (pathComb_vertices_finite γ 2).to_subtype
  have hbound : 2 * j.val + 2 ≤ L := by omega
  let f := combShiftEmbedding (γ := γ) (2 * j.val) hbound
  have hf : ∀ {a b : (pathComb γ 2).verts}, (pathComb γ 2).coe.Adj a b →
      (pathComb γ L).coe.Adj (f a) (f b) := combShiftEmbedding_adj _ hbound
  let D := combBlock hL (subgraphUnion G N R) c j
  obtain ⟨hCD, hPD⟩ := comb_two_cells_in_block hL htail hN hc hcentres P hE hPaths
    (fun e f hne ↦ (hInter e f hne).1) root hR hmeet j hj0 hjn
  let r := (rootedPathComb γ 2 (by decide)).root
  obtain ⟨K, hK, hV, hroot, ⟨M⟩⟩ := exists_supported_rooted_subdivision_restriction
    f hf c hc D (fun v ↦ ⟨hcentres (f v), hCD v⟩) P hPaths hInter hPD r
  let e := subgraphSimpleGraphIso (pathComb γ 2)
  let e' : GraphMinor.Iso (toGraph (pathComb γ 2)) (Graph.ofSimpleGraph (pathComb γ 2).coe) :=
    { vertexEquiv := e.vertexEquiv.symm
      edgeEquiv := e.edgeEquiv.symm
      isLink_iff := fun edge x y ↦ by
        simpa only [Equiv.apply_symm_apply] using
          (e.isLink_iff (e.edgeEquiv.symm edge) (e.vertexEquiv.symm x)
            (e.vertexEquiv.symm y)).symm }
  have hsmall : HasRootedMinor (rootedPathComb γ 2 (by decide))
      (⟨K, ⟨c (f r), hroot⟩⟩ : RootedGraph α β) := ⟨M.comapSource e' rfl⟩
  have hKV : V(K) ⊆ V(N) := by
    rw [hV]
    intro x hx
    rcases hx with ⟨v, rfl⟩ | hx
    · exact hcentres (f v)
    · obtain ⟨edge, hx⟩ := mem_iUnion.mp hx
      obtain ⟨_, _, _, hPath, _⟩ := hPaths (subdivisionEmbeddingEdges f hf edge)
      exact hPath.le.vertexSet_mono hx
  have hKN : K ≤ N := by
    refine ⟨hKV, ?_⟩
    intro edge x y he
    exact (he.mono hK).1
  exact ⟨K, hKN, hK, hV, hroot, HasRootedMinor.trans ⟨binaryTree_model_in_two_cell_comb γ⟩ hsmall⟩

end GraphMinor.GM01
