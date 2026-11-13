module

public import GraphMinor.GM01.BinaryChildEmbeddings
public import GraphMinor.GM01.BinaryRootHalves
public import GraphMinor.GM01.PathCombs
import GraphMinor.GM01.OneCellCombModels
import GraphMinor.GM01.Basic

/-!
# Contracting the chosen binary half into one spine cell

For the suitably chosen half in Graph Minors I, (5.1), pages 60–61,
keep the marked attachment vertex in its last-bit half together with
the binary root. Contract this connected set to the new spine vertex.
The opposite half is a rooted `H_(γ−1)` subgraph, joined to the root
by its first edge. The one-cell constructor gives `P(γ,1)`, and its
root branch still contains the marked attachment vertex.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function

/-- Contract one root half and retain the opposite binary arm, keeping
a marked vertex in the new spine branch for GM01 (5.1). -/
theorem exists_one_cell_comb_model_of_binary_root_half {γ : ℕ} (hγ : 0 < γ)
    (bit : Bool) (v : (binaryTree γ).verts) (hv : v.val ∈ binaryRootHalf γ bit) :
    ∃ M : RootedMinorModel (rootedPathComb γ 1 (by decide)) (binaryRootedTree γ),
      v.val ∈ M.branch (rootedPathComb γ 1 (by decide)).root := by
  classical
  let f : (binaryTree (γ - 1)).verts ↪ List Bool :=
    (binaryChildEmbedding hγ (!bit)).trans ⟨Subtype.val,Subtype.val_injective⟩
  let S := range f
  let H := (binaryTree γ).induce S
  have hS : S ⊆ (binaryTree γ).verts := by
    rintro x ⟨u,rfl⟩
    exact (binaryChildEmbedding hγ (!bit) u).property
  have hH : H ≤ binaryTree γ := ⟨hS,fun _ _ h ↦ h.2.2⟩
  have hmem : [!bit] ∈ H.verts := ⟨⟨[],binaryTree_root_mem (γ - 1)⟩,rfl⟩
  let GB : RootedGraph (List Bool) (Sym2 (List Bool)) := ⟨toGraph H,⟨[!bit],hmem⟩⟩
  have hGB : GB.graph ≤ (binaryRootedTree γ).graph := toGraph_mono hH
  have hAdj : ∀ {u w : (binaryTree (γ - 1)).verts},
      (binaryTree (γ - 1)).Adj u.val w.val → H.Adj (f u) (f w) := by
    intro u w huw
    exact ⟨mem_range_self u,mem_range_self w,binaryChildEmbedding_adj hγ (!bit) huw⟩
  let MB : RootedMinorModel (binaryRootedTree (γ - 1)) GB :=
    rootedModelOfSubgraphEmbedding (binaryTree (γ - 1)) H f (fun u ↦ mem_range_self u)
      hAdj (binaryRootedTree (γ - 1)).root
  have hDis : Disjoint (binaryRootHalf γ bit) V(GB.graph) := by
    apply Set.disjoint_left.mpr
    rintro word hw ⟨u,hu⟩
    rcases hw.2 with hnil | ⟨stem,hstem⟩
    · have heq : u.val ++ [!bit] = [] := hu.trans hnil
      have hlen := congrArg List.length heq
      simp only [List.length_append,List.length_singleton,List.length_nil] at hlen
      omega
    · have heq : u.val ++ [!bit] = stem ++ [bit] := hu.trans hstem
      have hlast := congrArg List.getLast? heq
      simp at hlast
  have hJoin : ∃ e x, x ∈ binaryRootHalf γ bit ∧
      (binaryRootedTree γ).graph.IsLink e x GB.root.val := by
    refine ⟨s([],[!bit]),[],binaryRootHalf_root_mem γ bit,rfl,?_⟩
    exact ⟨binaryTree_root_mem γ,hS hmem,Or.inl ⟨!bit,rfl⟩⟩
  let M := rootedOneCellCombModelOfBinaryArm hγ (binaryRootedTree γ) (binaryRootHalf γ bit)
    (fun _ h ↦ h.1) (binaryRootHalf_connected γ bit) (binaryRootHalf_root_mem γ bit) GB hGB MB hDis hJoin
  have hBranch := rootedOneCellCombModelOfBinaryArm_root_branch hγ (binaryRootedTree γ)
    (binaryRootHalf γ bit) (fun _ h ↦ h.1) (binaryRootHalf_connected γ bit)
    (binaryRootHalf_root_mem γ bit) GB hGB MB hDis hJoin
  exact ⟨M,hBranch.symm ▸ hv⟩

/-- A suitably chosen half keeps any specified source vertex in the
one-cell comb's root branch, the half choice in GM01 (5.1), pages 60–61. -/
theorem exists_one_cell_comb_model_marking_binary_vertex {γ : ℕ} (hγ : 0 < γ)
    (v : (binaryTree γ).verts) :
    ∃ M : RootedMinorModel (rootedPathComb γ 1 (by decide)) (binaryRootedTree γ),
      v.val ∈ M.branch (rootedPathComb γ 1 (by decide)).root := by
  by_cases hv : v.val = []
  · apply exists_one_cell_comb_model_of_binary_root_half hγ false v
    exact ⟨v.property,Or.inl hv⟩
  · exact exists_one_cell_comb_model_of_binary_root_half hγ (v.val.getLast hv) v
      (binaryRootHalf_mem_of_nonempty v hv)

end GraphMinor.GM01
