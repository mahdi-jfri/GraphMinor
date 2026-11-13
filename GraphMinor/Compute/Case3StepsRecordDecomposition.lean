module

public import GraphMinor.Compute.Case3StepsBranchRecord
import GraphMinor.Compute.Bridge13

/-!
# Reading a retained interior decomposition

Renaming preserves the full directed-copy count. For at most one edge,
the case (iii) conclusion uses the paper's small-edge convention. For at
least two edges, the copied parent and leaf lists give the decomposition
of the decoded member, with the returned width bound.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

/-- The graph decoded from a record has the compact member's full edge count. -/
theorem case3BranchRecord_toSubgraph_ncard {n : ℕ} (G : MultiDigraph n)
    (f : ℕ ↪ ℕ) (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ)
    (G₀ : Graph ℕ (ℕ × ℕ × ℕ))
    (hsub : relabelGraph f g G.toGMDigraph.toGraph ≤ G₀) :
    E((case3BranchRecord G f g code).toSubgraph G₀).ncard = G.numEdges := by
  rw [case3BranchRecord_toSubgraph G f g code G₀ hsub,
    ncard_edgeSet_relabelGraph f g]
  exact G.ncard_edgeSet_toGMDigraph

/-- Every valid retained code gives exactly the small-edge alternative or
the width-bounded decomposition required by output (a). -/
theorem case3BranchRecord_toSubgraph_decomposition {n B : ℕ} (G : MultiDigraph n)
    (f : ℕ ↪ ℕ) (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ)
    (hcode : IsValidBranchDecompCode B G code)
    (G₀ : Graph ℕ (ℕ × ℕ × ℕ))
    (hsub : relabelGraph f g G.toGMDigraph.toGraph ≤ G₀) :
    let r := case3BranchRecord G f g code
    let bd := r.toBranchDecomp
    E(r.toSubgraph G₀).ncard ≤ 1 ∨
      (GM13.IsGraphBranchDecomposition (r.toSubgraph G₀) bd.2.1 bd.2.2 ∧
        GM13.graphBranchDecompWidth (r.toSubgraph G₀) bd.2.1 bd.2.2 ≤ B) := by
  dsimp only
  by_cases hm : G.numEdges ≤ 1
  · exact Or.inl ((case3BranchRecord_toSubgraph_ncard G f g code G₀ hsub).symm ▸ hm)
  · exact Or.inr (case3BranchRecord_toSubgraph_branchDecomp G f g code hcode (by omega) G₀ hsub)

/-- The frozen decoder returns the retained record's decomposition on its
member graph, so the same width conclusion holds after block lookup. -/
theorem case3ParsedBlock_record_decomposition {n N B : ℕ} (D : MultiDigraph n)
    (f : ℕ ↪ ℕ) (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ)
    (hcode : IsValidBranchDecompCode B D code) (G : MultiDigraph N) (X : Finset (Fin N))
    (p : ParsedCase3Block (G.deleteVertices X) X) (block : List ℕ)
    (hparse : parseCase3Block (G.deleteVertices X) X block = some p)
    (hr : case3BranchRecord D f g code ∈ p.members)
    (hsub : relabelGraph f g D.toGMDigraph.toGraph ≤ delGraph G X) :
    let A := (case3BranchRecord D f g code).toSubgraph (delGraph G X)
    let bd := case3Decoder.branchDecomp N G X block A
    E(A).ncard ≤ 1 ∨
      (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
        GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ B) := by
  dsimp only
  rw [p.branchDecomp_toSubgraph hparse hr]
  exact case3BranchRecord_toSubgraph_decomposition D f g code hcode (delGraph G X) hsub

end GraphMinor.Compute
