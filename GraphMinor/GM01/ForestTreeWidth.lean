module

public import GraphMinor.GM01.Statements
public import GraphMinor.GM01.QuantitativeBounds
import GraphMinor.GM01.ForestGridExclusion
import GraphMinor.GM01.ForestRootedExclusion
import GraphMinor.GM01.RootedWidth
import GraphMinor.GM01.GraphComponents
import GraphMinor.GM01.PathWidthComponents

/-!
# Bounded path-width from excluding the three-branch tree

This is the componentwise proof of Graph Minors I, (3.1), on page 54.
Root each component arbitrarily. Exclusion of the three-branch tree
excludes the rooted three-cell comb. Result (3.5) gives grid exclusion,
so the proved bound (3.7)(i) applies to each component. Concatenate the
component decompositions by (1.4).
-/

public section

namespace GraphMinor.GM01

open Set Graph

universe u v

/-- Graph Minors I, (3.1), page 51: "For $\lambda \ge 1$, odd, there is
a number $w(\lambda)$ such that every graph with no minor isomorphic to
$\mathbf{Y}_\lambda$ has path-with $\le w(\lambda)$."
Follow its proof on page 54 using the now-proved (3.5) and (3.7)(i).
The bound is `p(lam,3)` and every component receives the same bound. -/
theorem theorem_3_1_proof : GM01Theorem31Statement.{u, v} := by
  intro lam hlam hodd
  refine ⟨pathWidthBound lam lam 3, ?_⟩
  intro α β G hV hE hNo
  apply theorem_1_4_proof hV
  intro v
  let C : RootedGraph α β :=
    ⟨G.induce (componentVertices G v), ⟨v.val, mem_componentVertices_self G v⟩⟩
  have hCG : C.graph ≤ G := G.induce_le (fun _ hx ↦ hx.1)
  have hCV : V(C.graph).Finite := hV.subset hCG.vertexSet_mono
  have hCE : E(C.graph).Finite := hE.subset hCG.edgeSet_mono
  have hCNo : ¬ IsIsoMinor (forestTreeGraph lam) C.graph := by
    rintro ⟨K, hKC, edges, hEdges, hIso⟩
    exact hNo ⟨K, hKC.trans hCG, edges, hEdges, hIso⟩
  have hNoComb := not_rootedPathComb_of_not_forestTree C hCV hCE lam hCNo
  have hGrid := theorem_3_5_proof lam hlam hodd C.graph hCNo
  exact (rooted_width_bounds lam hodd C hCV (componentVertices_connected G v) hGrid).1
    lam le_rfl 3 (by decide) hNoComb

end GraphMinor.GM01
