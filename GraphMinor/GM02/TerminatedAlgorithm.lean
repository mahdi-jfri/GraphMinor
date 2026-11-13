module

public import GraphMinor.Compute.GM02Algorithm32

/-!
# The terminated-graph algorithm of Graph Minors II

The alternating A1/A2 program decides feasibility or gives a width
threshold on simple inputs. The final program computes the underlying
simple graph from the original multigraph, keeps its supplied terminal
pairs, and uses the larger width parameter from page 318. Its actual
Word RAM execution and polynomial bound give the printed three-way
algorithm for arbitrary terminated input graphs.
-/

public section
namespace GraphMinor.GM02
open GraphMinor.Compute

/-- Graph Minors II, (3.2), page 318:
"For any two fixed integers $w$, $k$ there is a polynomial algorithm which has input a terminated graph $(G, \mathcal{A})$ of index $\le k$, and outputs either"

"(i) $(G, \mathcal{A})$ is feasible, or"
"(ii) $(G, \mathcal{A})$ is not feasible, or"
"(iii) $G$ has tree-width $> w$."

Follow the paper's alternating recursion and its final underlying-simple
graph reduction. The input contains only original multiplicities and
terminal endpoints. The three flags have the stated meanings for the
original graph, including its loops and parallel edges. -/
theorem algorithm_3_2_proof (w k : ℤ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime gm02MultiTerminatedSize
        (fun x s => s.arrs inArr = x.enc ∧ (x.A.index : ℤ) ≤ k)
        (fun x s => x.correct w s) P (fun n => (n + 1) ^ c) := by
  exact ⟨gm02Algorithm32Prog w k, gm02RecursivePolynomialExponent (recursiveWidthParameter w k),
    gm02Algorithm32_computes w k⟩

end GraphMinor.GM02
