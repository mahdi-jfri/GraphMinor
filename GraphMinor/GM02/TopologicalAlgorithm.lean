module

public import GraphMinor.Compute.GM02Algorithm46

/-!
# The labelled topological-containment algorithm of Graph Minors II

Eliminate branch loops as on page 319, build the split terminated graphs,
and apply the terminated-graph program. Edge vertices and distinct
incidence choices correct the printed split construction for loops and
parallel edges (see the correction to (4.5) in `corrections/GM02.md`). The resulting
program reads the original graph-pair encoding and has polynomial time.
-/

public section
namespace GraphMinor.GM02
open Graph Set GraphMinor.Compute

/-- Graph Minors II, (4.6), page 319:
"For any fixed graph $H_0$ and fixed integer $w$, there is a polynomial algorithm which has input graphs $G$, $H$ with $V(H) \\subseteq V(G)$ such that $H$ is isomorphic to a subgraph of $H_0$, and which has output either"

"(i) $G$ topologically contains $H$, or"
"(ii) $G$ does not topologically contain $H$, or"
"(iii) $G$ has tree-width $> w$."

The input type supplies the vertex inclusion. The only remaining input
promise is isomorphism to a subgraph of the fixed graph. The split
construction uses edge vertices and incidence choices to cover loops
and parallel edges, where the printed (4.5) fails. -/
theorem algorithm_4_6_proof {A B : Type*} (H₀ : Graph A B)
    (hE : E(H₀).Finite) (w : ℤ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime gm02TopologicalSize
        (fun x s => s.arrs inArr = x.enc ∧
          ∃ L : Graph A B, L ≤ H₀ ∧ Nonempty (Iso x.H L))
        (fun x s => x.correct w s) P (fun n => (n + 1) ^ c) := by
  let K := E(H₀).ncard
  let q := max w.toNat 2 + 2 * K + 1
  exact ⟨gm02TopologicalDecisionProg K q, gm02TopologicalPolynomialExponent q K,
    gm02Algorithm46_computes H₀ hE w⟩

end GraphMinor.GM02
