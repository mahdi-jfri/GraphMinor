module

public import GraphMinor.Compute.GM13ClassProgram
import GraphMinor.Compute.Join13Adapter72
import GraphMinor.Compute.Algorithm41Aux20

/-!
# Quadratic recognition of a minor-closed class excluding a planar graph

Graph Minors XIII, (4.3), pages 76–77, first obtains a finite excluded-minor
list and a branch-width cutoff. The four-step program then caps the graph,
calls (3.3), rejects the high-width case, and otherwise uses (4.1) to decide
membership from the empty-root folio. Every subroutine used here is proved.

Graphs are supplied in the standard multigraph encoding, including loops and
parallel edges. The answer is `1` for membership and `0` otherwise, in `outReg`.
Step (1) keeps at most `δ` loops at each vertex and at most `δ + 1` edges between two
distinct vertices (`capPairProg`). The print says `δ` edges, which can lose a minor (see the
correction to (4.3), Step (1), in `corrections/GM13.md`). `membership_capPair43` proves that the
cap keeps membership, by
the minor argument behind the paper's "as is easily seen", and the capped graph has `O(v²)` edges.
-/

public section
namespace GraphMinor.Compute

open GraphMinor GM13 Graph Set Classical

/-- Graph Minors XIII, (4.3), pages 76–77:
"Let $\mathcal{F}$ be a minor-closed class of graphs such that some planar graph is not in
$\mathcal{F}$. Then there is an algorithm to determine whether $G \in \mathcal{F}$ with running
time $O(v^2)$."

This reusable recognition result takes only minor closure and a finite excluded
planar graph. It derives the finite obstruction list, the width cutoff, and all
subroutine specifications. The input size is `(n + 1)²`, so a linear bound in
`alg44Size` is the asserted quadratic bound in the number of vertices. -/
theorem gm13_algorithm_4_3
    (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ)))
    (hclosed : ∀ ⦃G₁ G₂ : Graph ℕ (ℕ × ℕ × ℕ)⦄,
      V(G₁).Finite → E(G₁).Finite → V(G₂).Finite → E(G₂).Finite →
      IsIsoMinor G₁ G₂ → G₂ ∈ ℱ → G₁ ∈ ℱ)
    (H₀ : Graph ℕ (ℕ × ℕ × ℕ)) (hVH₀ : V(H₀).Finite) (hEH₀ : E(H₀).Finite)
    (hPlanar₀ : IsPlanar H₀) (hH₀_not : H₀ ∉ ℱ) :
    ∃ P : Cmd,
      ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
        (fun x s => s.regs outReg = if x.G.toGMDigraph.toGraph ∈ ℱ then 1 else 0)
        P (fun size => size) := by
  obtain ⟨B, ω, δ, _, hω, hB, hclass, hhigh⟩ :=
    GM13.theorem_4_3_proof ℱ hclosed H₀ hVH₀ hEH₀ hPlanar₀ hH₀_not
  have hB' : ∀ H ∈ B,
      V(H).Finite ∧ E(H).Finite ∧ V(H).ncard ≤ δ ∧ E(H).ncard ≤ δ := by
    intro H hHB
    have hh := hB H hHB
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
  let P33 := alg33MultiProg ω 11 12 13 20 10
  have h33 : Alg33Spec ω 11 12 13 20 10 P33 :=
    alg33Spec_of_algorithm_3_3 ω hω 11 12 13 20 10
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨P41, h41⟩ := alg41MultiSpec72_of_claim41
    (fun δ ξ B => ⟨alg41CoreProg δ ξ B, algorithm_4_1_core δ ξ B⟩) δ (3 * ω)
  obtain ⟨C, c, hC, hc, run⟩ :=
    alg43Prog_exec ℱ B δ ω hω hB' hclass hclosed hhigh P33 P41 h33 h41
  refine ⟨alg43Prog ℱ δ P33 P41, C, c, hC, hc, ?_⟩
  intro x s hin
  exact run x.n x.G (wordSize c (alg44Size x)) le_rfl s hin

end GraphMinor.Compute
