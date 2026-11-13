module

public import GraphMinor.Compute.GM02TopologicalComplexity
public import GraphMinor.Compute.GM02TopologicalWordBounds
public import GraphMinor.Compute.GM02TopologicalInputFacts

/-!
# Plain-input polynomial computation for II (4.6)

The fixed comparison graph bounds the number of pattern edges. Choose
one recursive width threshold above the corrected split-graph bound.
The complete execution theorem, its word bounds, and its time bound
then give a polynomial algorithm on the original graph-pair encoding.
-/

public section
namespace GraphMinor.Compute
open Graph Set

/-- The topological-containment program runs in polynomial time under the printed fixed-subgraph promise. -/
theorem gm02Algorithm46_computes {A B : Type*} (H₀ : Graph A B)
    (hE : E(H₀).Finite) (w : ℤ) :
    let K := E(H₀).ncard
    let q := max w.toNat 2 + 2 * K + 1
    ComputesRelInTime gm02TopologicalSize
      (fun x s => s.arrs inArr = x.enc ∧
        ∃ L : Graph A B, L ≤ H₀ ∧ Nonempty (Iso x.H L))
      (fun x s => x.correct w s) (gm02TopologicalDecisionProg K q)
      (fun n => (n + 1) ^ gm02TopologicalPolynomialExponent q K) := by
  dsimp only
  let K := E(H₀).ncard
  let q := max w.toNat 2 + 2 * K + 1
  refine ⟨gm02TopologicalPolynomialCoefficient q K, gm02TopologicalWordCoefficient q K,
    ?_, ?_, ?_⟩
  · unfold gm02TopologicalPolynomialCoefficient
    omega
  · have h := gm02TopologicalWordCoefficient_ge_two q K
    omega
  · intro x s hin
    obtain ⟨L, hL, ⟨φ⟩⟩ := hin.2
    have hK : x.edges.length ≤ K := x.edges_le_of_iso_subgraph hE hL φ
    obtain ⟨hw, hsize, henc, hN, hmw, hpow, hjoin, hword⟩ :=
      gm02Topological_wordBounds q K x
    obtain ⟨s', t, he, ht, hc⟩ := gm02TopologicalDecisionProg_exec x s hK w q
      (Nat.lt_succ_self _) hin.1 hw hsize henc hN hmw hpow hjoin hword
    exact ⟨s', t, he, ht.trans (gm02TopologicalBudget_polynomial q K x), hc⟩

end GraphMinor.Compute
