module

public import GraphMinor.Compute.GM02BalancedComplexity

/-!
# Graph Minors II's balanced-separation algorithm

The explicit Word RAM program enumerates the permitted separator sets,
checks the remaining component counts, groups components by the proof of
(2.6), and writes both side vertex sets. Its input contains only a plain
simple graph encoding and the supplied subset's membership bits. A
negative integer order bound rejects immediately.
-/

public section
namespace GraphMinor.GM02
open GraphMinor.Compute

/-- Graph Minors II, (3.1), page 316:
"For any fixed integer $w$, there is a polynomial algorithm which has input
a simple graph $G$ and a subset $Q$ of $V(G)$, and which has output either"
a separation of order at most $w$ satisfying the two printed two-thirds
balance bounds, or "a (valid) statement that no such separation exists."

`GM02Alg31Input.correct` includes actual side arrays for a successful
separation, and excludes every such separation for a negative output.
The program follows the paper's exhaustive component test and component
grouping. Degree `w.toNat + 3` bounds its vertex-count running time. -/
theorem algorithm_3_1_proof (w : ℤ) :
    ∃ P : Cmd, ComputesRelInTime gm02Alg31Size (fun x s => s.arrs inArr = x.enc)
      (fun x s => x.correct w s) P (fun n => (n + 1) ^ (w.toNat + 3)) := by
  by_cases hw : 0 ≤ w
  · have hk : (w.toNat : ℤ) = w := Int.toNat_of_nonneg hw
    refine ⟨gm02BalancedSeparationProg w.toNat, ?_⟩
    simpa only [hk] using gm02Alg31_nat_computes w.toNat
  · refine ⟨.assign outReg (.const 0), ?_⟩
    apply (gm02Alg31_negative (w := w) (by omega)).mono_time (K := 1) le_rfl
    intro n
    simpa only [Nat.one_mul] using Nat.one_le_pow (w.toNat + 3) (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

end GraphMinor.GM02
