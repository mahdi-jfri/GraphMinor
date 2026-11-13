module
public import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega

/-!
# The size needed to connect a selected set

Thomason's main proof, p. 264 (1984), uses `k≥5` to ensure
`k≥floor(log₂ k)+3`, so the available degree surplus suffices for
Lemma 4. We prove this estimate directly from powers of two.
-/

public section
namespace GraphMinor.Thomason

/-- The elementary logarithm estimate used to join the chosen `k`-set
in Thomason's main theorem, p. 264. -/
theorem log_add_three_le {k : ℕ} (hk : 5 ≤ k) : Nat.log 2 k + 3 ≤ k := by
  have hp : k < 2 ^ (k - 2) := by
    induction k, hk using Nat.le_induction with
    | base => decide
    | succ n hn ih =>
      have he : n + 1 - 2 = (n - 2) + 1 := by omega
      rw [he, Nat.pow_succ]
      omega
  have hl : Nat.log 2 k < k - 2 :=
    (Nat.log_lt_iff_lt_pow (by decide) (by omega : k ≠ 0)).mpr hp
  omega

end GraphMinor.Thomason
