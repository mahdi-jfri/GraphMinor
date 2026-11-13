module

public import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Bounding geometric decay after deletion

During branch construction, at most a known number of vertices have
been deleted. Replace the geometric numerator by the original order
and its denominator by the smallest permitted remaining order. This
gives one explicit numeric bound for all allowed deletion counts.
-/

public section
namespace GraphMinor.Thomason

/-- A single conservative geometric bound covers every deletion count
up to `C`, provided the reserved choice count `M` fits in the remainder. -/
theorem geometric_bound_after_deletion_le (N D M C k x : ℕ)
    (hx : x ≤ C) (hMC : M + C ≤ N) :
    (N - x) * D ^ k / (N - x + 1 - M) ^ k ≤
      N * D ^ k / (N - C + 1 - M) ^ k := by
  have hB : 0 < N - C + 1 - M := by omega
  have hden : N - C + 1 - M ≤ N - x + 1 - M := by omega
  have hp := Nat.pow_le_pow_left hden k
  apply (Nat.le_div_iff_mul_le (pow_pos hB k)).mpr
  calc
    ((N - x) * D ^ k / (N - x + 1 - M) ^ k) * (N - C + 1 - M) ^ k ≤
        ((N - x) * D ^ k / (N - x + 1 - M) ^ k) * (N - x + 1 - M) ^ k :=
      Nat.mul_le_mul_left _ hp
    _ ≤ (N - x) * D ^ k := Nat.div_mul_le_self _ _
    _ ≤ N * D ^ k := Nat.mul_le_mul_right _ (Nat.sub_le _ _)

end GraphMinor.Thomason
