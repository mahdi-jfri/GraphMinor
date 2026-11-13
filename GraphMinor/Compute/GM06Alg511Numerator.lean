module

public import GraphMinor.Compute.GM06Alg511WindingSetup
public import GraphMinor.Compute.GM06Alg511ScaledWinding
import Mathlib.Tactic

/-!
# Integer numerator output for the initial winding

For VI (5.11), page 134, append the fixed scaled-numerator arithmetic
to the complete initial winding phase. Doubling the word size suffices
for the products of word-sized accumulators and the path count. The
previous execution lifts to this larger size with the same time.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute a feasible initial winding as signed numerator parts
54/55 over the positive path count in register 52. -/
def gm06Alg511NumeratorProg : Cmd :=
  .seq gm06Alg511InitialWindingProg gm06Alg511ScaledWindingProg

/-- A product and an added index fit in twice the word size when
all three operands fit in the original word size. -/
theorem gm06Alg511ProductAdd_lt_double {w k p j : ℕ}
    (hk : k < 2 ^ w) (hp : p < 2 ^ w) (hj : j < 2 ^ w) :
    k * p + j < 2 ^ (2 * w) := by
  have hpow : 2 ^ (2 * w) = (2 ^ w) * (2 ^ w) := by
    rw [show 2 * w = w + w by omega, Nat.pow_add]
  rw [hpow]
  calc
    k * p + j < k * p + 2 ^ w := Nat.add_lt_add_left hj _
    _ ≤ k * 2 ^ w + 2 ^ w := Nat.add_le_add_right (Nat.mul_le_mul_left k hp.le) _
    _ = (k + 1) * 2 ^ w := by ring
    _ ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_right _ (by omega)

end GraphMinor.Compute
