module

public import GraphMinor.Compute.GM02TestInjectionCode
public import GraphMinor.Compute.GM02InjectionSizeBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A fixed polynomial bound for an injection candidate

The labelled test uses the host size plus a fixed pattern size. Bound
that shifted size by a fixed multiple of one plus the host size, then
raise to the labelled test's exponent. The same exponent covers all
linear input construction and the fixed decoding and validation work.
-/

public section
namespace GraphMinor.Compute

/-- A fixed coefficient for one injection-code test and its counting-loop overhead. -/
@[expose] noncomputable def gm02InjectionCodeCoefficient (q : ℕ) (H : GM02EdgeListInput) : ℕ :=
  (118 + 16 * H.n + 8 * H.edges.length + H.n * (8 + 4 * H.n) + (gm02InjectionValidExpr H.n).cost) +
    ((gm02InjectionMembershipExpr H.n).cost + 15) + 48 * (6 + H.n + 2 * H.edges.length) +
    gm02TopologicalPolynomialCoefficient q H.edges.length *
      (H.size + 1) ^ gm02TopologicalPolynomialExponent q H.edges.length

/-- A fixed polynomial in the plain host size bounds a whole candidate and its loop overhead. -/
theorem gm02InjectionCodeBudget_polynomial (q : ℕ) (G H : GM02EdgeListInput) :
    gm02InjectionCodeBudget q G H + 15 ≤ gm02InjectionCodeCoefficient q H *
      (G.size + 1) ^ gm02TopologicalPolynomialExponent q H.edges.length := by
  let D := gm02TopologicalPolynomialExponent q H.edges.length
  let P := (G.size + 1) ^ D
  let B := 118 + 16 * H.n + 8 * H.edges.length + H.n * (8 + 4 * H.n) + (gm02InjectionValidExpr H.n).cost
  let M := (gm02InjectionMembershipExpr H.n).cost + 15
  let F := 6 + H.n + 2 * H.edges.length
  let C := gm02TopologicalPolynomialCoefficient q H.edges.length
  have hD : 2 ≤ D := by
    dsimp only [D, gm02TopologicalPolynomialExponent, gm02RecursivePolynomialExponent]
    omega
  have hP : 1 ≤ P := Nat.one_le_pow D _ (by omega)
  have hsize : G.size + 1 ≤ P := Nat.le_self_pow (by omega) _
  have hn : G.n ≤ P := by
    have h : G.n ≤ G.size + 1 := by unfold GM02EdgeListInput.size; omega
    exact h.trans hsize
  have hB : B ≤ B * P := Nat.le_mul_of_pos_right _ hP
  have hM : G.n * M ≤ M * P := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left M hn
  have hL : 48 * gm02InjectedInputLength G H ≤ 48 * (F * P) :=
    Nat.mul_le_mul_left _ ((gm02InjectedInputLength_le_linear G H).trans (Nat.mul_le_mul_left F hsize))
  have hshift : G.size + H.size + 1 ≤ (H.size + 1) * (G.size + 1) := by
    nlinarith [Nat.zero_le (H.size * G.size)]
  have hpower : (G.size + H.size + 1) ^ D ≤ (H.size + 1) ^ D * P := by
    simpa only [Nat.mul_pow] using Nat.pow_le_pow_left hshift D
  have hC := Nat.mul_le_mul_left C hpower
  have hbudget : gm02InjectionCodeBudget q G H + 15 =
      B + G.n * M + 48 * gm02InjectedInputLength G H + C * (G.size + H.size + 1) ^ D := by
    dsimp only [gm02InjectionCodeBudget, gm02InjectionCandidateBudget, B, M, C, D]
    ring
  rw [hbudget]
  calc
    _ ≤ B * P + M * P + 48 * (F * P) + C * ((H.size + 1) ^ D * P) :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hB hM) hL) hC
    _ = gm02InjectionCodeCoefficient q H * (G.size + 1) ^ D := by
      dsimp only [gm02InjectionCodeCoefficient, B, M, F, C, P, D]
      ring

end GraphMinor.Compute
