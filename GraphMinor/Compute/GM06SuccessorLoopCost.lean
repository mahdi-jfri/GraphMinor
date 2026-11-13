module

public import GraphMinor.Compute.GM06ReachableBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Combining the loop's polynomial budgets

The early scans of VI (5.7), page 133, have the proved uniform
fourth-degree bound in the original size. The terminal decision
and UNDO are quadratic. The loop makes at most a linear number
of rounds. This file combines those actual budgets with the two
whole-phase budgets by scalar inequalities, without assuming any
phase correctness or termination statement.

The resulting degree is one more than the maximum of four and
the two phase degrees. The actual phase bounds will be substituted
when proving the complete command's execution theorem.
-/

public section
namespace GraphMinor.Compute

/-- A uniform complete-loop budget, including initialization,
finite-counter overhead, both phases, terminal decision and UNDO.
The two phase costs are ordinary numeric arguments. -/
@[expose] def gm06SuccessorLoopCost (N reduction4 terminal : ℕ) : ℕ :=
  let S := N + 1
  100 * S + 3 + 4 * S *
    (5062500000 * S ^ 4 + reduction4 + terminal + 2080 * S ^ 2 + 13)

/-- The degree contributed by linear iteration of the largest
per-round polynomial bound. -/
@[expose] def gm06SuccessorLoopDegree (reduction4Degree terminalDegree : ℕ) : ℕ :=
  max 4 (max reduction4Degree terminalDegree) + 1

/-- Increasing either phase budget increases the total budget. -/
theorem gm06SuccessorLoopCost_mono (N : ℕ) {a b c d : ℕ}
    (hab : a ≤ b) (hcd : c ≤ d) :
    gm06SuccessorLoopCost N a c ≤ gm06SuccessorLoopCost N b d := by
  unfold gm06SuccessorLoopCost
  dsimp only
  gcongr

/-- Substituting any two polynomial phase budgets gives a fixed
polynomial bound for the complete cost expression. This is pure
arithmetic and contains no assumption about either phase program. -/
theorem gm06SuccessorLoopCost_le_polynomial (N C₄ Cₜ d₄ dₜ : ℕ) :
    gm06SuccessorLoopCost N (C₄ * (N + 1) ^ d₄) (Cₜ * (N + 1) ^ dₜ) ≤
      (4 * (5062503000 + C₄ + Cₜ) + 103) *
        (N + 1) ^ gm06SuccessorLoopDegree d₄ dₜ := by
  let S := N + 1
  let e := max 4 (max d₄ dₜ)
  have hS : 1 ≤ S := by omega
  have h4 : 4 ≤ e := Nat.le_max_left _ _
  have h2 : 2 ≤ e := (by decide : 2 ≤ 4).trans h4
  have hd₄ : d₄ ≤ e := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hdₜ : dₜ ≤ e := (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hp4 : S ^ 4 ≤ S ^ e := pow_le_pow_right' hS h4
  have hp2 : S ^ 2 ≤ S ^ e := pow_le_pow_right' hS h2
  have hp₄ : S ^ d₄ ≤ S ^ e := pow_le_pow_right' hS hd₄
  have hpₜ : S ^ dₜ ≤ S ^ e := pow_le_pow_right' hS hdₜ
  have hp0 : 1 ≤ S ^ e := by simpa only [pow_zero] using pow_le_pow_right' hS (Nat.zero_le e)
  have hconstant : 13 ≤ 13 * S ^ e := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 13 hp0
  have hround : 5062500000 * S ^ 4 + C₄ * S ^ d₄ + Cₜ * S ^ dₜ + 2080 * S ^ 2 + 13 ≤
      (5062503000 + C₄ + Cₜ) * S ^ e := by
    calc
      _ ≤ 5062500000 * S ^ e + C₄ * S ^ e + Cₜ * S ^ e + 2080 * S ^ e + 13 * S ^ e :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.mul_le_mul_left _ hp4) (Nat.mul_le_mul_left _ hp₄))
          (Nat.mul_le_mul_left _ hpₜ)) (Nat.mul_le_mul_left _ hp2)) hconstant
      _ = (5062502093 + C₄ + Cₜ) * S ^ e := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have hp1 : S ≤ S ^ (e + 1) := by
    simpa only [pow_one] using pow_le_pow_right' hS (by omega : 1 ≤ e + 1)
  have hp0' : 1 ≤ S ^ (e + 1) := by
    simpa only [pow_zero] using pow_le_pow_right' hS (Nat.zero_le (e + 1))
  have hinit : 100 * S + 3 ≤ 103 * S ^ (e + 1) := by omega
  change 100 * S + 3 + 4 * S *
      (5062500000 * S ^ 4 + C₄ * S ^ d₄ + Cₜ * S ^ dₜ + 2080 * S ^ 2 + 13) ≤
    (4 * (5062503000 + C₄ + Cₜ) + 103) * S ^ (e + 1)
  calc
    _ ≤ 103 * S ^ (e + 1) + 4 * S * ((5062503000 + C₄ + Cₜ) * S ^ e) :=
      Nat.add_le_add hinit (Nat.mul_le_mul_left _ hround)
    _ = _ := by rw [pow_succ]; ring

end GraphMinor.Compute
