module

public import GraphMinor.GM06.Alg34LoopRoundExec
import GraphMinor.Compute.WhileRounds
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Termination and time of the reduction loop

Multiply remaining work by the cost of one round and its guard. Each
round strictly decreases work, so it pays for its execution. The loop
rule then yields a halted configuration with the original answer.
-/

public section
namespace GraphMinor.Compute
open GM06
universe u

/-- The complete reduction loop halts with the correct saved Boolean
and takes at most its initial work times the uniform round cost. -/
theorem gm06Driver_while {M E Q : ℕ} {answer : Prop}
    {cfg : GM06DriverConfig} {s : State}
    (hInv : gm06DriverInvariant.{u} M E Q answer cfg s) :
    ∃ b s' t, Exec (wordSize 256 Q) (.while (.reg 9000) gm06DriverBody) s s' t ∧
      t ≤ (gm06RoundBound Q + 1) * cfg.work (M + 1) + 1 ∧
      s'.regs 9001 = (if b then 1 else 0) ∧ (answer ↔ b = true) := by
  have hw : 1 < 2 ^ wordSize 256 Q := lt_two_pow_wordSize_of_le (by decide) (by omega)
  let P := gm06RoundBound Q + 1
  have hround : ∀ g s, gm06DriverInvariant.{u} M E Q answer g s →
      ∃ v, (Expr.reg 9000).eval (wordSize 256 Q) s = some v ∧ (v ≠ 0 →
        ∃ g' s' t, Exec (wordSize 256 Q) gm06DriverBody s s' t ∧
          gm06DriverInvariant.{u} M E Q answer g' s' ∧
          (Expr.reg 9000).cost + t + P * g'.work (M + 1) ≤ P * g.work (M + 1)) := by
    intro g s hi
    cases g with
    | halted b =>
      exact ⟨0, Crossing.eval_reg hi.1 (Nat.two_pow_pos _), fun hv => False.elim (hv rfl)⟩
    | running X past tasks =>
      refine ⟨1, Crossing.eval_reg (gm06DriverInvariant_running_flag hi) hw, ?_⟩
      intro _
      obtain ⟨g', s', t, he, ht, hi', hlt⟩ := gm06Driver_round hi
      have hpay := Nat.mul_le_mul_left P (Nat.succ_le_of_lt hlt)
      rw [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hpay
      exact ⟨g', s', t, he, hi', by change 1 + t + _ ≤ _; dsimp only [P] at *; omega⟩
  obtain ⟨g', s', t, he, hi', hz, ht⟩ := Exec.while_pot
    (gm06DriverInvariant.{u} M E Q answer) (fun g => P * g.work (M + 1)) hround cfg s hInv
  cases g' with
  | halted b =>
    exact ⟨b, s', t, he, by change t + P * 0 ≤ P * cfg.work (M + 1) + 1 at ht; simpa only [Nat.mul_zero, Nat.add_zero] using ht,
      hi'.2.1, hi'.2.2⟩
  | running X past tasks =>
    have hh := Crossing.eval_reg (gm06DriverInvariant_running_flag hi') hw
    rw [hz] at hh
    cases hh

end GraphMinor.Compute
