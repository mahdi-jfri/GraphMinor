module

public import GraphMinor.Compute.GM06Algorithm57Body
public import GraphMinor.Compute.GM06SuccessorLoopCost
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Executing the concrete counting loop of VI (5.7)

The actual active-body theorem preserves the outer invariant for
every positive path count. A completed entry executes an idle round.
The finite counting-loop execution therefore follows by induction
on its original fixed range, with a uniform instruction budget.

The actual-history measure excludes an active entry at the final
counter, so the resulting state has produced the public output.
Initialization and all loop rounds together have a fifth-degree
original-size time bound and logarithmic words.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

private theorem idle_time (N : ℕ) : 2 ≤ gm06Algorithm57RoundCost N + 1 := by
  unfold gm06Algorithm57RoundCost
  omega

private theorem guarded_time {a b : ℕ} (h : a ≤ b) : 1 + a ≤ b + 1 := by omega

private theorem total_time {N F a b : ℕ}
    (ha : a ≤ 100 * (N + 1)) (hF : F ≤ 4 * (N + 1))
    (hb : b ≤ 3 + F * (gm06Algorithm57RoundCost N + 8)) :
    a + b ≤ gm06SuccessorLoopCost N (20971520000000 * (N + 1) ^ 4)
      (327680000000 * (N + 1) ^ 3) := by
  have hm := Nat.mul_le_mul_right (gm06Algorithm57RoundCost N + 8) hF
  calc
    a + b ≤ 100 * (N + 1) + (3 + 4 * (N + 1) * (gm06Algorithm57RoundCost N + 8)) := by omega
    _ = _ := by unfold gm06SuccessorLoopCost gm06Algorithm57RoundCost; dsimp only; ring

/-- The concrete program executes from ordinary input and returns the
actual original-label output for every positive path count. The complete loop uses its
proved active body and actual histories; no loop-step or phase theorem
is a hypothesis. -/
theorem gm06Algorithm57_exec
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder} {θ : ℝ}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (hG₀ : IsCylinderSection5Drawing k G₀) (hθ₀ : L₀.HasTheta θ)
    (s : State) (hinput : s.arrs 0 = gm06EncodeSuccessorInput x) :
    ∃ sf t, Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06Algorithm57Prog s sf t ∧
      t ≤ gm06SuccessorLoopCost (gm06SuccessorInputSize x)
        (20971520000000 * (gm06SuccessorInputSize x + 1) ^ 4)
        (327680000000 * (gm06SuccessorInputSize x + 1) ^ 3) ∧
      sf.regs 904 = 0 ∧ sf.arrs 0 = s.arrs 0 ∧
      GM06SuccessorOutputRep input θ (sf.regs 0) (sf.arrs 8) := by
  let N := gm06SuccessorInputSize x
  let F := 2 * (x.vertexCount + G₀.E.ncard) + 1
  let B := gm06Algorithm57RoundCost N + 1
  obtain ⟨hw, _, _, hFcap, _, _⟩ := input.initial_word_caps hG₀
  have hw1 : 1 < 2 ^ wordSize 32 N := (by decide : 1 < 3).trans hw
  obtain ⟨sm, ti, initial, hei, hti, htag, hvertex, hedge, hi⟩ :=
    gm06InitializeSuccessorLoopCoreProg_invariant input hG₀ θ s hinput
  let I := gm06SuccessorLoopInvariant input θ initial
  obtain ⟨sf, tf, hef, htf, hf⟩ := Crossing.forUp_exec' I F B hw1 hFcap
    (r_i := 900) (hi := .reg 905)
    (fun j _ st hj => ⟨hj.1, Crossing.eval_reg hj.2.1 hFcap⟩)
    (fun j _ st hj => by
      rcases gm06SuccessorLoopInvariant_flag hj with hstop | hgo
      · have he : Exec (wordSize 32 N)
            (.ite (.reg 904) (gm06SuccessorLoopBody gm06Reduction4PhaseProg gm06TerminalPhaseProg) .skip)
            st st 2 := .ite_false (Crossing.eval_reg hstop (Nat.two_pow_pos _)) (.skip _)
        exact ⟨st, 2, he, idle_time N, gm06SuccessorLoopInvariant_idle hj hstop, hj.1⟩
      · obtain ⟨st', t, he, ht, hcounter, hnext⟩ :=
          gm06Algorithm57_body input initial htag hvertex hedge hG₀ hθ₀ st hj hgo
        have he' : Exec (wordSize 32 N)
            (.ite (.reg 904) (gm06SuccessorLoopBody gm06Reduction4PhaseProg gm06TerminalPhaseProg) .skip)
            st st' (1 + t) := .ite_true (Crossing.eval_reg hgo hw1) one_ne_zero he
        exact ⟨st', 1 + t, he', guarded_time ht, hnext, hcounter⟩)
    sm hi
  have htf' : tf ≤ 3 + F * (gm06Algorithm57RoundCost N + 8) := by
    change tf ≤ 3 + F * (1 + 6 + (gm06Algorithm57RoundCost N + 1)) at htf
    have heq : 1 + 6 + (gm06Algorithm57RoundCost N + 1) = gm06Algorithm57RoundCost N + 8 := by omega
    rw [heq] at htf
    exact htf
  obtain ⟨hn, hm, _, _, _, _⟩ := input.size_bounds
  have hF : F ≤ 4 * (N + 1) := by dsimp only [F, N]; omega
  have heFull : Exec (wordSize 32 N) gm06Algorithm57Prog s sf (ti + tf) := by
    rw [gm06Algorithm57Prog_eq]
    cases hei with
    | seq heInit heControl =>
      simpa only [Nat.add_assoc] using Exec.seq heInit (Exec.seq heControl hef)
  obtain ⟨hstop, hout⟩ := gm06SuccessorLoopInvariant_output_at_fuel input initial hG₀ hθ₀ hf
  exact ⟨sf, ti + tf, heFull, total_time hti hF htf', hstop, gm06Algorithm57Prog_input_preserved heFull, hout⟩

/-- A uniform polynomial bound for the actual concrete execution for
every positive path count. The degree five comes from linearly many rounds of the proved
quartic dense-array budgets, with the cubic terminal phase included. -/
theorem gm06Algorithm57_polynomial
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder} {θ : ℝ}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (hG₀ : IsCylinderSection5Drawing k G₀) (hθ₀ : L₀.HasTheta θ)
    (s : State) (hinput : s.arrs 0 = gm06EncodeSuccessorInput x) :
    ∃ sf t, Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06Algorithm57Prog s sf t ∧
      t ≤ 85217050012103 * (gm06SuccessorInputSize x + 1) ^ 5 ∧
      sf.regs 904 = 0 ∧ sf.arrs 0 = s.arrs 0 ∧
      GM06SuccessorOutputRep input θ (sf.regs 0) (sf.arrs 8) := by
  obtain ⟨sf, t, he, ht, hstop, hsame, hout⟩ := gm06Algorithm57_exec input hG₀ hθ₀ s hinput
  have hp := gm06SuccessorLoopCost_le_polynomial (gm06SuccessorInputSize x) 20971520000000 327680000000 4 3
  norm_num [gm06SuccessorLoopDegree] at hp
  exact ⟨sf, t, he, ht.trans hp, hstop, hsame, hout⟩

end GraphMinor.Compute
