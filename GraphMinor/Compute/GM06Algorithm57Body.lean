module

public import GraphMinor.Compute.GM06Algorithm57Early
import GraphMinor.Compute.GM06Algorithm57Rerouting
import GraphMinor.Compute.GM06Algorithm57Terminal

/-!
# The complete concrete loop body of VI (5.7)

At an active represented entry the real early driver either performs
an early reduction or excludes all three early types. The latter case
calls the real whole Reduction 4 command. Its success reroutes and
continues; its failure calls the complete terminal branch, including
witness construction and UNDO when positive.

Each of these concrete executions establishes the outer invariant
after the counting-loop increment. Their actual instruction counts
have one uniform original-size bound. No correctness or execution
statement about a phase is a hypothesis of this theorem.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- Uniform time for one active concrete body, before the outer guard
and counter increment. It sums the proved budgets of its real branches. -/
@[expose] def gm06Algorithm57RoundCost (N : ℕ) : ℕ :=
  5062500000 * (N + 1) ^ 4 + 20971520000000 * (N + 1) ^ 4 +
    327680000000 * (N + 1) ^ 3 + 2080 * (N + 1) ^ 2 + 5

private theorem early_time {a N : ℕ} (ha : a ≤ 5062500000 * (N + 1) ^ 4) :
    a + 2 ≤ gm06Algorithm57RoundCost N := by
  unfold gm06Algorithm57RoundCost
  omega

private theorem reroute_time {a b N : ℕ} (ha : a ≤ 5062500000 * (N + 1) ^ 4)
    (hb : b ≤ 20971520000000 * (N + 1) ^ 4) :
    a + (1 + (b + 2)) ≤ gm06Algorithm57RoundCost N := by
  unfold gm06Algorithm57RoundCost
  omega

private theorem terminal_time {a b c N : ℕ} (ha : a ≤ 5062500000 * (N + 1) ^ 4)
    (hb : b ≤ 20971520000000 * (N + 1) ^ 4)
    (hc : c ≤ 327680000000 * (N + 1) ^ 3 + 2080 * (N + 1) ^ 2 + 3) :
    a + (1 + (b + (1 + c))) ≤ gm06Algorithm57RoundCost N := by
  unfold gm06Algorithm57RoundCost
  omega

/-- The actual complete active body executes and preserves the outer invariant (Lemma 18 of our
proof of VI (5.7), outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) for every positive `k`. All
four reduction branches and both terminal outcomes call their already proved concrete execution and
drawing theorems. The outer counter is kept for the caller to increment. -/
theorem gm06Algorithm57_body
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder} {θ : ℝ}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    (hinit : initial.tagged = input.graph.initialTagged)
    (hvertex : initial.vertex = input.graph.vertexLabels)
    (hedge : HEq initial.edge input.graph.edgeLabels)
    (hG₀ : IsCylinderSection5Drawing k G₀) (hθ₀ : L₀.HasTheta θ)
    {i : ℕ} (s : State) (inv : gm06SuccessorLoopInvariant input θ initial i s)
    (hgo : s.regs 904 = 1) :
    ∃ sf t, Exec (wordSize 32 (gm06SuccessorInputSize x))
        (gm06SuccessorLoopBody gm06Reduction4PhaseProg gm06TerminalPhaseProg) s sf t ∧
      t ≤ gm06Algorithm57RoundCost (gm06SuccessorInputSize x) ∧
      sf.regs 900 = i ∧ gm06SuccessorLoopInvariant input θ initial (i + 1) (sf.setReg 900 (i + 1)) := by
  obtain ⟨se, te, hee, hte, he900, he905, hego, heinput, hecase⟩ :=
    gm06Algorithm57_early_invariant input initial hinit hG₀ hθ₀ s inv hgo
  rcases hecase with ⟨heBody, hinv⟩ | ⟨heflag, ends, rots, paths, G, L, cur, d, r,
      records, tail, hcounter, run, trace, core, hinj, hbits, hcapacity, hno⟩
  · exact ⟨se, te + 2, heBody, early_time hte, he900, hinv⟩
  · obtain ⟨sr, tr, her, htr, hr900, hr905, hrgo, hrinput, hrcase⟩ :=
      gm06Algorithm57_rerouting_invariant input initial hinit hG₀ hθ₀ cur hinj hbits
        hcounter run trace hno se core hcapacity he900 he905 hego heinput
    rcases hrcase with ⟨heSuffix, hinv⟩ | ⟨hrflag, corer, hcapacityr, hnone⟩
    · have hex : Exec (wordSize 32 (gm06SuccessorInputSize x))
          (gm06SuccessorLoopBody gm06Reduction4PhaseProg gm06TerminalPhaseProg) s sr
          (te + (1 + (tr + 2))) :=
        .seq hee (.ite_false (Crossing.eval_reg heflag (Nat.two_pow_pos _)) heSuffix)
      exact ⟨sr, _, hex, reroute_time hte htr, hr900, hinv⟩
    · obtain ⟨st, tt, het, htt, ht900, _, _, _, _, hinv⟩ :=
        gm06Algorithm57_terminal input initial hinit hvertex hedge hG₀ hθ₀ cur hinj hbits
          run trace hnone sr corer hcapacityr hr900 hr905 hrinput
      have hex : Exec (wordSize 32 (gm06SuccessorInputSize x))
          (gm06SuccessorLoopBody gm06Reduction4PhaseProg gm06TerminalPhaseProg) s st
          (te + (1 + (tr + (1 + tt)))) :=
        .seq hee (.ite_false (Crossing.eval_reg heflag (Nat.two_pow_pos _))
          (.seq her (.ite_false (Crossing.eval_reg hrflag (Nat.two_pow_pos _)) het)))
      exact ⟨st, _, hex, terminal_time hte htr htt, ht900, hinv⟩

end GraphMinor.Compute
