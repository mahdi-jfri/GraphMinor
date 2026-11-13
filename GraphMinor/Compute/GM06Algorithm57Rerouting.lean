module

public import GraphMinor.Compute.GM06Algorithm57
public import GraphMinor.Compute.GM06SuccessorLoopInvariant
import GraphMinor.Compute.GM06ReachedReroutingBranch

/-!
# Preserving the outer invariant through the concrete rerouting branch

The failed early driver supplies the current bit-one core and the
three early exclusions. The actual whole
Reduction 4 phase either gives a true rerouting or excludes the last
reduction too. This file connects that proved branch to the outer
counter and actual chronological histories.

A success executes the phase and its following success guard, then
establishes the outer invariant after the counter increment. A failure
preserves the core and gives the no-reduction premise for the terminal
criterion. The original code, fuel and continuation flag survive.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- The actual concrete rerouting branch preserves the outer invariant
on success for every positive `k`. On failure it keeps the full reached core and
proves that no reduction applies, ready for the terminal branch. -/
theorem gm06Algorithm57_rerouting_invariant
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder} {θ : ℝ}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    (hinit : initial.tagged = input.graph.initialTagged)
    (hG₀ : IsCylinderSection5Drawing k G₀) (hθ₀ : L₀.HasTheta θ)
    {ends : List ℕ} {rots paths : List (List ℕ)}
    {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} G L)
    (hvinj : Function.Injective cur.vertex) (hbits : ∀ p ∈ cur.tagged, p.2 ≤ 1)
    {d r i : ℕ} (hcounter : d + r = i)
    (run : Alg57ReductionRun ⟨G₀, L₀, true⟩ ⟨G, L, true⟩ d r)
    {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records)
    (hno : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
      ¬ Section5Reduction1Step k G L H M ∧ ¬ Section5Reduction2Step k G L H M ∧
        ¬ Section5Reduction3Step k G L H M)
    {tail : List ℕ} (s : State) (core : GM06SuccessorCoreRep cur true records tail s)
    (hcapacity : (s.arrs 9).length = 2 * (x.vertexCount + G₀.E.ncard))
    (h900 : s.regs 900 = i) (h905 : s.regs 905 = 2 * (x.vertexCount + G₀.E.ncard) + 1)
    (hgo : s.regs 904 = 1) (hinput : s.arrs 0 = gm06EncodeSuccessorInput x) :
    ∃ sf t, Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06Reduction4PhaseProg s sf t ∧
      t ≤ 20971520000000 * (gm06SuccessorInputSize x + 1) ^ 4 ∧
      sf.regs 900 = i ∧ sf.regs 905 = 2 * (x.vertexCount + G₀.E.ncard) + 1 ∧
      sf.regs 904 = 1 ∧ sf.arrs 0 = gm06EncodeSuccessorInput x ∧
      ((Exec (wordSize 32 (gm06SuccessorInputSize x))
          (.seq gm06Reduction4PhaseProg (.ite (.reg 646) .skip
            (gm06FinishSuccessorProg gm06TerminalPhaseProg))) s sf (t + 2) ∧
          gm06SuccessorLoopInvariant input θ initial (i + 1) (sf.setReg 900 (i + 1))) ∨
       (sf.regs 646 = 0 ∧ GM06SuccessorCoreRep cur true records tail sf ∧
          (sf.arrs 9).length = 2 * (x.vertexCount + G₀.E.ncard) ∧
          ¬ Section5AnyReductionApplies k G L)) := by
  obtain ⟨sf, t, he, ht, _, hout⟩ := gm06Reached_rerouting_branch input initial hinit hG₀ hθ₀ cur
    hvinj run trace hno gm06TerminalPhaseProg s core
  obtain ⟨ha, hr⟩ := gm06Reduction4PhaseProg_core_frame he
  have h900' := (hr 900 (by simp)).trans h900
  have h905' := (hr 905 (by simp)).trans h905
  have hgo' := (hr 904 (by simp)).trans hgo
  have hinput' := (ha 0 (by simp)).trans hinput
  have hcapacity' : (sf.arrs 9).length = 2 * (x.vertexCount + G₀.E.ncard) := by
    rw [ha 9 (by simp)]; exact hcapacity
  refine ⟨sf, t, he, ht, h900', h905', hgo', hinput', ?_⟩
  rcases hout with ⟨hzero, core', hnone⟩ |
      ⟨M, hrows, _, heBranch, _, nextCore, hinj, run', trace', _, _, _⟩
  · exact Or.inr ⟨hzero, core', hcapacity', hnone⟩
  · refine Or.inl ⟨heBranch, ?_⟩
    refine ⟨by simp, by simpa using h905', hinput', Or.inr ⟨by simpa using hgo',
      ends, rots, _, G, M, cur.withLinkage M _ hrows, false, d, r + 1, records ++ [none], tail,
      ?_, run', trace', nextCore.setCounter (i + 1), hinj, hbits, hcapacity'⟩⟩
    omega

end GraphMinor.Compute
