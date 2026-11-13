module

public import GraphMinor.Compute.GM06Algorithm57
public import GraphMinor.Compute.GM06SuccessorLoopInvariant
import GraphMinor.Compute.GM06ReachedEarlyCore

/-!
# Preserving the outer invariant through the concrete early branches

An active outer-loop entry contains its actual current core and
histories. Running the concrete early driver either performs a
reduction or proves that all three early types fail. In the first
case it executes the whole concrete loop body, and the outer counter
increment gives the next invariant entry.

In the second case the theorem returns the current drawing, its
unchanged actual histories, bit-one core, and the three exclusions.
These are precisely the reached data passed to the whole Reduction 4
phase. No phase behavior is assumed and neither phase runs during an
early success.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- The concrete early driver preserves the outer invariant on every
success. A failure exposes the actual bit-one configuration and
proved early exclusions needed by the next whole-phase call. -/
theorem gm06Algorithm57_early_invariant
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder} {θ : ℝ}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    (hinit : initial.tagged = input.graph.initialTagged)
    (hG₀ : IsCylinderSection5Drawing k G₀) (hθ₀ : L₀.HasTheta θ)
    {i : ℕ} (s : State) (inv : gm06SuccessorLoopInvariant input θ initial i s)
    (hgo : s.regs 904 = 1) :
    ∃ sf t, Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06EarlyReductionsProg s sf t ∧
      t ≤ 5062500000 * (gm06SuccessorInputSize x + 1) ^ 4 ∧
      sf.regs 900 = i ∧ sf.regs 905 = 2 * (x.vertexCount + G₀.E.ncard) + 1 ∧
      sf.regs 904 = 1 ∧ sf.arrs 0 = gm06EncodeSuccessorInput x ∧
      ((Exec (wordSize 32 (gm06SuccessorInputSize x))
          (gm06SuccessorLoopBody gm06Reduction4PhaseProg gm06TerminalPhaseProg) s sf (t + 2) ∧
          gm06SuccessorLoopInvariant input θ initial (i + 1) (sf.setReg 900 (i + 1))) ∨
       (sf.regs 901 = 0 ∧ ∃ (ends : List ℕ) (rots paths : List (List ℕ))
         (G : Drawing ClosedCylinder) (L : CylinderLinkage k G)
         (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} G L)
         (d r : ℕ) (records : List (Option (ℕ × ℕ))) (tail : List ℕ),
         d + r = i ∧ Alg57ReductionRun ⟨G₀, L₀, true⟩ ⟨G, L, true⟩ d r ∧
         GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records ∧
         GM06SuccessorCoreRep cur true records tail sf ∧
         Function.Injective cur.vertex ∧ (∀ p ∈ cur.tagged, p.2 ≤ 1) ∧
         (sf.arrs 9).length = 2 * (x.vertexCount + G₀.E.ncard) ∧
         ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
           ¬ Section5Reduction1Step k G L H M ∧ ¬ Section5Reduction2Step k G L H M ∧
             ¬ Section5Reduction3Step k G L H M)) := by
  obtain ⟨h900, h905, hinput, hcase⟩ := inv
  rcases hcase with ⟨hstop, _⟩ | ⟨_, ends, rots, paths, G, L, cur, b, d, r,
      records, tail, hcounter, run, trace, core, hinj, hbits, hcapacity⟩
  · exact False.elim (Nat.zero_ne_one (hstop.symm.trans hgo))
  obtain ⟨sf, t, he, ht, ha, hr, hout⟩ := gm06Reached_early_core input initial hinit hG₀ hθ₀ cur hinj hbits b
    run records trace tail gm06Reduction4PhaseProg gm06TerminalPhaseProg s core hcapacity
  have h900' := (hr 900 (by simp)).trans h900
  have h905' := (hr 905 (by simp)).trans h905
  have hgo' := (hr 904 (by simp)).trans hgo
  have hinput' := (ha 0 (by simp)).trans hinput
  refine ⟨sf, t, he, ht, h900', h905', hgo', hinput', ?_⟩
  rcases hout with ⟨hflag, hb, core', hno⟩ |
      ⟨newEnds, newRots, newPaths, H, M, next, record, newTail, heBody, _, nextCore,
        hinj', hbits', _, run', trace', _, hcapacity'⟩
  · have run' : Alg57ReductionRun ⟨G₀, L₀, true⟩ ⟨G, L, true⟩ d r := by simpa only [hb] using run
    have h9eq : sf.arrs 9 = s.arrs 9 := core'.history.trans core.history.symm
    have hcapacity' : (sf.arrs 9).length = 2 * (x.vertexCount + G₀.E.ncard) := by
      rw [h9eq]; exact hcapacity
    exact Or.inr ⟨hflag, ends, rots, paths, G, L, cur, d, r, records, tail,
      hcounter, run', trace, core', hinj, hbits, hcapacity', hno⟩
  · refine Or.inl ⟨heBody, ?_⟩
    refine ⟨by simp, by simpa using h905', hinput', Or.inr ⟨by simpa using hgo',
      newEnds, newRots, newPaths, H, M, next, true, d + 1, r, records ++ [record], newTail,
      ?_, run', trace', nextCore.setCounter (i + 1), hinj', hbits', hcapacity'⟩⟩
    omega

end GraphMinor.Compute
