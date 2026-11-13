module

public import GraphMinor.Compute.GM06SuccessorCoreState
public import GraphMinor.Compute.GM06ReachedEarlyRound

/-!
# Preserving the complete core through an early loop round

The actual early-round theorem executes the three scans with all
word and history bounds derived from the original input. This file
collects its resulting array equalities into the core assertion.
Register 100 is read from the command itself, so a failed early
round still supplies the original count to the Reduction 4 phase.

Every successful early branch has a new actual drawing and linkage,
a full core with bit one, and extended forward and inverse histories.
The history buffer keeps its original capacity. If all scans fail,
the core is unchanged and its bit is one. These are the two states
that the outer loop's proof uses before its next control branch.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- The actual reached early driver preserves the complete core and
both histories. All memory premises are interpretations of the reached
state; all numerical side conditions are derived inside the proof. -/
theorem gm06Reached_early_core
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder} {θ : ℝ}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    (hinit : initial.tagged = input.graph.initialTagged)
    (hG₀ : IsCylinderSection5Drawing k G₀) (hθ₀ : L₀.HasTheta θ)
    {oldEnds : List ℕ} {oldRots oldPaths : List (List ℕ)}
    {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    (cur : GM06CurrentDrawingRep
      {x with endpoints := oldEnds, rotations := oldRots, linkage := oldPaths} G L)
    (hvinj : Function.Injective cur.vertex) (hbits : ∀ p ∈ cur.tagged, p.2 ≤ 1)
    (b : Bool) {d r : ℕ} (run : Alg57ReductionRun ⟨G₀, L₀, true⟩ ⟨G, L, b⟩ d r)
    (records : List (Option (ℕ × ℕ)))
    (trace : GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records)
    (tail : List ℕ) (reduction4Phase terminalPhase : Cmd) (s : State)
    (core : GM06SuccessorCoreRep cur b records tail s)
    (hcapacity : (s.arrs 9).length = 2 * (x.vertexCount + G₀.E.ncard)) :
    ∃ sf t,
      Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06EarlyReductionsProg s sf t ∧
      t ≤ 5062500000 * (gm06SuccessorInputSize x + 1) ^ 4 ∧
      (∀ a ∈ [0, 2, 6, 7], sf.arrs a = s.arrs a) ∧
      (∀ q ∈ [900, 904, 905], sf.regs q = s.regs q) ∧
      ((sf.regs 901 = 0 ∧ b = true ∧ GM06SuccessorCoreRep cur true records tail sf ∧
          ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
            ¬ Section5Reduction1Step k G L H M ∧
            ¬ Section5Reduction2Step k G L H M ∧
            ¬ Section5Reduction3Step k G L H M) ∨
       ∃ (ends : List ℕ) (rots paths : List (List ℕ))
         (H : Drawing ClosedCylinder) (M : CylinderLinkage k H)
         (next : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} H M)
         (record : Option (ℕ × ℕ)) (newTail : List ℕ),
         Exec (wordSize 32 (gm06SuccessorInputSize x))
           (gm06SuccessorLoopBody reduction4Phase terminalPhase) s sf (t + 2) ∧
         sf.regs 901 ∈ [1, 2, 3] ∧
         GM06SuccessorCoreRep next true (records ++ [record]) newTail sf ∧
         Function.Injective next.vertex ∧ (∀ p ∈ next.tagged, p.2 ≤ 1) ∧
         IsCylinderSection5Drawing k H ∧
         Alg57ReductionRun ⟨G₀, L₀, true⟩ ⟨H, M, true⟩ (d + 1) r ∧
         GM06UndoTrace x.vertexCount k initial.undoState next.undoState (records ++ [record]) ∧
         gm06LoopMeasure sf < gm06LoopMeasure s ∧
         (sf.arrs 9).length = 2 * (x.vertexCount + G₀.E.ncard)) := by
  obtain ⟨sf, t, he, ht, ha, hr, hout⟩ := gm06Reached_early_round input initial hinit hG₀ hθ₀ cur hvinj hbits
    b run records trace tail reduction4Phase terminalPhase s core.count core.endpoints core.rotations
    core.inner core.outer core.linkage core.history hcapacity core.active core.live core.historyReg core.bit
  have h100 := gm06EarlyReductionsProg_original_count he core.count
  refine ⟨sf, t, he, ht, ha, hr, ?_⟩
  rcases hout with ⟨hflag, hbit, hb, hcount, hsame, hno⟩ |
      ⟨ends, rots, paths, H, M, next, record, newTail, heBody, hflag, hbit,
        h3, h4, h8, h12, h14, hinj, _, hbits', hH, run', trace', _, _, hmeasure, hcount, h9, hcap⟩
  · refine Or.inl ⟨hflag, hb, ?_, hno⟩
    exact ⟨(ha 2 (by simp)).trans core.count,
      (hsame 3 (by simp)).trans core.endpoints, (hsame 4 (by simp)).trans core.rotations,
      (ha 6 (by simp)).trans core.inner, (ha 7 (by simp)).trans core.outer,
      (hsame 8 (by simp)).trans core.linkage, (hsame 9 (by simp)).trans core.history,
      (hsame 12 (by simp)).trans core.active, (hsame 14 (by simp)).trans core.live,
      h100, hcount, hbit⟩
  · have nextCore : GM06SuccessorCoreRep next true (records ++ [record]) newTail sf :=
      ⟨(ha 2 (by simp)).trans core.count, h3, h4, (ha 6 (by simp)).trans core.inner,
        (ha 7 (by simp)).trans core.outer, h8, h9, h12, h14, h100, hcount, hbit⟩
    exact Or.inr ⟨ends, rots, paths, H, M, next, record, newTail, heBody, hflag,
      nextCore, hinj, hbits', hH, run', trace', hmeasure, hcap.trans hcapacity⟩

end GraphMinor.Compute
