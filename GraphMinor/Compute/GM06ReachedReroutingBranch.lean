module

public import GraphMinor.Compute.GM06ReachedReduction4Phase
import GraphMinor.GM06.Alg57CurrentReduction4Phase
import GraphMinor.GM06.Alg57OnePathPhase
import GraphMinor.GM06.Alg57OnePathEncoded
import GraphMinor.GM06.Section5SinglePathReduction4Progress

/-!
# The actual rerouting branch of VI (5.7) for every positive path count

After all early scans fail, the reference bit is one. The complete
Reduction 4 phase executes on the reached core. Its computed output
is sound and complete for the current drawing. This file calls
the proved geometric links for one path and for at least two paths.

A success therefore gives a real new reference linkage, its full
current representation, and the extended forward and inverse
histories. The actual RAM measure falls by one. A failure excludes
all four reductions, preserves the old core, and leaves the terminal
branch ready. No phase correctness result is a hypothesis.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- At a failed phase, the already failed early scans and the proved
phase completeness exclude every reduction. For one path, the
valency-one case follows directly from failure of Reduction 3. -/
private theorem no_reduction_of_failed_phase
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder} {θ : ℝ}
    {L : CylinderLinkage k G} (cur : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
      ¬ Section5Reduction1Step k G L H M ∧ ¬ Section5Reduction2Step k G L H M ∧
        ¬ Section5Reduction3Step k G L H M)
    (hb : (gm06Reduction4Phase x cur.tagged.length).1 = false) :
    ¬ Section5AnyReductionApplies k G L := by
  have hno1 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
      IsCylinderSection5Drawing k H → ¬ Section5Reduction1Step k G L H M :=
    fun H M _ => (hno H M).1
  have hno2 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
      IsCylinderSection5Drawing k H → ¬ Section5Reduction2Step k G L H M :=
    fun H M _ => (hno H M).2.1
  have hno4 : ¬ ∃ M : CylinderLinkage k G, Section5Reduction4Step k G L G M := by
    by_cases hk : 1 < k
    · exact cur.reduction4Phase_complete hk hG hno2 hθ hb
    · have hk1 : k = 1 := by have := hG.1; omega
      subst k
      by_cases hv : vertexValency G.toGraph (cylinderM1Point 1 0) = 1
      · rintro ⟨M, hr⟩
        exact not_reduction4_of_one_valency_one_no_reduction3 L M hG hv
          (fun H M _ => (hno H M).2.2) hr
      · exact cur.reduction4Phase_one_complete hG hno1 hno2 hv hθ hb
  rintro ⟨H, M, _, step⟩
  rcases step with h1 | h2 | h3 | h4
  · exact (hno H M).1 h1
  · exact (hno H M).2.1 h2
  · exact (hno H M).2.2 h3
  · have hHG : H = G := h4.1
    subst H
    exact hno4 ⟨M, h4⟩

/-- Execute and interpret the complete reached Reduction 4 phase
for every positive `k`. A successful phase executes the following success
guard, leaving the terminal command untouched. A failed phase returns
the exact no-reduction condition used by the terminal criterion. -/
theorem gm06Reached_rerouting_branch
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder} {θ : ℝ}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    (hinit : initial.tagged = input.graph.initialTagged)
    (hG₀ : IsCylinderSection5Drawing k G₀) (hθ₀ : L₀.HasTheta θ)
    {ends : List ℕ} {rots paths : List (List ℕ)}
    {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} G L)
    (hvinj : Function.Injective cur.vertex) {d r : ℕ}
    (run : Alg57ReductionRun ⟨G₀, L₀, true⟩ ⟨G, L, true⟩ d r)
    {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records)
    (hno : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
      ¬ Section5Reduction1Step k G L H M ∧ ¬ Section5Reduction2Step k G L H M ∧
        ¬ Section5Reduction3Step k G L H M)
    {tail : List ℕ} (terminalPhase : Cmd) (s : State)
    (core : GM06SuccessorCoreRep cur true records tail s) :
    let y := {x with endpoints := ends, rotations := rots, linkage := paths}
    let rows := (gm06Reduction4Phase y cur.tagged.length).2
    ∃ sf t, Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06Reduction4PhaseProg s sf t ∧
      t ≤ 20971520000000 * (gm06SuccessorInputSize x + 1) ^ 4 ∧
      Keeps gm06Reduction4PhaseRegs gm06Reduction4PhaseArrs s sf ∧
      ((sf.regs 646 = 0 ∧ GM06SuccessorCoreRep cur true records tail sf ∧
          ¬ Section5AnyReductionApplies k G L) ∨
       ∃ (M : CylinderLinkage k G)
         (hrows : GM06LinkageRowsEncoding M cur.tagged cur.vertex cur.edge rows),
         let next := cur.withLinkage M rows hrows
         sf.regs 646 = 1 ∧
         Exec (wordSize 32 (gm06SuccessorInputSize x))
           (.seq gm06Reduction4PhaseProg (.ite (.reg 646) .skip
             (gm06FinishSuccessorProg terminalPhase))) s sf (t + 2) ∧
         Section5Reduction4Step k G L G M ∧ GM06SuccessorCoreRep next false (records ++ [none]) tail sf ∧
         Function.Injective next.vertex ∧
         Alg57ReductionRun ⟨G₀, L₀, true⟩ ⟨G, M, false⟩ d (r + 1) ∧
         GM06UndoTrace x.vertexCount k initial.undoState next.undoState (records ++ [none]) ∧
         M.HasTheta θ ∧
         (IsThetaFeasible k G (θ + 1 / (k : ℝ)) ↔
           IsThetaFeasible k G₀ (θ + 1 / (k : ℝ))) ∧
         gm06LoopMeasure sf + 1 = gm06LoopMeasure s) := by
  let y := {x with endpoints := ends, rotations := rots, linkage := paths}
  let rows := (gm06Reduction4Phase y cur.tagged.length).2
  obtain ⟨hG, hθ, _⟩ := run.invariant hG₀ hθ₀
  have hno2 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
      IsCylinderSection5Drawing k H → ¬ Section5Reduction2Step k G L H M :=
    fun H M _ => (hno H M).2.1
  obtain ⟨sf, t, he, ht, hf, hflag, h8, hbit, hfailure⟩ :=
    gm06Reduction4PhaseProg_reached input initial hinit cur trace hG s core
  change sf.regs 646 = (if (gm06Reduction4Phase y cur.tagged.length).1 then 1 else 0) at hflag
  change sf.arrs 8 = gm06EncodeRows rows at h8
  change sf.regs 329 = (if (gm06Reduction4Phase y cur.tagged.length).1 then 0 else true.toNat) at hbit
  refine ⟨sf, t, he, ht, hf, ?_⟩
  cases hb : (gm06Reduction4Phase y cur.tagged.length).1 with
  | false =>
    have hflag' : sf.regs 646 = 0 := by simpa only [hb, Bool.false_eq_true, ite_false] using hflag
    have hcore := hfailure hb
    exact Or.inl ⟨hflag', hcore, no_reduction_of_failed_phase cur hG hθ hno hb⟩
  | true =>
    have hflag' : sf.regs 646 = 1 := by simpa only [hb, ite_true] using hflag
    have hbit' : sf.regs 329 = 0 := by simpa only [hb, ite_true] using hbit
    obtain ⟨M, step, hrows⟩ : ∃ M : CylinderLinkage k G,
        Section5Reduction4Step k G L G M ∧
          GM06LinkageRowsEncoding M cur.tagged cur.vertex cur.edge rows := by
      by_cases hk : 1 < k
      · exact cur.reduction4Phase_sound hk hG hno2 hθ hb
      · have hk1 : k = 1 := by have := hG.1; omega
        subst k
        exact cur.reduction4Phase_one_sound_rows hG hno2 hθ hb
    change GM06LinkageRowsEncoding M cur.tagged cur.vertex cur.edge rows at hrows
    let next := cur.withLinkage M rows hrows
    have hcore : GM06SuccessorCoreRep next false (records ++ [none]) tail sf :=
      core.rerouting M rows hrows he h8 hbit'
    obtain ⟨hinj, _, _, run', trace', hθ', hfeas, _, _⟩ :=
      gm06Rerouting_current_invariant cur hvinj ⟨G₀, L₀, true⟩ hG₀ hθ₀ run
        initial.undoState records trace M step rows hrows
    obtain ⟨_, _, _, _, hmeasure, _, _, _, _⟩ :=
      gm06Reduction4PhaseProg_rerouting_state cur M rows hrows he h8 hbit' core.active core.live core.bit
    obtain ⟨hw, _, _, _, _, _⟩ := input.initial_word_caps hG₀
    have heBranch : Exec (wordSize 32 (gm06SuccessorInputSize x))
        (.seq gm06Reduction4PhaseProg (.ite (.reg 646) .skip
          (gm06FinishSuccessorProg terminalPhase))) s sf (t + 2) :=
      .seq he (.ite_true (Crossing.eval_reg hflag' (by omega)) one_ne_zero (.skip _))
    exact Or.inr ⟨M, hrows, hflag', heBranch, step, hcore, hinj, run', trace', hθ', hfeas, hmeasure⟩

end GraphMinor.Compute
