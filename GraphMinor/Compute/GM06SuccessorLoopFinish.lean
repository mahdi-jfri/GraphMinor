module

public import GraphMinor.Compute.GM06SuccessorLoopControl
public import GraphMinor.Compute.GM06ReachableBounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Stopping and preserving the answer in VI (5.7)

After all four reductions fail, the active valency test decides
next-winding feasibility in the reached drawing. In its negative
case the loop returns zero without running the witness phase.
The actual reduction history transfers that answer to the input.

Once the continuation flag is zero, the remaining fixed-fuel
iterations only advance the outer counter. They preserve every
array and every other register, including the answer and recovered
path rows. The early driver also preserves the input and the two
outer control registers by its literal command's write frame.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem early_control_not_written :
    (904 : Reg) ∉ gm06EarlyReductionsProg.writtenRegs ∧
      (905 : Reg) ∉ gm06EarlyReductionsProg.writtenRegs ∧
      (0 : Arr) ∉ gm06EarlyReductionsProg.writtenArrs := by decide

/-- The early driver preserves the original input and the outer
continuation and fuel registers on every actual execution. -/
theorem gm06EarlyReductionsProg_control_frame {w t : ℕ} {s sf : State}
    (he : Exec w gm06EarlyReductionsProg s sf t) :
    sf.arrs 0 = s.arrs 0 ∧ sf.regs 904 = s.regs 904 ∧ sf.regs 905 = s.regs 905 := by
  exact ⟨he.arrs_eq_of_not_mem_writtenArrs early_control_not_written.2.2,
    he.regs_eq_of_not_mem_writtenRegs early_control_not_written.1,
    he.regs_eq_of_not_mem_writtenRegs early_control_not_written.2.1⟩

/-- The negative terminal branch executes the actual active-valency
test, returns infeasibility in the original drawing, and clears the
continuation flag. No instruction of the witness phase is executed. -/
theorem gm06FinishSuccessorProg_negative
    {w k : ℕ} {x y : GM06SuccessorInput} {G₀ G : Drawing ClosedCylinder} {θ : ℝ}
    {L₀ : CylinderLinkage k G₀} {L : CylinderLinkage k G}
    (input : GM06SuccessorInputRep x G₀ L₀) (cur : GM06CurrentDrawingRep y G L)
    (hvinj : Function.Injective cur.vertex)
    (hG₀ : IsCylinderSection5Drawing k G₀) (hθ₀ : L₀.HasTheta θ)
    {b : Bool} {d r : ℕ} (run : Alg57ReductionRun ⟨G₀, L₀, true⟩ ⟨G, L, b⟩ d r)
    (hno : ¬ Section5AnyReductionApplies k G L)
    (hnegative : ¬ IsThetaFeasible k G (θ + 1 / (k : ℝ)))
    (terminalPhase : Cmd) (s : State)
    (hw : 2 < 2 ^ w) (hn : y.vertexCount < 2 ^ w)
    (hm : 2 * cur.tagged.length < 2 ^ w) (hk : k < 2 ^ w)
    (hbits : ∀ p ∈ cur.tagged, p.2 ≤ 1)
    (h3 : s.arrs 3 = y.endpoints) (h6 : s.arrs 6 = y.innerCuff)
    (h12 : s.arrs 12 = cur.tagged.map Prod.snd) :
    ∃ sf t, Exec w (gm06FinishSuccessorProg terminalPhase) s sf t ∧
      t ≤ 19 + k * (22 + 42 * cur.tagged.length) ∧
      Keeps [0, 20, 21, 22, 902, 903, 904] [] s sf ∧
      sf.regs 0 = 0 ∧ sf.regs 904 = 0 ∧
      GM06SuccessorOutputRep input θ (sf.regs 0) (sf.arrs 8) := by
  obtain ⟨hG, hθ, hfeas⟩ := run.invariant hG₀ hθ₀
  obtain ⟨sm, t, he, ht, hf, hbit, hgood⟩ :=
    gm06CurrentTerminalTestProg_current cur hvinj hG hθ hno s hw hn hm hk hbits h3 h6 h12
  have hzero : sm.regs 0 = 0 := hbit.resolve_right (fun h => hnegative (hgood.mp h))
  have hskip : Exec w (.ite (.reg 0) (.seq terminalPhase gm06RecoverContractionsProg) .skip)
      sm sm 2 := .ite_false (Crossing.eval_reg hzero (Nat.two_pow_pos w)) (.skip _)
  let sf := sm.setReg 904 0
  have hstop : Exec w (.assign 904 (.const 0)) sm sf 2 :=
    .assign (Crossing.eval_const (Nat.two_pow_pos w))
  have hframe : Keeps [0, 20, 21, 22, 902, 903, 904] [] s sf := by
    constructor
    · intro a ha
      have hnot : a ∉ [0, 20, 21, 22, 902, 903] := by
        intro hm
        exact ha (List.mem_append_left [904] hm)
      have hne : a ≠ 904 := by intro h; subst a; exact ha (by simp)
      exact (State.setReg_regs_ne _ _ hne).trans (hf.1 a hnot)
    · exact hf.2
  have hzero' : sf.regs 0 = 0 := by simpa [sf] using hzero
  refine ⟨sf, t + (2 + 2), .seq he (.seq hskip hstop), by omega, hframe,
    hzero', by simp [sf], Or.inl ⟨hzero', ?_⟩⟩
  exact fun h => hnegative (hfeas.mpr h)

/-- The active-valency terminal decision, including its stopping
instructions, has a uniform quadratic bound in the original size. -/
theorem gm06FinishSuccessorProg_negative_cost
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    (hinit : initial.tagged = input.graph.initialTagged)
    {ends : List ℕ} {rots paths : List (List ℕ)}
    {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} G L)
    {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records) :
    19 + k * (22 + 42 * cur.tagged.length) ≤ 80 * (gm06SuccessorInputSize x + 1) ^ 2 := by
  have htag := gm06Reached_tagged_length input initial hinit cur trace
  obtain ⟨_, hm, hk, _, _, _⟩ := input.size_bounds
  rw [htag]
  calc
    _ ≤ 19 + gm06SuccessorInputSize x * (22 + 42 * gm06SuccessorInputSize x) := by gcongr
    _ ≤ _ := by nlinarith

/-- All remaining fixed-fuel rounds after an answer only advance
register 900. In particular, no reduction or terminal phase runs,
and all arrays and the output bit are preserved. -/
theorem gm06SuccessorLoop_idle_suffix
    {w N i : ℕ} (reduction4Phase terminalPhase : Cmd) (s : State)
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w) (hi : i ≤ N)
    (h900 : s.regs 900 = i) (h904 : s.regs 904 = 0) (h905 : s.regs 905 = N) :
    ∃ sf t, Exec w (forUp 900 (.reg 905)
      (.ite (.reg 904) (gm06SuccessorLoopBody reduction4Phase terminalPhase) .skip)) s sf t ∧
      t ≤ 3 + (N - i) * 9 ∧ Keeps [900] [] s sf ∧
      sf.regs 900 = N ∧ sf.regs 904 = 0 ∧ sf.regs 905 = N := by
  let I (j : ℕ) (st : State) : Prop :=
    Keeps [900] [] s st ∧ st.regs 900 = j ∧ st.regs 904 = 0 ∧ st.regs 905 = N
  obtain ⟨sf, t, he, ht, hI⟩ := Crossing.forUp_exec I (fun _ => 0) N 2 hw hN
    (r_i := 900) (hi := .reg 905)
    (fun j _ st hj => ⟨hj.2.1, Crossing.eval_reg hj.2.2.2 hN⟩)
    (fun j _ st hj => by
      have hstep : Exec w (.ite (.reg 904)
          (gm06SuccessorLoopBody reduction4Phase terminalPhase) .skip) st st 2 :=
        .ite_false (Crossing.eval_reg hj.2.2.1 (Nat.two_pow_pos w)) (.skip _)
      refine ⟨st, 2, hstep, by simp, ?_, hj.2.1⟩
      exact ⟨hj.1.setReg (by simp) _, by simp, by simpa using hj.2.2.1,
        by simpa using hj.2.2.2⟩)
    i hi s ⟨Keeps.refl _ _ _, h900, h904, h905⟩
  exact ⟨sf, t, he, by simpa only [Expr.cost, Nat.add_zero, Nat.reduceAdd] using ht, hI⟩

/-- A successor output already produced by the loop remains a
successor output after its idle fixed-fuel suffix. -/
theorem gm06SuccessorOutputRep_idle {k : ℕ} {x : GM06SuccessorInput}
    {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    (input : GM06SuccessorInputRep x G L) (θ : ℝ) {s sf : State}
    (hframe : Keeps [900] [] s sf)
    (hout : GM06SuccessorOutputRep input θ (s.regs 0) (s.arrs 8)) :
    GM06SuccessorOutputRep input θ (sf.regs 0) (sf.arrs 8) := by
  rw [hframe.1 0 (by decide), hframe.2 8 (by decide)]
  exact hout

end GraphMinor.Compute
