module

public import GraphMinor.Compute.GM06Algorithm57
public import GraphMinor.Compute.GM06SuccessorLoopInvariant
public import GraphMinor.Compute.GM06ReachedTerminalDecision
public import GraphMinor.Compute.GM06ReachedReduction4Phase
import GraphMinor.Compute.GM06TerminalPhaseExec
import GraphMinor.GM06.Alg57CurrentTerminalPhase
import GraphMinor.GM06.Alg57OnePathTerminalPhase
import GraphMinor.GM06.Section5TerminalFeasibility

/-!
# The concrete terminal branch of VI (5.7)

The whole terminal command executes on the current core with the
original logarithmic words and a uniform cubic time bound. Its
write frame turns the computed successor rows into the same core
with a new reference linkage and unchanged inverse records.

The proved drawing links for one path and for at least two paths
identify those rows with an actual next-winding linkage. The complete terminal
branch first runs the valency test. A negative answer stops. A
positive answer calls the whole terminal command and actual UNDO,
then stops with the original-label output. Both cases establish
the answered outer invariant after the counter increment.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- The actual whole terminal phase executes at any reached proper
core, with its exact pure rows, answer one and original-size cubic
bound. No phase execution or word-bound premise is supplied. -/
theorem gm06TerminalPhaseProg_reached
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    (hinit : initial.tagged = input.graph.initialTagged)
    {ends : List ℕ} {rots paths : List (List ℕ)}
    {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} G L)
    {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records)
    (hG : IsCylinderSection5Drawing k G) {b : Bool} {tail : List ℕ} (s : State)
    (core : GM06SuccessorCoreRep cur b records tail s) :
    let y := {x with endpoints := ends, rotations := rots, linkage := paths}
    ∃ sf t, Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06TerminalPhaseProg s sf t ∧
      t ≤ 327680000000 * (gm06SuccessorInputSize x + 1) ^ 3 ∧
      Keeps gm06TerminalPhaseRegs gm06TerminalPhaseArrs s sf ∧
      sf.arrs 8 = gm06EncodeRows (gm06TerminalPhase y cur.tagged.length) ∧ sf.regs 0 = 1 := by
  let y := {x with endpoints := ends, rotations := rots, linkage := paths}
  obtain ⟨he, hi, ho, hp, hrows, hnd⟩ := gm06Current_phase_lengths cur
  obtain ⟨hend, hd, hinner, houter, hkeys⟩ := gm06Current_phase_values cur hG
  have hcode := gm06Reached_phase_word_cap input initial hinit cur trace hG
  have hcount : y.linkage.length = y.innerCuff.length := hp.trans hi.symm
  have h12 : (s.arrs 12).length = cur.tagged.length := by rw [core.active, List.length_map]
  obtain ⟨sf, t, hex, ht, hf, h8, hbit⟩ := gm06TerminalPhaseProg_exec y s he hend hd hinner houter
    hcount hrows hnd hkeys hcode core.countReg h12 core.rotations core.endpoints core.linkage core.inner core.outer
  have htime := ht.trans (gm06Reached_phase_polynomial_le input initial hinit cur trace hG 10000000 3)
  exact ⟨sf, t, hex, by simpa only [Nat.reducePow, Nat.reduceMul] using htime, hf, h8, hbit⟩

/-- The terminal command's real write frame preserves all graph and
history fields when its computed rows encode the terminal witness. -/
theorem GM06SuccessorCoreRep.terminalWitness
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} {cur : GM06CurrentDrawingRep x G L}
    {b : Bool} {records : List (Option (ℕ × ℕ))} {tail : List ℕ} {s : State}
    (core : GM06SuccessorCoreRep cur b records tail s)
    (M : CylinderLinkage k G) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding M cur.tagged cur.vertex cur.edge rows)
    {w t : ℕ} {sf : State} (he : Exec w gm06TerminalPhaseProg s sf t)
    (h8 : sf.arrs 8 = gm06EncodeRows rows) :
    GM06SuccessorCoreRep (cur.withLinkage M rows hrows) b records tail sf := by
  have hf := gm06TerminalPhaseProg_frame he
  have ha (a : ℕ) (hm : a ∈ [2, 3, 4, 6, 7, 9, 12, 14]) : sf.arrs a = s.arrs a := by
    apply hf.2 a
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hr (q : ℕ) (hm : q ∈ [100, 309, 329]) : sf.regs q = s.regs q := by
    apply hf.1 q
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> decide
  exact ⟨(ha 2 (by simp)).trans core.count, (ha 3 (by simp)).trans core.endpoints,
    (ha 4 (by simp)).trans core.rotations, (ha 6 (by simp)).trans core.inner,
    (ha 7 (by simp)).trans core.outer, h8, (ha 9 (by simp)).trans core.history,
    (ha 12 (by simp)).trans core.active, (ha 14 (by simp)).trans core.live,
    (hr 100 (by simp)).trans core.countReg, (hr 309 (by simp)).trans core.historyReg,
    (hr 329 (by simp)).trans core.bit⟩

private theorem terminal_positive_time {a b c N : ℕ}
    (ha : a ≤ 80 * (N + 1) ^ 2) (hb : b ≤ 327680000000 * (N + 1) ^ 3)
    (hc : c ≤ 2000 * (N + 1) ^ 2) :
    a + ((1 + (b + c)) + 2) ≤ 327680000000 * (N + 1) ^ 3 + 2080 * (N + 1) ^ 2 + 3 := by
  omega

private theorem terminal_negative_time {a N : ℕ} (ha : a ≤ 80 * (N + 1) ^ 2) :
    a + (2 + 2) ≤ 327680000000 * (N + 1) ^ 3 + 2080 * (N + 1) ^ 2 + 3 := by
  have hp : 1 ≤ (N + 1) ^ 2 := one_le_pow₀ (by omega : 1 ≤ N + 1)
  omega

/-- The whole concrete terminal branch executes and returns the public
original-label output for every positive `k`. A positive decision calls the actual
whole witness phase and actual UNDO. Both outcomes clear flag 904 and
establish the answered outer invariant. -/
theorem gm06Algorithm57_terminal
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder} {θ : ℝ}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    (hinit : initial.tagged = input.graph.initialTagged)
    (hvertex : initial.vertex = input.graph.vertexLabels)
    (hedge : HEq initial.edge input.graph.edgeLabels)
    (hG₀ : IsCylinderSection5Drawing k G₀) (hθ₀ : L₀.HasTheta θ)
    {ends : List ℕ} {rots paths : List (List ℕ)}
    {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} G L)
    (hvinj : Function.Injective cur.vertex) (hbits : ∀ p ∈ cur.tagged, p.2 ≤ 1)
    {d r : ℕ} (run : Alg57ReductionRun ⟨G₀, L₀, true⟩ ⟨G, L, true⟩ d r)
    {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records)
    (hno : ¬ Section5AnyReductionApplies k G L) {tail : List ℕ} {i : ℕ} (s : State)
    (core : GM06SuccessorCoreRep cur true records tail s)
    (hcapacity : (s.arrs 9).length = 2 * (x.vertexCount + G₀.E.ncard))
    (h900 : s.regs 900 = i) (h905 : s.regs 905 = 2 * (x.vertexCount + G₀.E.ncard) + 1)
    (hinput : s.arrs 0 = gm06EncodeSuccessorInput x) :
    ∃ sf t, Exec (wordSize 32 (gm06SuccessorInputSize x))
        (gm06FinishSuccessorProg gm06TerminalPhaseProg) s sf t ∧
      t ≤ 327680000000 * (gm06SuccessorInputSize x + 1) ^ 3 +
        2080 * (gm06SuccessorInputSize x + 1) ^ 2 + 3 ∧
      sf.regs 900 = i ∧ sf.regs 905 = 2 * (x.vertexCount + G₀.E.ncard) + 1 ∧ sf.regs 904 = 0 ∧
      sf.arrs 0 = gm06EncodeSuccessorInput x ∧ GM06SuccessorOutputRep input θ (sf.regs 0) (sf.arrs 8) ∧
      gm06SuccessorLoopInvariant input θ initial (i + 1) (sf.setReg 900 (i + 1)) := by
  let y := {x with endpoints := ends, rotations := rots, linkage := paths}
  obtain ⟨hG, hθ, hfeas⟩ := run.invariant hG₀ hθ₀
  have hw1 : 1 < 2 ^ wordSize 32 (gm06SuccessorInputSize x) :=
    (by decide : 1 < 3).trans (input.initial_word_caps hG₀).1
  obtain ⟨sd, td, hed, htd, cored, hd0, hdr, hdbit, hdyes, hdno⟩ :=
    gm06Reached_terminal_decision input initial hinit hG₀ hθ₀ cur hvinj hbits true run trace hno s core
  have hd900 := (hdr 900 (by simp)).trans h900
  have hd905 := (hdr 905 (by simp)).trans h905
  have hdinput := hd0.trans hinput
  rcases hdbit with hzero | hone
  · let sf := sd.setReg 904 0
    have heIf : Exec (wordSize 32 (gm06SuccessorInputSize x))
        (.ite (.reg 0) (.seq gm06TerminalPhaseProg gm06RecoverContractionsProg) .skip) sd sd 2 :=
      .ite_false (Crossing.eval_reg hzero (Nat.two_pow_pos _)) (.skip _)
    have heStop : Exec (wordSize 32 (gm06SuccessorInputSize x)) (.assign 904 (.const 0)) sd sf 2 :=
      .assign (Crossing.eval_const (Nat.two_pow_pos _))
    have hout : GM06SuccessorOutputRep input θ (sf.regs 0) (sf.arrs 8) := by
      refine Or.inl ⟨?_, hdno.mp hzero⟩
      simpa only [sf, State.setReg_regs_ne _ _ (by decide : (0 : Reg) ≠ 904)] using hzero
    have hsf900 : sf.regs 900 = i := by simpa [sf] using hd900
    have hsf905 : sf.regs 905 = 2 * (x.vertexCount + G₀.E.ncard) + 1 := by simpa [sf] using hd905
    have hsfstop : sf.regs 904 = 0 := by simp [sf]
    refine ⟨sf, td + (2 + 2), .seq hed (.seq heIf heStop), terminal_negative_time htd,
      hsf900, hsf905, hsfstop, hdinput, hout, ?_⟩
    exact ⟨by simp, by simpa using hsf905, hdinput,
      Or.inl ⟨by simpa using hsfstop, by simpa using hout⟩⟩
  · have hval := (isThetaFeasible_next_iff_no_initial_valency_one L hG hθ hno).mp
      (hfeas.mpr (hdyes.mp hone))
    obtain ⟨M, hM, _, hrows⟩ : ∃ M : CylinderLinkage k G,
        M.HasTheta (θ + 1 / (k : ℝ)) ∧
          (∀ i, M.curve i 1 = L.curve (finSuccCycle i) 1) ∧
          GM06LinkageRowsEncoding M cur.tagged cur.vertex cur.edge
            (gm06TerminalPhase y cur.tagged.length) := by
      by_cases hk : 1 < k
      · exact cur.terminalPhase_linkage_phase hk hG hno hval hθ
      · have hk1 : k = 1 := by have := hG.1; omega
        subst k
        rw [gm06TerminalPhase_eq_successorRows]
        exact cur.terminalPhase_one_linkage hG hno hval hθ
    let rows := gm06TerminalPhase y cur.tagged.length
    change GM06LinkageRowsEncoding M cur.tagged cur.vertex cur.edge rows at hrows
    obtain ⟨sp, tp, hep, htp, hfp, hp8, hpbit⟩ :=
      gm06TerminalPhaseProg_reached input initial hinit cur trace hG sd cored
    change sp.arrs 8 = gm06EncodeRows rows at hp8
    let next := cur.withLinkage M rows hrows
    have corep : GM06SuccessorCoreRep next true records tail sp := cored.terminalWitness M rows hrows hep hp8
    have hcapacityp : (sp.arrs 9).length = 2 * (x.vertexCount + G₀.E.ncard) := by
      rw [hfp.2 9 (by decide), cored.history, ← core.history]
      exact hcapacity
    obtain ⟨su, tu, heu, htu, _, _, _, houtu, hu0, hur⟩ :=
      gm06RecoverContractionsProg_reached input initial hinit hvertex hedge hG₀ next hM trace sp corep
        hcapacityp hpbit
    let sf := su.setReg 904 0
    have heIf : Exec (wordSize 32 (gm06SuccessorInputSize x))
        (.ite (.reg 0) (.seq gm06TerminalPhaseProg gm06RecoverContractionsProg) .skip)
        sd su (1 + (tp + tu)) :=
      .ite_true (Crossing.eval_reg hone hw1) one_ne_zero (.seq hep heu)
    have heStop : Exec (wordSize 32 (gm06SuccessorInputSize x)) (.assign 904 (.const 0)) su sf 2 :=
      .assign (Crossing.eval_const (Nat.two_pow_pos _))
    have hout : GM06SuccessorOutputRep input θ (sf.regs 0) (sf.arrs 8) := by simpa [sf] using houtu
    have hu900 : su.regs 900 = i := (hur 900 (by simp)).trans ((hfp.1 900 (by decide)).trans hd900)
    have hu905 : su.regs 905 = 2 * (x.vertexCount + G₀.E.ncard) + 1 :=
      (hur 905 (by simp)).trans ((hfp.1 905 (by decide)).trans hd905)
    have huinput : su.arrs 0 = gm06EncodeSuccessorInput x := hu0.trans ((hfp.2 0 (by decide)).trans hdinput)
    have hsf900 : sf.regs 900 = i := by simpa [sf] using hu900
    have hsf905 : sf.regs 905 = 2 * (x.vertexCount + G₀.E.ncard) + 1 := by simpa [sf] using hu905
    have hsfstop : sf.regs 904 = 0 := by simp [sf]
    refine ⟨sf, td + ((1 + (tp + tu)) + 2), .seq hed (.seq heIf heStop),
      terminal_positive_time htd htp htu, hsf900, hsf905, hsfstop, huinput, hout, ?_⟩
    exact ⟨by simp, by simpa using hsf905, huinput,
      Or.inl ⟨by simpa using hsfstop, by simpa using hout⟩⟩

end GraphMinor.Compute
