module

public import GraphMinor.Compute.GM06SuccessorCoreState
import GraphMinor.Compute.GM06SuccessorLoopFinish
import GraphMinor.Compute.GM06ReachableBounds
import GraphMinor.Compute.GM06RecoverSuccessorOutput

/-!
# Reached terminal decision and recovery in VI (5.7)

Once all four reductions have failed, the active valency test decides
the next-winding question. The actual forward history identifies that
question with the original input question. All machine-word bounds
follow from the original input and inverse history.

The test preserves every current array and the graph, history and
bit registers. Thus the positive case supplies the same current core
to the terminal witness phase. The negative bit already certifies the
public infeasibility answer. The original-size time bound is quadratic.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

private theorem terminal_time_le {t k m B : ℕ}
    (ht : t ≤ 15 + k * (22 + 42 * m)) (hB : 19 + k * (22 + 42 * m) ≤ B) : t ≤ B := by
  omega

/-- The actual terminal decision at a reached core returns zero
exactly for original-input infeasibility, and one exactly for original
feasibility. The core and outer controls are preserved, with no extra
word-bound or terminal-correctness premises. -/
theorem gm06Reached_terminal_decision
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder} {θ : ℝ}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    (hinit : initial.tagged = input.graph.initialTagged)
    (hG₀ : IsCylinderSection5Drawing k G₀) (hθ₀ : L₀.HasTheta θ)
    {ends : List ℕ} {rots paths : List (List ℕ)}
    {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} G L)
    (hvinj : Function.Injective cur.vertex) (hbits : ∀ p ∈ cur.tagged, p.2 ≤ 1)
    (b : Bool) {d r : ℕ} (run : Alg57ReductionRun ⟨G₀, L₀, true⟩ ⟨G, L, b⟩ d r)
    {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records)
    (hno : ¬ Section5AnyReductionApplies k G L) {tail : List ℕ} (s : State)
    (core : GM06SuccessorCoreRep cur b records tail s) :
    ∃ sf t, Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06CurrentTerminalTestProg s sf t ∧
      t ≤ 80 * (gm06SuccessorInputSize x + 1) ^ 2 ∧
      GM06SuccessorCoreRep cur b records tail sf ∧ sf.arrs 0 = s.arrs 0 ∧
      (∀ q ∈ [900, 904, 905], sf.regs q = s.regs q) ∧
      (sf.regs 0 = 0 ∨ sf.regs 0 = 1) ∧
      (sf.regs 0 = 1 ↔ IsThetaFeasible k G₀ (θ + 1 / (k : ℝ))) ∧
      (sf.regs 0 = 0 ↔ ¬ IsThetaFeasible k G₀ (θ + 1 / (k : ℝ))) := by
  obtain ⟨hG, hθ, hfeas⟩ := run.invariant hG₀ hθ₀
  obtain ⟨hw, _, hbudget, _, _, _⟩ := input.initial_word_caps hG₀
  have htag := gm06Reached_tagged_length input initial hinit cur trace
  have hm : 2 * cur.tagged.length < 2 ^ wordSize 32 (gm06SuccessorInputSize x) := by
    rw [htag]; omega
  have hw2 : 2 < 2 ^ wordSize 32 (gm06SuccessorInputSize x) := by omega
  have hn : x.vertexCount < 2 ^ wordSize 32 (gm06SuccessorInputSize x) := by omega
  have hk : k < 2 ^ wordSize 32 (gm06SuccessorInputSize x) := by omega
  obtain ⟨sf, t, he, ht, hf, hbit, hgood⟩ := gm06CurrentTerminalTestProg_current cur hvinj hG hθ hno s
    hw2 hn hm hk hbits core.endpoints core.inner core.active
  have ha (a : ℕ) : sf.arrs a = s.arrs a := hf.2 a (by simp)
  have hr (q : ℕ) (hq : q ∈ [100, 309, 329, 900, 904, 905]) : sf.regs q = s.regs q := by
    apply hf.1 q
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have core' : GM06SuccessorCoreRep cur b records tail sf :=
    ⟨(ha 2).trans core.count, (ha 3).trans core.endpoints, (ha 4).trans core.rotations,
      (ha 6).trans core.inner, (ha 7).trans core.outer, (ha 8).trans core.linkage,
      (ha 9).trans core.history, (ha 12).trans core.active, (ha 14).trans core.live,
      (hr 100 (by simp)).trans core.countReg, (hr 309 (by simp)).trans core.historyReg,
      (hr 329 (by simp)).trans core.bit⟩
  have htime := gm06FinishSuccessorProg_negative_cost input initial hinit cur trace
  have hgood' : sf.regs 0 = 1 ↔ IsThetaFeasible k G₀ (θ + 1 / (k : ℝ)) := hgood.trans hfeas
  refine ⟨sf, t, he, terminal_time_le ht htime, core', ha 0, ?_, hbit, hgood', ?_⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact hr _ (by simp)
  · constructor
    · intro hzero hyes
      have hone := hgood'.mpr hyes
      omega
    · intro hnot
      exact hbit.resolve_right (fun hone => hnot (hgood'.mp hone))

/-- RAM UNDO after an actual terminal witness produces the public
original-label output at the original logarithmic word size. The
stored history and initial label equalities are the ones already
proved by initialization and the loop; no word bounds are supplied. -/
theorem gm06RecoverContractionsProg_reached
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder} {θ : ℝ}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    (hinit : initial.tagged = input.graph.initialTagged)
    (hvertex : initial.vertex = input.graph.vertexLabels)
    (hedge : HEq initial.edge input.graph.edgeLabels)
    (hG₀ : IsCylinderSection5Drawing k G₀)
    {ends : List ℕ} {rots rows : List (List ℕ)}
    {G : Drawing ClosedCylinder} {M : CylinderLinkage k G}
    (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := rows} G M)
    (hM : M.HasTheta (θ + 1 / (k : ℝ))) {b : Bool}
    {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records)
    {tail : List ℕ} (s : State) (core : GM06SuccessorCoreRep cur b records tail s)
    (hcapacity : (s.arrs 9).length = 2 * (x.vertexCount + G₀.E.ncard))
    (hanswer : s.regs 0 = 1) :
    ∃ sf t, Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06RecoverContractionsProg s sf t ∧
      t ≤ 2000 * (gm06SuccessorInputSize x + 1) ^ 2 ∧
      sf.regs 0 = 1 ∧ sf.regs 309 = 0 ∧
      sf.arrs 8 = gm06EncodeRows (gm06UndoTraceRows records rows) ∧
      GM06SuccessorOutputRep input θ (sf.regs 0) (sf.arrs 8) ∧ sf.arrs 0 = s.arrs 0 ∧
      ∀ q ∈ [900, 904, 905], sf.regs q = s.regs q := by
  obtain ⟨hw, _, hbudget, hfuel, _, _⟩ := input.initial_word_caps hG₀
  have hlen : initial.tagged.length = G₀.E.ncard := by
    rw [hinit, GM06SuccessorGraphRep.initialTagged, List.length_map]
    exact input.graph.pairCount_eq
  have hcap : 1 + k + 2 * initial.tagged.length + x.vertexCount <
      2 ^ wordSize 32 (gm06SuccessorInputSize x) := by rw [hlen]; omega
  have hhist : (gm06ContractionHistoryWords (records.filterMap id) ++ tail).length <
      2 ^ wordSize 32 (gm06SuccessorInputSize x) := by
    rw [← core.history, hcapacity]
    omega
  obtain ⟨sf, t, he, ht, hf, hbit, hcount, hrows, hout⟩ :=
    gm06RecoverContractionsProg_output input initial hinit hvertex hedge trace M hM rows cur.linkage tail s
      (by omega) hcap hhist core.linkage core.history core.historyReg hanswer
  refine ⟨sf, t, he, ht, hbit, hcount, hrows, hout, hf.2 0 (by decide), ?_⟩
  intro q hq
  apply hf.1 q
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> decide

end GraphMinor.Compute
