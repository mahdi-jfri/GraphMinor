module

public import GraphMinor.Compute.GM06SuccessorCoreState
public import GraphMinor.Compute.GM06CurrentPhaseBounds
public import GraphMinor.Compute.GM06Reduction4PhaseExec
import GraphMinor.GM06.Alg57CurrentCutOrbit

/-!
# Executing the whole Reduction 4 phase at a reached state

The current drawing interpretation bounds the ordinary endpoint and
path words and both cuff lists. Its positive rotation rows are
without repetitions and lie in the fixed augmented dart space.
The past inverse trace bounds the phase's cubic workspace by the
original logarithmic word size.

These facts discharge every input premise of the proved whole phase
program. Its exact pure output and write frame therefore hold on the
loop's actual core, with a uniform original-size quartic time bound.
When the phase returns no rerouting, the entire old core assertion
is preserved, including its reference linkage and inverse history.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- Word ranges for the actual current finite arrays used by a whole
phase. They follow from the drawing and path interpretation alone. -/
theorem gm06Current_phase_values
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (cur : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) :
    (∀ v ∈ x.endpoints, v < x.vertexCount) ∧
      (∀ d ∈ x.linkage.flatten, d < 2 * cur.tagged.length) ∧
      (∀ v ∈ x.innerCuff, v < x.vertexCount) ∧
      (∀ v ∈ x.outerCuff, v < x.vertexCount) ∧
      ∀ d ∈ x.rotations.flatten,
        d < 2 * (cur.tagged.length + x.innerCuff.length + x.outerCuff.length) := by
  refine ⟨fun _ h => cur.endpoint_word_lt h, ?_, ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨row, hr, hrow⟩ := List.mem_flatten.mp hd
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    obtain ⟨_, _, henc, _⟩ := cur.linkage.path ⟨i, cur.linkage.1 ▸ hi⟩
    exact (henc.active_words d hrow).choose
  · intro v hv
    rw [cur.inner, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact (cur.source i).isLt
  · intro v hv
    rw [cur.outer, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact (cur.target i).isLt
  · intro d hd
    have hb := cur.rotation_word_lt hG hd
    rw [cur.inner, cur.outer, List.length_ofFn, List.length_ofFn]
    omega

private theorem phase_linkage_of_false {x : GM06SuccessorInput} {m : ℕ}
    (h : (gm06Reduction4Phase x m).1 = false) : (gm06Reduction4Phase x m).2 = x.linkage := by
  cases hw : gm06Reduction4PhaseWitness x m with
  | none => rw [gm06Reduction4Phase_of_none hw]
  | some p =>
    obtain ⟨i, j, darts⟩ := p
    rw [gm06Reduction4Phase_of_some hw] at h
    cases h

/-- The real whole Reduction 4 command executes at every reached
proper core. Its memory frame and exact output are those of the pure
phase, and its time is bounded in the original size. A negative phase
result preserves the complete old core. No phase execution, geometric
soundness, or word-bound statement is supplied as a hypothesis. -/
theorem gm06Reduction4PhaseProg_reached
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
    ∃ sf t, Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06Reduction4PhaseProg s sf t ∧
      t ≤ 20971520000000 * (gm06SuccessorInputSize x + 1) ^ 4 ∧
      Keeps gm06Reduction4PhaseRegs gm06Reduction4PhaseArrs s sf ∧
      sf.regs 646 = (if (gm06Reduction4Phase y cur.tagged.length).1 then 1 else 0) ∧
      sf.arrs 8 = gm06EncodeRows (gm06Reduction4Phase y cur.tagged.length).2 ∧
      sf.regs 329 = (if (gm06Reduction4Phase y cur.tagged.length).1 then 0 else b.toNat) ∧
      ((gm06Reduction4Phase y cur.tagged.length).1 = false →
        GM06SuccessorCoreRep cur b records tail sf) := by
  let y := {x with endpoints := ends, rotations := rots, linkage := paths}
  obtain ⟨he, hi, ho, hp, hrows, hnd⟩ := gm06Current_phase_lengths cur
  obtain ⟨hend, hd, hinner, houter, hkeys⟩ := gm06Current_phase_values cur hG
  have hcode := gm06Reached_phase_word_cap input initial hinit cur trace hG
  have hcount : y.linkage.length = y.innerCuff.length := hp.trans hi.symm
  have h12 : (s.arrs 12).length = cur.tagged.length := by rw [core.active, List.length_map]
  obtain ⟨sf, t, hex, ht, hf, hflag, h8, hbit⟩ := gm06Reduction4PhaseProg_exec y s he hend hd hinner houter
    hcount hrows hnd hkeys hcode core.countReg h12 core.rotations core.endpoints core.linkage core.inner core.outer
  have htime := ht.trans (gm06Reached_phase_polynomial_le input initial hinit cur trace hG 20000000 4)
  refine ⟨sf, t, hex, by simpa only [Nat.reducePow, Nat.reduceMul] using htime,
    hf, hflag, h8, ?_, ?_⟩
  · simpa only [core.bit] using hbit
  · intro hfalse
    change (gm06Reduction4Phase y cur.tagged.length).1 = false at hfalse
    obtain ⟨ha, hr⟩ := gm06Reduction4PhaseProg_core_frame hex
    have hpaths : (gm06Reduction4Phase y cur.tagged.length).2 = paths := phase_linkage_of_false hfalse
    have h8' : sf.arrs 8 = gm06EncodeRows paths := h8.trans (congrArg gm06EncodeRows hpaths)
    have hbit' : sf.regs 329 = b.toNat := by simpa only [hfalse, Bool.false_eq_true, ite_false, core.bit] using hbit
    exact ⟨(ha 2 (by simp)).trans core.count, (ha 3 (by simp)).trans core.endpoints,
      (ha 4 (by simp)).trans core.rotations, (ha 6 (by simp)).trans core.inner,
      (ha 7 (by simp)).trans core.outer, h8', (ha 9 (by simp)).trans core.history,
      (ha 12 (by simp)).trans core.active, (ha 14 (by simp)).trans core.live,
      (hr 100 (by simp)).trans core.countReg, (hr 309 (by simp)).trans core.historyReg, hbit'⟩

end GraphMinor.Compute
