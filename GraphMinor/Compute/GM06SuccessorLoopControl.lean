module

public import GraphMinor.Compute.GM06EarlyReductionProgram
public import GraphMinor.Compute.GM06CurrentTerminalTest
public import GraphMinor.Compute.GM06RecoverContractions
public import GraphMinor.Compute.GM06InitSuccessorWorkspace
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The control flow and fuel of VI (5.7)

The loop tests its three early branches first, then calls the whole
Reduction 4 phase. When both stages fail, it tests the terminal
valencies. A negative answer stops. A positive answer calls the
whole terminal witness phase and UNDO before stopping. The phase
programs are parameters of this command constructor so their actual
proved programs can be inserted without changing the control flow.

The original counts give `2(n+m)+1` iterations. The pure mask measure
is the actual drawing measure, so a history of that many reduction
rounds is impossible. The finite counter continues through idle
rounds after the answer has been produced.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- A terminal branch first decides feasibility. If positive, it
constructs and recovers the witness. Both answers clear flag 904. -/
@[expose] def gm06FinishSuccessorProg (terminalPhase : Cmd) : Cmd :=
  .seq gm06CurrentTerminalTestProg
    (.seq (.ite (.reg 0) (.seq terminalPhase gm06RecoverContractionsProg) .skip)
      (.assign 904 (.const 0)))

/-- One loop round, calling the two whole phase programs after the
three early scans. Positive reduction flags continue the loop. -/
@[expose] def gm06SuccessorLoopBody (reduction4Phase terminalPhase : Cmd) : Cmd :=
  .seq gm06EarlyReductionsProg
    (.ite (.reg 901) .skip
      (.seq reduction4Phase
        (.ite (.reg 646) .skip (gm06FinishSuccessorProg terminalPhase))))

/-- Initialize the fixed fuel, continuation flag and outer counter.
Only original vertex and ordinary edge-slot counts determine fuel. -/
@[expose] def gm06InitSuccessorLoopControlProg : Cmd :=
  .seq (.assign 905 (.op .add
    (.op .mul (.const 2) (.op .add (.reg 100) (.len 12))) (.const 1)))
    (.seq (.assign 904 (.const 1)) (.assign 900 (.const 0)))

/-- The finite outer loop calls no phase after flag 904 has been
cleared. Its fixed bound is kept in register 905. -/
@[expose] def gm06SuccessorLoopProg (reduction4Phase terminalPhase : Cmd) : Cmd :=
  .seq gm06InitSuccessorLoopControlProg
    (forUp 900 (.reg 905)
      (.ite (.reg 904) (gm06SuccessorLoopBody reduction4Phase terminalPhase) .skip))

/-- The complete command constructor initializes the ordinary core,
history and bit, then runs the finite outer control loop. -/
@[expose] def gm06Algorithm57ProgramOfPhases (reduction4Phase terminalPhase : Cmd) : Cmd :=
  .seq gm06InitializeSuccessorProg (gm06SuccessorLoopProg reduction4Phase terminalPhase)

/-- Fuel initialization executes in twelve RAM steps and preserves
all instance arrays and the reference-winding bit. -/
theorem gm06InitSuccessorLoopControlProg_exec {w n m : ℕ} (s : State)
    (hw : 2 < 2 ^ w) (hfuel : 2 * (n + m) + 1 < 2 ^ w)
    (h100 : s.regs 100 = n) (h12 : (s.arrs 12).length = m) :
    ∃ sf, Exec w gm06InitSuccessorLoopControlProg s sf 12 ∧
      Keeps [905, 904, 900] [] s sf ∧
      sf.regs 905 = 2 * (n + m) + 1 ∧ sf.regs 904 = 1 ∧ sf.regs 900 = 0 := by
  have hn : n < 2 ^ w := by omega
  have hm : m < 2 ^ w := by omega
  have hlen : (Expr.len 12).eval w s = some m := by
    simp [Expr.eval, checkWord, h12, hm]
  have hsum := Crossing.eval_add (Crossing.eval_reg h100 hn) hlen (by omega : n + m < 2 ^ w)
  have hmul := Crossing.eval_mul (Crossing.eval_const hw) hsum (by omega : 2 * (n + m) < 2 ^ w)
  have heval := Crossing.eval_add hmul (Crossing.eval_const (by omega : 1 < 2 ^ w)) hfuel
  let s₀ := s.setReg 905 (2 * (n + m) + 1)
  let s₁ := s₀.setReg 904 1
  let sf := s₁.setReg 900 0
  have he₀ : Exec w (.assign 905 (.op .add
      (.op .mul (.const 2) (.op .add (.reg 100) (.len 12))) (.const 1))) s s₀ 8 := by
    simpa only [s₀, Expr.cost, Nat.reduceAdd] using Exec.assign (r := 905) heval
  have he₁ : Exec w (.assign 904 (.const 1)) s₀ s₁ 2 := .assign (Crossing.eval_const (by omega))
  have he₂ : Exec w (.assign 900 (.const 0)) s₁ sf 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  refine ⟨sf, .seq he₀ (.seq he₁ he₂),
    (((Keeps.refl _ _ s).setReg (by decide) _).setReg (by decide) _).setReg (by decide) _,
    ?_, ?_, ?_⟩
  · simp [sf, s₁, s₀]
  · simp [sf, s₁]
  · simp [sf]

/-- The ordinary input initializer establishes the complete current
relation, live and active masks, empty recovery history and bit one.
It supplies the actual initial state used by the loop invariant. -/
theorem gm06InitializeSuccessorProg_current
    {w k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L)
    (s : State) (hw : 2 < 2 ^ w) (ha : s.arrs 0 = gm06EncodeSuccessorInput x)
    (hlen : (gm06EncodeSuccessorInput x).length < 2 ^ w)
    (hwords : ∀ a ∈ gm06EncodeSuccessorInput x, a < 2 ^ w)
    (hsize : 2 * (x.vertexCount + G.E.ncard) < 2 ^ w) :
    ∃ (sf : State) (t : ℕ) (cur : GM06CurrentDrawingRep x G L),
      Exec w gm06InitializeSuccessorProg s sf t ∧
      t ≤ 30 + 22 * (gm06EncodeSuccessorInput x).length + 15 * (x.vertexCount + G.E.ncard) ∧
      sf.arrs 0 = s.arrs 0 ∧ sf.arrs 2 = [x.vertexCount] ∧
      sf.arrs 3 = x.endpoints ∧ sf.arrs 4 = gm06EncodeRows x.rotations ∧
      sf.arrs 6 = x.innerCuff ∧ sf.arrs 7 = x.outerCuff ∧ sf.arrs 8 = gm06EncodeRows x.linkage ∧
      sf.arrs 12 = cur.tagged.map Prod.snd ∧ sf.arrs 14 = gm02VertexBits cur.live ∧
      sf.arrs 9 = List.replicate (2 * (x.vertexCount + cur.tagged.length)) 0 ∧
      sf.regs 100 = x.vertexCount ∧ sf.regs 309 = 0 ∧ sf.regs 329 = 1 ∧
      cur.tagged = rep.graph.initialTagged ∧ cur.live = Finset.univ ∧
      cur.vertex = rep.graph.vertexLabels ∧ HEq cur.edge rep.graph.edgeLabels ∧ Function.Injective cur.vertex ∧
      (∀ p ∈ cur.tagged, p.2 ≤ 1) ∧
      gm06LoopMeasure sf = (Alg57DrawingState.mk G L true).measure := by
  classical
  obtain ⟨cur, htag, hlive, hv, hedge, _⟩ := rep.exists_currentDrawingRep_edge
  obtain ⟨sf, t, he, ht, hfields, hactive, hliveBits, hhistory, h100, h309, h329, hinput⟩ :=
    gm06InitializeSuccessorProg_exec x G.toGraph rep.graph s hw ha hlen hwords hsize
  have htagLen : cur.tagged.length = G.E.ncard := by
    rw [htag, GM06SuccessorGraphRep.initialTagged, List.length_map]
    exact rep.graph.pairCount_eq
  have hflags : cur.tagged.map Prod.snd = List.replicate G.E.ncard 1 := by
    rw [htag]
    simp only [GM06SuccessorGraphRep.initialTagged, List.map_map, Function.comp_def, List.map_const']
    exact congrArg (fun m => List.replicate m 1) rep.graph.pairCount_eq
  have hbits : gm02VertexBits cur.live = List.replicate x.vertexCount 1 := by
    simp [hlive, gm02VertexBits]
  have h12 : sf.arrs 12 = cur.tagged.map Prod.snd := hactive.trans hflags.symm
  have h14 : sf.arrs 14 = gm02VertexBits cur.live := hliveBits.trans hbits.symm
  refine ⟨sf, t, cur, he, ht, hinput, ?_, ?_, ?_, ?_, ?_, ?_, h12, h14,
    by rw [htagLen]; exact hhistory, h100, h309, h329, htag, hlive, hv, hedge,
    ?_, ?_, cur.ram_measure_eq sf true h12 h14 h329⟩
  · simpa [gm06SuccessorFieldArray, gm06SuccessorRows] using hfields ⟨0, by decide⟩
  · simpa [gm06SuccessorFieldArray, gm06SuccessorRows] using hfields ⟨1, by decide⟩
  · simpa [gm06SuccessorFieldArray, gm06SuccessorRows] using hfields ⟨2, by decide⟩
  · simpa [gm06SuccessorFieldArray, gm06SuccessorRows] using hfields ⟨3, by decide⟩
  · simpa [gm06SuccessorFieldArray, gm06SuccessorRows] using hfields ⟨4, by decide⟩
  · simpa [gm06SuccessorFieldArray, gm06SuccessorRows] using hfields ⟨5, by decide⟩
  · exact hv.symm ▸ rep.graph.vertexLabels.injective
  · intro p hp
    rw [htag, GM06SuccessorGraphRep.initialTagged] at hp
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
    exact Nat.le_refl 1

/-- Every reached proper drawing has positive measure: even one
initial path supplies an actual live vertex. -/
theorem gm06CurrentDrawing_measure_pos
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) (b : Bool) :
    0 < (Alg57DrawingState.mk G L b).measure := by
  let i : Fin k := ⟨0, hG.1⟩
  have hV : 0 < G.V.ncard := (Set.ncard_pos G.finite_V).mpr
    ⟨rep.vertex (rep.source i), rep.vertex_mem _ (rep.source_live i)⟩
  dsimp only [Alg57DrawingState.measure, Alg57DrawingState.size]
  omega

/-- The initialized mathematical measure fits below the fixed fuel,
using the current relation's original ordinary slot bounds. -/
theorem gm06CurrentDrawing_measure_le_fuel
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L) (b : Bool) :
    (Alg57DrawingState.mk G L b).measure ≤ 2 * (x.vertexCount + rep.tagged.length) + 1 := by
  have hs := rep.size_le_slots
  have hb : b.toNat ≤ 1 := by cases b <;> decide
  dsimp only [Alg57DrawingState.measure, Alg57DrawingState.size]
  omega

/-- A valid reduction history is strictly shorter than the allocated
fuel. Thus the outer RAM loop must reach an answering round. -/
theorem gm06ReductionRun_rounds_lt_fuel
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    {H : Drawing ClosedCylinder} {M : CylinderLinkage k H}
    {y : GM06SuccessorInput} (cur : GM06CurrentDrawingRep y H M)
    (hH : IsCylinderSection5Drawing k H) (b c : Bool) {d r : ℕ}
    (run : Alg57ReductionRun ⟨G, L, b⟩ ⟨H, M, c⟩ d r) :
    d + r < 2 * (x.vertexCount + rep.tagged.length) + 1 := by
  have hrun := run.rounds_add_measure_le
  have hstart := gm06CurrentDrawing_measure_le_fuel rep b
  have hpos := gm06CurrentDrawing_measure_pos cur hH c
  omega

end GraphMinor.Compute
