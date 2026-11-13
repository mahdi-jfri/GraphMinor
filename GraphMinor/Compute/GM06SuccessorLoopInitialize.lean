module

public import GraphMinor.Compute.GM06SuccessorLoopControl
public import GraphMinor.GM06.Alg57InputWordBounds

/-!
# Initializing the actual loop invariant of VI (5.7)

The six ordinary input fields determine the current arrays, empty
inverse history and initial bit. Their finite interpretation also
bounds every supplied word. Thus the initialization prefix executes
with a fixed logarithmic word size and linear time, starting from
arbitrary scratch memory.

The resulting current relation retains the original edge map, so
later UNDO produces paths in precisely the input enumeration.
Both chronological histories start empty. The actual mask measure
is positive and no larger than the allocated fixed fuel.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- The initialization prefix before the fixed-fuel counting loop. -/
@[expose] def gm06InitializeSuccessorLoopCoreProg : Cmd :=
  .seq gm06InitializeSuccessorProg gm06InitSuccessorLoopControlProg

/-- The ordinary input alone establishes every initial array, label,
history and control value. No machine-word bounds or geometric
certificates are supplied in addition to its actual interpretation. -/
theorem gm06InitializeSuccessorLoopCoreProg_current
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (input : GM06SuccessorInputRep x G L)
    (hG : IsCylinderSection5Drawing k G) (s : State)
    (hinput : s.arrs 0 = gm06EncodeSuccessorInput x) :
    ∃ (sf : State) (t : ℕ) (cur : GM06CurrentDrawingRep x G L),
      Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06InitializeSuccessorLoopCoreProg s sf t ∧
      t ≤ 100 * (gm06SuccessorInputSize x + 1) ∧
      sf.arrs 0 = s.arrs 0 ∧ sf.arrs 2 = [x.vertexCount] ∧
      sf.arrs 3 = x.endpoints ∧ sf.arrs 4 = gm06EncodeRows x.rotations ∧
      sf.arrs 6 = x.innerCuff ∧ sf.arrs 7 = x.outerCuff ∧ sf.arrs 8 = gm06EncodeRows x.linkage ∧
      sf.arrs 12 = cur.tagged.map Prod.snd ∧ sf.arrs 14 = gm02VertexBits cur.live ∧
      sf.arrs 9 = List.replicate (2 * (x.vertexCount + G.E.ncard)) 0 ∧
      sf.regs 100 = x.vertexCount ∧ sf.regs 309 = 0 ∧ sf.regs 329 = 1 ∧
      sf.regs 905 = 2 * (x.vertexCount + G.E.ncard) + 1 ∧ sf.regs 904 = 1 ∧ sf.regs 900 = 0 ∧
      cur.tagged = input.graph.initialTagged ∧ cur.live = Finset.univ ∧
      cur.vertex = input.graph.vertexLabels ∧ HEq cur.edge input.graph.edgeLabels ∧
      Function.Injective cur.vertex ∧ (∀ p ∈ cur.tagged, p.2 ≤ 1) ∧
      Alg57ReductionRun ⟨G, L, true⟩ ⟨G, L, true⟩ 0 0 ∧
      GM06UndoTrace x.vertexCount k cur.undoState cur.undoState [] ∧
      gm06LoopMeasure sf = (Alg57DrawingState.mk G L true).measure ∧
      0 < gm06LoopMeasure sf ∧ gm06LoopMeasure sf ≤ sf.regs 905 := by
  obtain ⟨hw, _, _, hfuel, hlen, hwords⟩ := input.initial_word_caps hG
  obtain ⟨sm, t, cur, he, ht, h0, h2, h3, h4, h6, h7, h8, h12, h14, h9,
      h100, h309, h329, htag, hlive, hvertex, hedge, hinj, hbits, hmeasure⟩ :=
    gm06InitializeSuccessorProg_current input s (by omega) hinput hlen hwords (by omega)
  have htagLen : cur.tagged.length = G.E.ncard := by
    rw [htag, GM06SuccessorGraphRep.initialTagged, List.length_map]
    exact input.graph.pairCount_eq
  have hmaskLen : (sm.arrs 12).length = G.E.ncard := by rw [h12, List.length_map, htagLen]
  obtain ⟨sf, heControl, hf, h905, h904, h900⟩ :=
    gm06InitSuccessorLoopControlProg_exec sm (by omega) hfuel h100 hmaskLen
  have ha (a : ℕ) : sf.arrs a = sm.arrs a := hf.2 a (by simp)
  have hr (r : ℕ) (hm : r ∈ [100, 309, 329]) : sf.regs r = sm.regs r := by
    apply hf.1 r
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> decide
  have h12' := (ha 12).trans h12
  have h14' := (ha 14).trans h14
  have h329' := (hr 329 (by simp)).trans h329
  have hmeasure' := cur.ram_measure_eq sf true h12' h14' h329'
  have hpositive := gm06CurrentDrawing_measure_pos cur hG true
  have hbound := gm06CurrentDrawing_measure_le_fuel cur true
  obtain ⟨hn, hm, _, _, _, hcode⟩ := input.size_bounds
  refine ⟨sf, t + 12, cur, .seq he heControl, by omega,
    (ha 0).trans h0, (ha 2).trans h2, (ha 3).trans h3, (ha 4).trans h4,
    (ha 6).trans h6, (ha 7).trans h7, (ha 8).trans h8, h12', h14', ?_,
    (hr 100 (by simp)).trans h100, (hr 309 (by simp)).trans h309, h329',
    h905, h904, h900, htag, hlive, hvertex, hedge, hinj, hbits,
    .nil _, .nil _, hmeasure', ?_, ?_⟩
  · rw [ha 9, h9, htagLen]
  · rw [hmeasure']; exact hpositive
  · rw [hmeasure', h905, ← htagLen]; exact hbound

end GraphMinor.Compute
