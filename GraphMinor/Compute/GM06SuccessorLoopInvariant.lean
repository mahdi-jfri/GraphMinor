module

public import GraphMinor.Compute.GM06SuccessorCoreState

/-!
# The outer counting-loop invariant for VI (5.7)

An active entry contains a current drawing interpretation, its
literal RAM core, and actual forward and inverse histories from
the input. The number of reductions in that history is the outer
counter. An answered entry contains the public output relation.
No condition asks for a future reduction or successor construction.

Initialization proves this assertion from the ordinary finite input.
Idle rounds preserve an answer while advancing the counter. At the
last allocated counter value an active history is impossible: its
proper current drawing has positive measure, whereas every recorded
round strictly lowers `2μ+b`. Thus a loop that preserves this assertion
has produced its output by the end of its fixed counting range.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- The memory and actual past histories at a counting-loop entry,
following Lemma 18 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`). The
answered case records an output already produced; the active case
records only current arrays and actual previous reductions. -/
@[expose] def gm06SuccessorLoopInvariant
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (θ : ℝ) (initial : GM06CurrentDrawingRep x G₀ L₀) (i : ℕ) (s : State) : Prop :=
  s.regs 900 = i ∧ s.regs 905 = 2 * (x.vertexCount + G₀.E.ncard) + 1 ∧
    s.arrs 0 = gm06EncodeSuccessorInput x ∧
    ((s.regs 904 = 0 ∧ GM06SuccessorOutputRep input θ (s.regs 0) (s.arrs 8)) ∨
      (s.regs 904 = 1 ∧ ∃ (ends : List ℕ) (rots paths : List (List ℕ))
        (G : Drawing ClosedCylinder) (L : CylinderLinkage k G)
        (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} G L)
        (b : Bool) (d r : ℕ) (records : List (Option (ℕ × ℕ))) (tail : List ℕ),
        d + r = i ∧ Alg57ReductionRun ⟨G₀, L₀, true⟩ ⟨G, L, b⟩ d r ∧
        GM06UndoTrace x.vertexCount k initial.undoState cur.undoState records ∧
        GM06SuccessorCoreRep cur b records tail s ∧
        Function.Injective cur.vertex ∧ (∀ p ∈ cur.tagged, p.2 ≤ 1) ∧
        (s.arrs 9).length = 2 * (x.vertexCount + G₀.E.ncard)))

/-- The real initialization prefix proves the outer invariant at
counter zero, with the original edge enumeration needed for final
UNDO. Its logarithmic word size and linear cost follow from input. -/
theorem gm06InitializeSuccessorLoopCoreProg_invariant
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (hG₀ : IsCylinderSection5Drawing k G₀) (θ : ℝ) (s : State)
    (hinput : s.arrs 0 = gm06EncodeSuccessorInput x) :
    ∃ (sf : State) (t : ℕ) (initial : GM06CurrentDrawingRep x G₀ L₀),
      Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06InitializeSuccessorLoopCoreProg s sf t ∧
      t ≤ 100 * (gm06SuccessorInputSize x + 1) ∧
      initial.tagged = input.graph.initialTagged ∧
      initial.vertex = input.graph.vertexLabels ∧ HEq initial.edge input.graph.edgeLabels ∧
      gm06SuccessorLoopInvariant input θ initial 0 sf := by
  obtain ⟨sf, t, initial, he, ht, core, h0, h905, h904, h900,
      htag, _, hv, hedge, hinj, hbits⟩ := gm06InitializeSuccessorLoopCoreProg_core input hG₀ s hinput
  have h9 : sf.arrs 9 = List.replicate (2 * (x.vertexCount + G₀.E.ncard)) 0 := core.history
  refine ⟨sf, t, initial, he, ht, htag, hv, hedge,
    h900, h905, h0.trans hinput, Or.inr ⟨h904, x.endpoints, x.rotations, x.linkage,
      G₀, L₀, initial, true, 0, 0, [], _, rfl, .nil _, .nil _, core, hinj, hbits, ?_⟩⟩
  rw [h9, List.length_replicate]

/-- Lemma 18 at an actual active RAM entry. The literal core represents
its current drawing and linkage. The winding and the feasibility question
are unchanged from the input. If the stored bit is zero, one of the
first three reductions is available in that current drawing. These facts
follow from the recorded past reductions. -/
theorem gm06SuccessorLoopInvariant_active_spec
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G₀} {input : GM06SuccessorInputRep x G₀ L₀}
    {θ : ℝ} {initial : GM06CurrentDrawingRep x G₀ L₀} {i : ℕ} {s : State}
    (inv : gm06SuccessorLoopInvariant input θ initial i s)
    (hG₀ : IsCylinderSection5Drawing k G₀) (hθ₀ : L₀.HasTheta θ)
    (hgo : s.regs 904 = 1) :
    ∃ (ends : List ℕ) (rots paths : List (List ℕ))
      (G : Drawing ClosedCylinder) (L : CylinderLinkage k G)
      (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} G L)
      (b : Bool) (records : List (Option (ℕ × ℕ))) (tail : List ℕ),
      GM06SuccessorCoreRep cur b records tail s ∧
      IsCylinderSection5Drawing k G ∧ L.HasTheta θ ∧
      (IsThetaFeasible k G (θ + 1 / (k : ℝ)) ↔
        IsThetaFeasible k G₀ (θ + 1 / (k : ℝ))) ∧
      (b = false → ∃ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
        IsCylinderSection5Drawing k H ∧
          (Section5Reduction1Step k G L H M ∨ Section5Reduction2Step k G L H M ∨
            Section5Reduction3Step k G L H M)) := by
  rcases inv.2.2.2 with ⟨hstop, _⟩ | ⟨_, ends, rots, paths, G, L, cur, b, d, r,
      records, tail, _, run, _, core, _, _, _⟩
  · omega
  · obtain ⟨hG, hθ, hf⟩ := run.invariant hG₀ hθ₀
    refine ⟨ends, rots, paths, G, L, cur, b, records, tail, core, hG, hθ, hf, ?_⟩
    intro hb
    exact run.early_reduction_of_zero_bit hG₀ (fun h => Bool.noConfusion h) hb

/-- Lemma 19 in the literal reached memory: the number of completed
reductions plus the current mask measure is at most the initial
`2μ+1`. Thus every completed reduction consumes one unit of the
original fuel, including a rerouting that changes only the bit. -/
theorem gm06SuccessorLoopInvariant_measure
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G₀} {input : GM06SuccessorInputRep x G₀ L₀}
    {θ : ℝ} {initial : GM06CurrentDrawingRep x G₀ L₀} {i : ℕ} {s : State}
    (inv : gm06SuccessorLoopInvariant input θ initial i s)
    (hgo : s.regs 904 = 1) :
    gm06LoopMeasure s + i ≤ 2 * (x.vertexCount + G₀.E.ncard) + 1 := by
  rcases inv.2.2.2 with ⟨hstop, _⟩ | ⟨_, ends, rots, paths, G, L, cur, b, d, r,
      records, tail, hcounter, run, _, core, _, _, _⟩
  · omega
  · have hm := cur.ram_measure_eq s b core.active core.live core.bit
    have hh := run.rounds_add_measure_le
    rw [← hm] at hh
    have hV : G₀.V.ncard = x.vertexCount := input.graph.vertexCount_eq.symm
    change gm06LoopMeasure s + d + r ≤ 2 * (G₀.V.ncard + G₀.E.ncard) + 1 at hh
    rw [hV] at hh
    omega

/-- The continuation flag is Boolean at every represented entry. -/
theorem gm06SuccessorLoopInvariant_flag
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G₀} {input : GM06SuccessorInputRep x G₀ L₀}
    {θ : ℝ} {initial : GM06CurrentDrawingRep x G₀ L₀} {i : ℕ} {s : State}
    (inv : gm06SuccessorLoopInvariant input θ initial i s) : s.regs 904 = 0 ∨ s.regs 904 = 1 := by
  exact inv.2.2.2.imp And.left And.left

/-- An answered entry remains represented after the idle body and
counter increment. Every array and output register is unchanged. -/
theorem gm06SuccessorLoopInvariant_idle
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G₀} {input : GM06SuccessorInputRep x G₀ L₀}
    {θ : ℝ} {initial : GM06CurrentDrawingRep x G₀ L₀} {i : ℕ} {s : State}
    (inv : gm06SuccessorLoopInvariant input θ initial i s) (hstop : s.regs 904 = 0) :
    gm06SuccessorLoopInvariant input θ initial (i + 1) (s.setReg 900 (i + 1)) := by
  obtain ⟨h900, h905, hinput, hcase⟩ := inv
  have hout : GM06SuccessorOutputRep input θ (s.regs 0) (s.arrs 8) := by
    rcases hcase with ⟨_, h⟩ | ⟨hgo, _⟩
    · exact h
    · omega
  refine ⟨by simp, by simpa using h905, hinput, Or.inl ⟨by simpa using hstop, ?_⟩⟩
  simpa using hout

/-- Every active entry has a counter strictly below the allocated
fuel. Its stored measure is positive because the proper current
drawing contains an initial path, while Lemma 19 bounds that measure
plus the completed-round counter by the original fuel. -/
theorem gm06SuccessorLoopInvariant_active_counter_lt
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G₀} {input : GM06SuccessorInputRep x G₀ L₀}
    {θ : ℝ} {initial : GM06CurrentDrawingRep x G₀ L₀} {i : ℕ} {s : State}
    (inv : gm06SuccessorLoopInvariant input θ initial i s)
    (hG₀ : IsCylinderSection5Drawing k G₀) (hθ₀ : L₀.HasTheta θ)
    (hgo : s.regs 904 = 1) : i < 2 * (x.vertexCount + G₀.E.ncard) + 1 := by
  obtain ⟨ends, rots, paths, G, L, cur, b, records, tail, core, hG, _⟩ :=
    gm06SuccessorLoopInvariant_active_spec inv hG₀ hθ₀ hgo
  have hpos := gm06CurrentDrawing_measure_pos cur hG b
  have hm := cur.ram_measure_eq s b core.active core.live core.bit
  have hbound := gm06SuccessorLoopInvariant_measure inv hgo
  rw [← hm] at hpos
  omega

/-- At the final fixed-fuel counter, the invariant forces an actual
answer. An active entry would give a valid reduction history of the
full fuel length, contradicting its positive current measure. -/
theorem gm06SuccessorLoopInvariant_output_at_fuel
    {k : ℕ} {x : GM06SuccessorInput} {G₀ : Drawing ClosedCylinder}
    {L₀ : CylinderLinkage k G₀} (input : GM06SuccessorInputRep x G₀ L₀)
    (initial : GM06CurrentDrawingRep x G₀ L₀)
    (hG₀ : IsCylinderSection5Drawing k G₀) {θ : ℝ} (hθ₀ : L₀.HasTheta θ)
    {s : State}
    (inv : gm06SuccessorLoopInvariant input θ initial (2 * (x.vertexCount + G₀.E.ncard) + 1) s) :
    s.regs 904 = 0 ∧ GM06SuccessorOutputRep input θ (s.regs 0) (s.arrs 8) := by
  rcases inv.2.2.2 with answered | ⟨hgo, _⟩
  · exact answered
  · have hlt := gm06SuccessorLoopInvariant_active_counter_lt inv hG₀ hθ₀ hgo
    exact False.elim (Nat.lt_irrefl _ hlt)

end GraphMinor.Compute
