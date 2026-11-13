module

public import GraphMinor.Compute.GM06Reduction4PhaseProgram
public import GraphMinor.GM06.Alg57CurrentUndo
public import GraphMinor.GM06.Alg57ReductionMeasure
public import GraphMinor.GM06.Alg57CurrentBounds
import GraphMinor.GM06.Section5Reduction4Progress

/-!
# The loop invariant through an actual rerouting

A Reduction 4 changes the reference linkage on the same drawing.
The permanent graph, cuff and rotation interpretation therefore
survives by replacing only the path rows. An arbitrary final witness
needs no inverse operation for this round, so its chronological
undo record is empty and the numeric contraction history is unchanged.

The complete phase command preserves the graph arrays and outer
control registers. Its successful path output and zero bit fit the
new current relation. The mathematical reduction history then gives
unchanged winding, equivalent next feasibility, strict descent of
`2μ+b`, and an available early reduction on the next round.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- The complete Reduction 4 command preserves every persistent
array except the linkage, and all outer control and history registers.
This follows from the command's actual write frame for any execution. -/
theorem gm06Reduction4PhaseProg_core_frame {w t : ℕ} {s sf : State}
    (he : Exec w gm06Reduction4PhaseProg s sf t) :
    (∀ a ∈ [0, 2, 3, 4, 5, 6, 7, 9, 12, 14, 17, 19], sf.arrs a = s.arrs a) ∧
      ∀ r ∈ [0, 100, 309, 900, 901, 904, 905], sf.regs r = s.regs r := by
  have hf := gm06Reduction4PhaseProg_frame he
  constructor
  · intro a ha
    apply hf.2 a
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr
    apply hf.1 r
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- An actual admissible rerouting with encoded new rows preserves
the complete current drawing interpretation and extends both actual
histories. This is the local successful Reduction 4 case of Lemma 18 of our proof of VI (5.7)
(outlined in `GraphMinor/GM06/Alg57Algorithm.lean`). The phase's geometric soundness supplies the
actual step and encoding. -/
theorem gm06Rerouting_current_invariant
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (cur : GM06CurrentDrawingRep x G L)
    (hvinj : Function.Injective cur.vertex)
    (X : Alg57DrawingState k) (hX : IsCylinderSection5Drawing k X.drawing)
    {θ : ℝ} (hθX : X.linkage.HasTheta θ) {d r : ℕ}
    (run : Alg57ReductionRun X ⟨G, L, true⟩ d r)
    (original : GM06UndoState x.vertexCount) (records : List (Option (ℕ × ℕ)))
    (trace : GM06UndoTrace x.vertexCount k original cur.undoState records)
    (M : CylinderLinkage k G) (step : Section5Reduction4Step k G L G M)
    (rows : List (List ℕ)) (hrows : GM06LinkageRowsEncoding M cur.tagged cur.vertex cur.edge rows) :
    let next := cur.withLinkage M rows hrows
    Function.Injective next.vertex ∧ next.tagged = cur.tagged ∧ next.live = cur.live ∧
      Alg57ReductionRun X ⟨G, M, false⟩ d (r + 1) ∧
      GM06UndoTrace x.vertexCount k original next.undoState (records ++ [none]) ∧
      M.HasTheta θ ∧
      (IsThetaFeasible k G (θ + 1 / (k : ℝ)) ↔
        IsThetaFeasible k X.drawing (θ + 1 / (k : ℝ))) ∧
      (Alg57DrawingState.mk G M false).measure < (Alg57DrawingState.mk G L true).measure ∧
      (∃ (H : Drawing ClosedCylinder) (N : CylinderLinkage k H),
        IsCylinderSection5Drawing k H ∧
          (Section5Reduction1Step k G M H N ∨ Section5Reduction2Step k G M H N ∨
            Section5Reduction3Step k G M H N)) := by
  obtain ⟨hG, hθ, _⟩ := run.invariant hX hθX
  have round : Alg57ReductionRound ⟨G, L, true⟩ ⟨G, M, false⟩ true :=
    .four step hG rfl rfl
  have run' := run.snoc_reroute round
  have trace' := trace.snoc (cur.withLinkage_undo M rows hrows)
  obtain ⟨_, hθ', hfeas⟩ := run'.invariant hX hθX
  exact ⟨hvinj, rfl, rfl, run', trace', hθ', hfeas, round.measure_lt,
    reduction123_applies_after_reduction4 L M hG step⟩

/-- In a successful phase execution, the new linkage rows and bit
zero give exactly the new current masks and the strict RAM-measure
drop. The phase's write frame also preserves the numeric undo history
and its record count, even though its chronological trace gains a round. -/
theorem gm06Reduction4PhaseProg_rerouting_state
    {w k t : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (cur : GM06CurrentDrawingRep x G L)
    (M : CylinderLinkage k G) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding M cur.tagged cur.vertex cur.edge rows)
    {s sf : State} (he : Exec w gm06Reduction4PhaseProg s sf t)
    (h8 : sf.arrs 8 = gm06EncodeRows rows) (h329 : sf.regs 329 = 0)
    (h12 : s.arrs 12 = cur.tagged.map Prod.snd)
    (h14 : s.arrs 14 = gm02VertexBits cur.live) (hbit : s.regs 329 = 1) :
    let next := cur.withLinkage M rows hrows
    sf.arrs 8 = gm06EncodeRows rows ∧
      sf.arrs 12 = next.tagged.map Prod.snd ∧ sf.arrs 14 = gm02VertexBits next.live ∧
      sf.regs 329 = Bool.toNat false ∧ gm06LoopMeasure sf + 1 = gm06LoopMeasure s ∧
      sf.arrs 9 = s.arrs 9 ∧ sf.regs 309 = s.regs 309 ∧
      (∀ a ∈ [0, 2, 3, 4, 6, 7], sf.arrs a = s.arrs a) ∧
      ∀ r ∈ [900, 901, 904, 905], sf.regs r = s.regs r := by
  obtain ⟨ha, hr⟩ := gm06Reduction4PhaseProg_core_frame he
  have h12' := (ha 12 (by simp)).trans h12
  have h14' := (ha 14 (by simp)).trans h14
  have hmeasure : gm06LoopMeasure sf + 1 = gm06LoopMeasure s := by
    unfold gm06LoopMeasure
    rw [ha 12 (by simp), ha 14 (by simp), h329, hbit]
  refine ⟨h8, h12', h14', h329, hmeasure, ha 9 (by simp), hr 309 (by simp), ?_, ?_⟩
  · intro a hm
    exact ha a (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; tauto)
  · intro r hm
    exact hr r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; tauto)

end GraphMinor.Compute
