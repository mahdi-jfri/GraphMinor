module

public import GraphMinor.Compute.GM06EarlyReductionInvariant
public import GraphMinor.Compute.GM06SuccessorLoopFinish

/-!
# An actual reached early round of VI (5.7)

The chronological history bounds all current words and leaves a free
contraction-record slot. Therefore the early driver executes at every
reached proper state with the word size chosen from the original input.
Its time has the same uniform quartic bound at every round.

A successful scan executes the whole loop body, since its branch tag
skips both finite phases. It extends the actual forward and inverse
histories and strictly lowers the RAM measure. If every early scan
fails, the old bit is one and the unchanged core is ready for the
Reduction 4 phase. The original input and outer controls survive.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- At any reached state, the actual early part executes without
additional word-bound or history-room premises. A successful early
branch already executes the complete loop body and preserves its
chronological and memory invariants. The two phase commands are not
executed in that case and have no correctness premises here. -/
theorem gm06Reached_early_round
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
    (h2 : s.arrs 2 = [x.vertexCount]) (h3 : s.arrs 3 = oldEnds)
    (h4 : s.arrs 4 = gm06EncodeRows oldRots) (h6 : s.arrs 6 = x.innerCuff)
    (h7 : s.arrs 7 = x.outerCuff) (h8 : s.arrs 8 = gm06EncodeRows oldPaths)
    (h9 : s.arrs 9 = gm06ContractionHistoryWords (records.filterMap id) ++ tail)
    (h9len : (s.arrs 9).length = 2 * (x.vertexCount + G₀.E.ncard))
    (h12 : s.arrs 12 = cur.tagged.map Prod.snd) (h14 : s.arrs 14 = gm02VertexBits cur.live)
    (h309 : s.regs 309 = (records.filterMap id).length) (h329 : s.regs 329 = b.toNat) :
    ∃ sf t,
      Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06EarlyReductionsProg s sf t ∧
      t ≤ 5062500000 * (gm06SuccessorInputSize x + 1) ^ 4 ∧
      (∀ a ∈ [0, 2, 6, 7], sf.arrs a = s.arrs a) ∧
      (∀ q ∈ [900, 904, 905], sf.regs q = s.regs q) ∧
      ((sf.regs 901 = 0 ∧ sf.regs 329 = 1 ∧ b = true ∧
          sf.regs 309 = (records.filterMap id).length ∧
          (∀ a ∈ [3, 4, 8, 9, 12, 14], sf.arrs a = s.arrs a) ∧
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
         sf.regs 901 ∈ [1, 2, 3] ∧ sf.regs 329 = 1 ∧
         sf.arrs 3 = ends ∧ sf.arrs 4 = gm06EncodeRows rots ∧ sf.arrs 8 = gm06EncodeRows paths ∧
         sf.arrs 12 = next.tagged.map Prod.snd ∧ sf.arrs 14 = gm02VertexBits next.live ∧
         Function.Injective next.vertex ∧ next.tagged.length = cur.tagged.length ∧
         (∀ p ∈ next.tagged, p.2 ≤ 1) ∧ IsCylinderSection5Drawing k H ∧
         Alg57ReductionRun ⟨G₀, L₀, true⟩ ⟨H, M, true⟩ (d + 1) r ∧
         GM06UndoTrace x.vertexCount k initial.undoState next.undoState (records ++ [record]) ∧
         M.HasTheta θ ∧
         (IsThetaFeasible k H (θ + 1 / (k : ℝ)) ↔
           IsThetaFeasible k G₀ (θ + 1 / (k : ℝ))) ∧
         gm06LoopMeasure sf < gm06LoopMeasure s ∧
         sf.regs 309 = ((records ++ [record]).filterMap id).length ∧
         sf.arrs 9 = gm06ContractionHistoryWords ((records ++ [record]).filterMap id) ++ newTail ∧
         (sf.arrs 9).length = (s.arrs 9).length) := by
  obtain ⟨hG, _, _⟩ := run.invariant hG₀ hθ₀
  obtain ⟨hw, hsquare, hcap, _, _, _, _⟩ :=
    gm06Reached_word_caps input initial hinit cur trace hG₀ hG
  obtain ⟨_, _, _, hfuel, _, _⟩ := input.initial_word_caps hG₀
  have hhistLen : (gm06ContractionHistoryWords (records.filterMap id) ++ tail).length =
      2 * (x.vertexCount + G₀.E.ncard) := by rw [← h9]; exact h9len
  have hhist : (gm06ContractionHistoryWords (records.filterMap id) ++ tail).length <
      2 ^ wordSize 32 (gm06SuccessorInputSize x) := by rw [hhistLen]; omega
  have hroom := gm06Reached_history_free_slot input initial cur trace hG
  rw [← hhistLen] at hroom
  obtain ⟨sf, t, he, ht, hfields, hcounter, hout⟩ := gm06EarlyReductionsProg_invariant cur hvinj
    ⟨G₀, L₀, true⟩ hG₀ rfl hθ₀ b run initial.undoState records trace tail s
    hw hsquare hcap hbits hhist hroom h2 h3 h4 h6 h7 h8 h9 h12 h14 h309 h329
  obtain ⟨hinput, h904, h905⟩ := gm06EarlyReductionsProg_control_frame he
  have ha : ∀ a ∈ [0, 2, 6, 7], sf.arrs a = s.arrs a := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hinput
    all_goals exact hfields _ (by simp)
  have hr : ∀ q ∈ [900, 904, 905], sf.regs q = s.regs q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hcounter
    · exact h904
    · exact h905
  refine ⟨sf, t, he, ht.trans (gm06Reached_early_cost_le input initial hinit cur trace hG), ha, hr, ?_⟩
  rcases hout with hnone | ⟨ends, rots, paths, H, M, next, record, newTail,
      hflag, hbit, h3', h4', h8', h12', h14', hinj, hlen, hbits', hH,
      run', trace', hθ', hfeas, hmeasure, hcount, hhistory, hhistSize⟩
  · exact Or.inl hnone
  · have hflagBound : sf.regs 901 < 2 ^ wordSize 32 (gm06SuccessorInputSize x) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hflag
      rcases hflag with h | h | h <;> omega
    have hflagNe : sf.regs 901 ≠ 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hflag
      rcases hflag with h | h | h <;> omega
    have heBody : Exec (wordSize 32 (gm06SuccessorInputSize x))
        (gm06SuccessorLoopBody reduction4Phase terminalPhase) s sf (t + 2) :=
      .seq he (.ite_true (Crossing.eval_reg rfl hflagBound) hflagNe (.skip _))
    exact Or.inr ⟨ends, rots, paths, H, M, next, record, newTail, heBody,
      hflag, hbit, h3', h4', h8', h12', h14', hinj, hlen, hbits', hH,
      run', trace', hθ', hfeas, hmeasure, hcount, hhistory, hhistSize⟩

end GraphMinor.Compute
