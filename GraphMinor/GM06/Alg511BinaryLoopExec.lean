module

public import GraphMinor.GM06.Alg511BinaryLoopRound
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Execution of the bounded binary feasibility loop

Every active controller round uses the exact successor contract and
the verified signed binary increment and comparison. Its input size
is bounded uniformly by the fixed drawing code and the simple-path
bound on each returned linkage. Stopped rounds are skips. Induction
through the actual controller gives the reached-state invariant at
the cap 1+|V(G)|/k, where VI (5.12) forces a stopped state.

The final continuing bit is therefore the exact feasibility answer,
with ordinary path rows on success. The time bound is the cap times
the successor bound plus graph-code and binary-width overhead. The
command and its exact successor execution contract are parameters
of this composition lemma for VI (5.11), pages 134–135. It does not
assert the existence of algorithm (5.7).
-/

@[expose] public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Compute.TwoPaths GraphMinor.Surface

/-- A uniform active-round budget: packed input, protected binary
rows, one binary addition, one guard and the two branch tests. -/
def alg511BinaryRoundBudget (B code base cap targetWidth incrementWidth : ℕ) : ℕ :=
  B + 215 + 68 * code + 24 * (base + cap + targetWidth + incrementWidth + 3) +
    (400 + 350 * (base + cap + incrementWidth + 1)) +
    (404 + 350 * (base + cap + targetWidth + 1)) + 4

private theorem round_time_le {u B code C words R base i cap b d : ℕ}
    (ht : u ≤ B + 215 + 68 * code + 24 * words +
      (400 + 350 * (base + i + d + 1)) + (404 + 350 * (base + (i + 1) + b + 1)) + 4)
    (hc : code ≤ C) (hr : words ≤ R) (hR : R = base + cap + b + d + 3) (hi : i + 1 ≤ cap) :
    u ≤ alg511BinaryRoundBudget B C base cap b d := by
  subst R
  apply ht.trans
  unfold alg511BinaryRoundBudget
  gcongr; omega

private theorem binary_row_lengths {x : GM06Alg511WindingInput} {target incrementRow : List ℕ}
    {base i b d : ℕ} {s : State} (h : alg511BinaryLoopCommon x target incrementRow base i s)
    (ht : target.length = b + 1) (hd : incrementRow.length = d + 1) :
    (([2800, 2801, 2802] : List ℕ).map (fun a => (s.arrs a).length)).sum ≤ base + i + b + d + 3 := by
  have hlen := h.2.2.2.2.2.2.2.words.1
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    h.2.2.2.2.1, h.2.2.2.2.2.1, ht, hd]
  omega


/-- Initialize only the controller's ordinary scalar slots and
protected counter row. All supplied binary rows and actual paths
remain untouched; this is the concrete prefix of the full command. -/
theorem alg511_binary_loop_prefix_exec {w : ℕ} {x : GM06Alg511WindingInput}
    (target incrementRow : List ℕ) (base : ℕ) (s : State) (hw : 1 < 2 ^ w)
    (ht : alg511BinaryLoopTables x s) (hk : s.regs 52 = x.drawing.pathCount)
    (hT : s.arrs 2801 = target) (hD : s.arrs 2802 = incrementRow)
    (hformat : alg511BinaryRowFormat (s.arrs 2800) base) :
    ∃ t, Exec w (.seq gm06Alg511BinaryLoopScalarsProg
      (.seq (.alloc 2803 (.const 1)) (.seq (.assign 6002 (.const 0)) (.assign 6000 (.const 1))))) s t 16 ∧
      alg511BinaryLoopCommon x target incrementRow base 0 t ∧
      t.regs 6000 = 1 ∧ t.regs 6002 = 0 ∧ t.arrs 8 = s.arrs 8 ∧ t.arrs 2800 = s.arrs 2800 := by
  obtain ⟨s₀, he₀, hkeep₀, hz⟩ := gm06Alg511BinaryLoopScalarsProg_exec (w := w) s
  let s₁ := s₀.setArr 2803 [0]
  let s₂ := s₁.setReg 6002 0
  let t := s₂.setReg 6000 1
  have he₁ : Exec w (.alloc 2803 (.const 1)) s₀ s₁ 2 := .alloc (Crossing.eval_const hw)
  have he₂ : Exec w (.assign 6002 (.const 0)) s₁ s₂ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  have he₃ : Exec w (.assign 6000 (.const 1)) s₂ t 2 := .assign (Crossing.eval_const hw)
  have hkeep₁ : Keeps [6000, 6002] [2803] s₀ t :=
    (((Keeps.refl [6000, 6002] [2803] s₀).setArr (by simp) [0]).setReg (by simp) 0).setReg (by simp) 1
  have hkeep : Keeps [54, 55, 62, 63, 66, 6000, 6002] [2803] s t :=
    (hkeep₀.mono (by simp) (by simp)).trans hkeep₁ (by simp) (by simp)
  have hcounterT : t.regs 6002 = 0 := by simp [t, s₂]
  have hformatT : alg511BinaryRowFormat (t.arrs 2800) (base + 0) := by
    rw [hkeep.2 2800 (by decide), Nat.add_zero]
    exact hformat
  refine ⟨t, .seq he₀ (.seq he₁ (.seq he₂ he₃)), ?_, by simp [t], hcounterT,
    hkeep.2 8 (by decide), hkeep.2 2800 (by decide)⟩
  refine ⟨by rw [hcounterT], (hkeep.1 52 (by decide)).trans hk, ?_,
    ht.frame (fun a ha => hkeep.2 a (by
      simp only [gm06Alg511RetainedSuccessorArrays, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide)),
    (hkeep.2 2801 (by decide)).trans hT, (hkeep.2 2802 (by decide)).trans hD, by simp [t, s₂, s₁], hformatT⟩
  intro r hr
  rw [hkeep₁.1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  exact hz r hr

/-- The actual bounded binary loop, after initialization, decides
the target and retains its encoded linkage on a positive answer.
No large integer is required to fit a machine word: all resource
premises concern graph counts, code lengths and digit widths. The
successor premise is exactly its raw input/output execution contract. -/
theorem alg511_binary_loop_run_exec {w B : ℕ} {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) (hG : IsCylinderSection5Drawing x.drawing.pathCount G)
    (sb si : ℕ) (b d : List ℕ) (base steps increment : ℕ) (start : ℝ) (number : ℤ)
    (callee : Cmd) (s : State) (hw : 3 < 2 ^ w)
    (hsize : max base b.length + (1 + x.drawing.vertexCount / x.drawing.pathCount) + 2 < 2 ^ w)
    (hk : x.drawing.pathCount < 2 ^ w) (hn : x.drawing.vertexCount + 2 < 2 ^ w)
    (he : x.drawing.endpoints.length < 2 ^ w)
    (hpathCap : 1 + x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount < 2 ^ w)
    (hcode : (gm06EncodeSuccessorInput (x.drawing.withLinkage [])).length +
      x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount < 2 ^ w)
    (hbaseWords : ∀ word ∈ gm06EncodeSuccessorInput (x.drawing.withLinkage []), word < 2 ^ w)
    (hsb : sb < 2) (hsi : si < 2) (hb : ∀ v ∈ b, v < 2) (hd : ∀ v ∈ d, v < 2) (hdb : d.length ≤ base)
    (hinc : 0 < increment) (hval : gm06Alg511BinaryRowValue (si :: d) = increment)
    (htarget : gm06Alg511BinaryRowValue (sb :: b) = number + (steps : ℤ) * increment)
    (hstart : IsThetaFeasible x.drawing.pathCount G start)
    (hs : alg511BinaryLoopState rep (sb :: b) (si :: d) base start number increment steps 0 s)
    (hcounter : s.regs 6002 = 0)
    (hcall : ∀ (L : CylinderLinkage x.drawing.pathCount G) (rows : List (List ℕ)) (theta : ℝ)
      (henc : GM06LinkageRowsEncoding L rep.graphTurn.graph.initialTagged rep.graphTurn.graph.vertexLabels
        rep.graphTurn.graph.edgeLabels rows), L.HasTheta theta →
      ∀ ss, ss.arrs 0 = gm06EncodeSuccessorInput (x.drawing.withLinkage rows) →
        ∃ raw u, Exec w callee ss raw u ∧ u ≤ B ∧
          GM06SuccessorOutputRep (rep.withLinkage L rows henc) theta (raw.regs 0) (raw.arrs 8)) :
    ∃ t u, Exec w (.seq (forUp 6002 gm06Alg511BinaryLoopLimit (gm06Alg511BinaryLoopBody callee))
        (.assign 0 (.reg 6000))) s t u ∧
      u ≤ 10 + (1 + x.drawing.vertexCount / x.drawing.pathCount) *
        (12 + alg511BinaryRoundBudget B
          ((gm06EncodeSuccessorInput (x.drawing.withLinkage [])).length +
            x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount)
          base (1 + x.drawing.vertexCount / x.drawing.pathCount) b.length d.length) ∧
      t.regs 0 < 2 ∧
      (t.regs 0 = 1 ↔ IsThetaFeasible x.drawing.pathCount G (start + (steps : ℝ) / x.drawing.pathCount)) ∧
      (t.regs 0 = 0 ↔ ¬ IsThetaFeasible x.drawing.pathCount G (start + (steps : ℝ) / x.drawing.pathCount)) ∧
      (t.regs 0 = 1 → alg511BinaryLoopLinkage rep start steps t) := by
  let cap := 1 + x.drawing.vertexCount / x.drawing.pathCount
  let C := (gm06EncodeSuccessorInput (x.drawing.withLinkage [])).length +
    x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount
  let budget := alg511BinaryRoundBudget B C base cap b.length d.length
  let I : ℕ → State → Prop := fun i st =>
    alg511BinaryLoopState rep (sb :: b) (si :: d) base start number increment steps i st ∧ st.regs 6002 = i
  have hcap : cap < 2 ^ w := by dsimp only [cap]; have := Nat.div_le_self x.drawing.vertexCount x.drawing.pathCount; omega
  have hhi : ∀ i ≤ cap, ∀ st, I i st → st.regs 6002 = i ∧ gm06Alg511BinaryLoopLimit.eval w st = some cap := by
    intro i _ st hI
    exact ⟨hI.2, gm06Alg511BinaryLoopLimit_eval x.drawing.vertexCount x.drawing.pathCount st
      (by omega) hn hG.1 hk hI.1.1.2.2.2.1.1 hI.1.1.2.1⟩
  have hbody : ∀ i < cap, ∀ st, I i st → ∃ t u, Exec w (gm06Alg511BinaryLoopBody callee) st t u ∧
      u ≤ budget ∧ I (i + 1) (t.setReg 6002 (i + 1)) ∧ t.regs 6002 = i := by
    intro i hi st hI
    have hcommon := hI.1.1
    rcases hI.1.2 with hrun | hstop
    · obtain ⟨L, rows, hp, henc, htheta⟩ := hrun.2.2.2.2
      have hlength := alg511_successor_input_length_le rep.graphTurn.graph henc
      change (gm06EncodeSuccessorInput (x.drawing.withLinkage rows)).length ≤ C at hlength
      have hwords := alg511_successor_input_words rep.graphTurn.graph henc hbaseWords hk (by change x.drawing.vertexCount < 2 ^ w; omega) he hpathCap
      change ∀ word ∈ gm06EncodeSuccessorInput (x.drawing.withLinkage rows), word < 2 ^ w at hwords
      obtain ⟨t, u, hex, ht, hnext, hc⟩ := alg511_binary_active_round_exec rep hG sb si b d base i steps increment start number
        callee st hw (by dsimp only [cap] at hi; omega)
        (hi.trans hcap) hsb hsi hb hd hdb hinc hval htarget hcommon hrun L rows hp henc htheta hk
        (hlength.trans_lt hcode) hwords (hcall L rows _ henc htheta)
      have hrows := binary_row_lengths hcommon (by rfl : (sb :: b).length = b.length + 1)
        (by rfl : (si :: d).length = d.length + 1)
      have htBound : u ≤ budget := round_time_le ht hlength
        (hrows.trans (by omega)) rfl (Nat.succ_le_of_lt hi)
      refine ⟨t, u, hex, htBound, ⟨hnext.setCounter (by rfl), by simp⟩, hc.trans hI.2⟩
    · obtain ⟨hex, hnext, hc⟩ := alg511_binary_loop_stopped_round_exec rep (sb :: b) (si :: d) base
        start number increment steps i callee st hcommon hstop hI.2
      exact ⟨st, 2, hex, by dsimp only [budget, alg511BinaryRoundBudget]; omega, ⟨hnext, by simp⟩, hc⟩
  obtain ⟨st, ul, hel, htl, hI⟩ := Crossing.forUp_exec' I cap budget (r_i := 6002)
    (hi := gm06Alg511BinaryLoopLimit) (body := gm06Alg511BinaryLoopBody callee)
    (by omega) hcap hhi hbody s ⟨hs, hcounter⟩
  have hfinished := alg511_binary_finished_at_cap rep hG hstart hI.1.2
  have hcorrect := hfinished.correct
  let t := st.setReg 0 (st.regs 6000)
  have heLast : Exec w (.assign 0 (.reg 6000)) st t 2 :=
    .assign (Crossing.eval_reg rfl (hcorrect.1.trans_le (by omega)))
  have hfinishedT : alg511BinaryLoopFinished rep start steps t :=
    hfinished.frame (State.setReg_regs_ne _ _ (by decide)) (State.setReg_regs_ne _ _ (by decide)) rfl
  have hcorrectT := hfinishedT.correct
  have hbit : t.regs 0 = t.regs 6000 := by simp [t]
  refine ⟨t, ul + 2, .seq hel heLast, ?_, ?_, ?_, ?_, ?_⟩
  · change ul + 2 ≤ 10 + cap * (12 + budget)
    have hcost : gm06Alg511BinaryLoopLimit.cost = 6 := by rfl
    rw [hcost] at htl
    change ul ≤ 8 + cap * (12 + budget) at htl
    omega
  · rw [hbit]; exact hcorrectT.1
  · rw [hbit]; exact hcorrectT.2.1
  · rw [hbit]
    constructor
    · intro hz hp
      have hone := hcorrectT.2.1.mpr hp
      omega
    · intro hno
      have hne : t.regs 6000 ≠ 1 := fun h => hno (hcorrectT.2.1.mp h)
      omega
  · rw [hbit]; exact hcorrectT.2.2

/-- The full binary controller initializes its scalar slots and
guard, then executes the proved bounded loop. Its time is polynomial
in the fixed drawing-code length and supplied binary widths, composed
with the exact successor time bound. The starting paths and value
are computed before this controller is called. -/
theorem alg511_binary_loop_exec {w B : ℕ} {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) (hG : IsCylinderSection5Drawing x.drawing.pathCount G)
    (sb si : ℕ) (b d : List ℕ) (base steps increment : ℕ) (start : ℝ) (number : ℤ)
    (callee : Cmd) (s : State) (hw : 3 < 2 ^ w)
    (hsize : max base b.length + (1 + x.drawing.vertexCount / x.drawing.pathCount) + 2 < 2 ^ w)
    (hk : x.drawing.pathCount < 2 ^ w) (hn : x.drawing.vertexCount + 2 < 2 ^ w)
    (he : x.drawing.endpoints.length < 2 ^ w)
    (hpathCap : 1 + x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount < 2 ^ w)
    (hcode : (gm06EncodeSuccessorInput (x.drawing.withLinkage [])).length +
      x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount < 2 ^ w)
    (hbaseWords : ∀ word ∈ gm06EncodeSuccessorInput (x.drawing.withLinkage []), word < 2 ^ w)
    (hsb : sb < 2) (hsi : si < 2) (hb : ∀ v ∈ b, v < 2) (hd : ∀ v ∈ d, v < 2) (hdb : d.length ≤ base)
    (hinc : 0 < increment) (hval : gm06Alg511BinaryRowValue (si :: d) = increment)
    (htarget : gm06Alg511BinaryRowValue (sb :: b) = number + (steps : ℤ) * increment)
    (hstart : IsThetaFeasible x.drawing.pathCount G start)
    (hTables : alg511BinaryLoopTables x s) (hkReg : s.regs 52 = x.drawing.pathCount)
    (hT : s.arrs 2801 = sb :: b) (hD : s.arrs 2802 = si :: d)
    (hformat : alg511BinaryRowFormat (s.arrs 2800) base)
    (hcurrent : gm06Alg511BinaryRowValue (s.arrs 2800) = number)
    (hL : alg511BinaryLoopLinkage rep start 0 s)
    (hcall : ∀ (L : CylinderLinkage x.drawing.pathCount G) (rows : List (List ℕ)) (theta : ℝ)
      (henc : GM06LinkageRowsEncoding L rep.graphTurn.graph.initialTagged rep.graphTurn.graph.vertexLabels
        rep.graphTurn.graph.edgeLabels rows), L.HasTheta theta →
      ∀ ss, ss.arrs 0 = gm06EncodeSuccessorInput (x.drawing.withLinkage rows) →
        ∃ raw u, Exec w callee ss raw u ∧ u ≤ B ∧
          GM06SuccessorOutputRep (rep.withLinkage L rows henc) theta (raw.regs 0) (raw.arrs 8)) :
    ∃ t u, Exec w (gm06Alg511BinaryLoopProg callee) s t u ∧
      u ≤ 430 + 350 * (base + b.length + 1) +
        (1 + x.drawing.vertexCount / x.drawing.pathCount) *
        (12 + alg511BinaryRoundBudget B
          ((gm06EncodeSuccessorInput (x.drawing.withLinkage [])).length +
            x.drawing.pathCount + x.drawing.pathCount * x.drawing.vertexCount)
          base (1 + x.drawing.vertexCount / x.drawing.pathCount) b.length d.length) ∧
      t.regs 0 < 2 ∧
      (t.regs 0 = 1 ↔ IsThetaFeasible x.drawing.pathCount G (start + (steps : ℝ) / x.drawing.pathCount)) ∧
      (t.regs 0 = 0 ↔ ¬ IsThetaFeasible x.drawing.pathCount G (start + (steps : ℝ) / x.drawing.pathCount)) ∧
      (t.regs 0 = 1 → alg511BinaryLoopLinkage rep start steps t) := by
  obtain ⟨s₁, he₁, hc₁, hf₁, hcounter₁, hp₁, ha₁⟩ := alg511_binary_loop_prefix_exec
    (w := w) (sb :: b) (si :: d) base s (by omega) hTables hkReg hT hD hformat
  obtain ⟨s₂, ug, heg, htg, hs₂, hcounter₂⟩ := alg511_binary_guard_linkage_exec rep sb b (si :: d)
    base 0 steps increment start number s₁ hw (by
      exact (Nat.add_le_add_right (Nat.add_le_add_left (Nat.zero_le (1 + x.drawing.vertexCount / x.drawing.pathCount)) _) 2).trans_lt hsize) hsb hb hinc (Nat.zero_le _) hc₁ hf₁
      (by simpa only [Nat.cast_zero, zero_mul, add_zero] using (congrArg gm06Alg511BinaryRowValue ha₁).trans hcurrent)
      htarget (hL.frame hp₁)
  obtain ⟨t, ul, hel, htl, hbit, hyes, hno, hpath⟩ := alg511_binary_loop_run_exec rep hG sb si b d base steps increment start number
    callee s₂ hw hsize hk hn he hpathCap hcode hbaseWords hsb hsi hb hd hdb hinc hval htarget hstart hs₂
      (hcounter₂.trans hcounter₁) hcall
  refine ⟨t, 16 + (ug + ul), .seq he₁ (.seq heg hel), ?_, hbit, hyes, hno, hpath⟩
  have hg : ug ≤ 404 + 350 * (base + b.length + 1) := by simpa only [Nat.add_zero] using htg
  omega

end GraphMinor.GM06
