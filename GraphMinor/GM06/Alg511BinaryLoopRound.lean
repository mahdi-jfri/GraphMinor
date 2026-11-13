module

public import GraphMinor.GM06.Alg511BinaryLoopGuard
public import GraphMinor.GM06.Alg511SuccessorSize
import Mathlib.Tactic

/-!
# Active binary rounds of the feasibility algorithm

Attach the current ordinary path rows to the fixed positive drawing
input and call the exact successor interface. The protected call
retains the binary current value, target and increment. On success,
add the increment with the signed binary program and retain the
returned actual linkage. On failure, VI (5.8) rules out the larger
target. The exact binary guard then gives the next reached state.
These are the active cases of VI (5.11), page 134. The execution
lemmas compose a command with its successor contract, rather than
asserting the existence of the numbered algorithm.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Compute.TwoPaths GraphMinor.Surface

private theorem add_time_bound {u a d base i : ℕ}
    (ht : u ≤ 400 + 350 * (a + d + 1)) (ha : a ≤ base + i) :
    u ≤ 400 + 350 * (base + i + d + 1) :=
  ht.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left 350 (Nat.add_le_add_right (Nat.add_le_add_right ha d) 1)) 400)

/-- A concrete binary addition advances the current row by the
fixed integer increment. It retains the actual path rows, all
common data and the ordinary controller counter. -/
theorem alg511_binary_increment_exec {w : ℕ} {x : GM06Alg511WindingInput}
    (target : List ℕ) (si : ℕ) (d : List ℕ) (base i : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : base + i + 2 < 2 ^ w)
    (hsi : si < 2) (hbits : ∀ digit ∈ d, digit < 2) (hd : d.length ≤ base)
    (hc : alg511BinaryLoopCommon x target (si :: d) base i s) :
    ∃ t u, Exec w (gm06Alg511BinaryRowAddProg 2800 2802 2800) s t u ∧
      u ≤ 400 + 350 * (base + i + d.length + 1) ∧
      alg511BinaryLoopCommon x target (si :: d) base (i + 1) t ∧
      gm06Alg511BinaryRowValue (t.arrs 2800) =
        gm06Alg511BinaryRowValue (s.arrs 2800) + gm06Alg511BinaryRowValue (si :: d) ∧
      t.regs 6000 = s.regs 6000 ∧ t.regs 6002 = s.regs 6002 ∧ t.arrs 8 = s.arrs 8 := by
  obtain ⟨sa, a, hA, hsa, hlen, habits⟩ := hc.2.2.2.2.2.2.2
  obtain ⟨t, u, out, sign, he, ht, hk, hout, hs, hl, hb, hv⟩ :=
    gm06Alg511BinaryRowAddProg_exec (w := w) 2800 2802 2800 (by decide) (by decide) (by decide)
      a d sa si s hw (by omega) habits hbits hsa hsi hA hc.2.2.2.2.2.1
  have hcommon : alg511BinaryLoopCommon x target (si :: d) base (i + 1) t := hc.update
    (by
      intro r hr
      apply hk.1 r
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by
      intro a ha
      apply hk.2 a
      simp only [gm06Alg511RetainedSuccessorArrays, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with (rfl | rfl | rfl | rfl | rfl) | rfl | rfl <;> decide)
    (by rw [hk.1 6002 (by decide)]; exact hc.1.trans (Nat.le_succ i))
    (by rw [hk.2 2803 (by decide)]; exact hc.2.2.2.2.2.2.1)
    ⟨sign, out, hout, hs, by omega, hb⟩
  refine ⟨t, u, he, add_time_bound ht hlen, hcommon, ?_, hk.1 6000 (by decide),
    hk.1 6002 (by decide), hk.2 8 (by decide)⟩
  simpa only [hout, hA] using hv

/-- A packed call can use arbitrary scratch storage. Its exact
input relation comes from the retained positive drawing and current
ordinary path rows; the protected binary values and graph data
retain their meanings afterwards. -/
theorem alg511_binary_call_exec {w B : ℕ} {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) (target incrementRow : List ℕ) (base i : ℕ)
    (L : CylinderLinkage x.drawing.pathCount G) (rows : List (List ℕ))
    (henc : GM06LinkageRowsEncoding L rep.graphTurn.graph.initialTagged rep.graphTurn.graph.vertexLabels
      rep.graphTurn.graph.edgeLabels rows) (theta : ℝ) (callee : Cmd) (s : State)
    (hw : 1 < 2 ^ w) (hk : x.drawing.pathCount < 2 ^ w)
    (hfit : (gm06EncodeSuccessorInput (x.drawing.withLinkage rows)).length < 2 ^ w)
    (hwords : ∀ word ∈ gm06EncodeSuccessorInput (x.drawing.withLinkage rows), word < 2 ^ w)
    (hbinary : ∀ a ∈ ([2800, 2801, 2802] : List ℕ), (s.arrs a).length < 2 ^ w ∧ ∀ d ∈ s.arrs a, d < 2 ^ w)
    (hic : i < 2 ^ w) (hc : alg511BinaryLoopCommon x target incrementRow base i s)
    (hf : s.regs 6000 = 1) (hp : s.arrs 8 = gm06EncodeRows rows)
    (hcall : ∀ ss, ss.arrs 0 = gm06EncodeSuccessorInput (x.drawing.withLinkage rows) →
      ∃ raw u, Exec w callee ss raw u ∧ u ≤ B ∧
        GM06SuccessorOutputRep (rep.withLinkage L rows henc) theta (raw.regs 0) (raw.arrs 8)) :
    ∃ t u, Exec w (gm06Alg511BinaryCountedSuccessorCall callee) s t u ∧
      u ≤ B + 215 + 68 * (gm06EncodeSuccessorInput (x.drawing.withLinkage rows)).length +
        24 * (([2800, 2801, 2802] : List ℕ).map (fun a => (s.arrs a).length)).sum ∧
      alg511BinaryLoopCommon x target incrementRow base i t ∧ t.regs 6000 = 1 ∧
      t.regs 6002 = s.regs 6002 ∧ t.arrs 2800 = s.arrs 2800 ∧
      GM06SuccessorOutputRep (rep.withLinkage L rows henc) theta (t.regs 0) (t.arrs 8) := by
  obtain ⟨t, raw, u, he, ht, hpRaw, hbit, hpath, ha, hm, hcounter, hr⟩ :=
    gm06Alg511BinaryCountedSuccessorCall_exec callee (x.drawing.withLinkage rows) s hw hfit hwords
      (hc.fields rows hp) hbinary hc.2.2.2.2.2.2.1 (hc.1.trans_lt hic)
      (hc.scalar_words hw hk (by rw [hf]; decide))
      (fun raw => GM06SuccessorOutputRep (rep.withLinkage L rows henc) theta (raw.regs 0) (raw.arrs 8)) hcall
  have hcurrent := ha 2800 (by simp)
  have hcommon : alg511BinaryLoopCommon x target incrementRow base i t := hc.update
    (by
      intro r hmem
      apply hr r
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
      tauto)
    (by
      intro a hmem
      apply ha a
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
      tauto)
    (by rw [hcounter]; exact hc.1) (by rw [hm]; rfl)
    (by rw [hcurrent]; exact hc.2.2.2.2.2.2.2)
  exact ⟨t, u, he, ht, hcommon, (hr 6000 (by simp)).trans hf, hcounter, hcurrent,
    by simpa only [hbit, hpath] using hpRaw⟩

private theorem round_theta_lt {k i steps : ℕ} (hk : 0 < k) (hi : i < steps) (start : ℝ) :
    start + (i : ℝ) / k < start + (steps : ℝ) / k := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hiR : (i : ℝ) < steps := by exact_mod_cast hi
  simpa only [add_comm] using add_lt_add_left ((div_lt_div_iff_of_pos_right hkR).mpr hiR) start

private theorem round_theta_succ (start : ℝ) (k i : ℕ) :
    start + (i : ℝ) / k + 1 / k = start + ((i + 1 : ℕ) : ℝ) / k := by
  push_cast
  ring

/-- An active successor round reaches the next running state or a
proved stopped state. The only successor premise is the exact raw
array-zero input / bit-and-ordinary-path output execution contract.
All binary arithmetic and graph data preservation are proved here. -/
theorem alg511_binary_active_round_exec {w B : ℕ} {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G) (hG : IsCylinderSection5Drawing x.drawing.pathCount G)
    (sb si : ℕ) (b d : List ℕ) (base i steps increment : ℕ) (start : ℝ) (number : ℤ)
    (callee : Cmd) (s : State) (hw : 3 < 2 ^ w)
    (hsize : max base b.length + (i + 1) + 2 < 2 ^ w) (hic : i < 2 ^ w)
    (hsb : sb < 2) (hsi : si < 2) (hb : ∀ v ∈ b, v < 2) (hd : ∀ v ∈ d, v < 2) (hdb : d.length ≤ base)
    (hinc : 0 < increment) (hval : gm06Alg511BinaryRowValue (si :: d) = increment)
    (htarget : gm06Alg511BinaryRowValue (sb :: b) = number + (steps : ℤ) * increment)
    (hcommon : alg511BinaryLoopCommon x (sb :: b) (si :: d) base i s)
    (hrun : alg511BinaryLoopRunning rep start number increment steps i s)
    (L : CylinderLinkage x.drawing.pathCount G) (rows : List (List ℕ))
    (hpaths : s.arrs 8 = gm06EncodeRows rows)
    (henc : GM06LinkageRowsEncoding L rep.graphTurn.graph.initialTagged rep.graphTurn.graph.vertexLabels rep.graphTurn.graph.edgeLabels rows)
    (htheta : L.HasTheta (start + (i : ℝ) / x.drawing.pathCount))
    (hk : x.drawing.pathCount < 2 ^ w)
    (hfit : (gm06EncodeSuccessorInput (x.drawing.withLinkage rows)).length < 2 ^ w)
    (hwords : ∀ word ∈ gm06EncodeSuccessorInput (x.drawing.withLinkage rows), word < 2 ^ w)
    (hcall : ∀ ss, ss.arrs 0 = gm06EncodeSuccessorInput (x.drawing.withLinkage rows) →
      ∃ raw u, Exec w callee ss raw u ∧ u ≤ B ∧
        GM06SuccessorOutputRep (rep.withLinkage L rows henc) (start + (i : ℝ) / x.drawing.pathCount)
          (raw.regs 0) (raw.arrs 8)) :
    ∃ t u, Exec w (gm06Alg511BinaryLoopBody callee) s t u ∧
      u ≤ B + 215 + 68 * (gm06EncodeSuccessorInput (x.drawing.withLinkage rows)).length +
        24 * (([2800, 2801, 2802] : List ℕ).map (fun a => (s.arrs a).length)).sum +
        (400 + 350 * (base + i + d.length + 1)) +
        (404 + 350 * (base + (i + 1) + b.length + 1)) + 4 ∧
      alg511BinaryLoopState rep (sb :: b) (si :: d) base start number increment steps (i + 1) t ∧
      t.regs 6002 = s.regs 6002 := by
  have hbinary := hcommon.binary_words (w := w) (cap := i) (targetWidth := b.length) (incrementWidth := d.length)
    (by rfl) ⟨sb, b, rfl, hsb, by rfl, hb⟩ ⟨si, d, rfl, hsi, by rfl, hd⟩ (by omega) (by omega)
  obtain ⟨st, uc, hec, htc, hc, hf, hcounter, hcurrent, hout⟩ := alg511_binary_call_exec rep (sb :: b) (si :: d) base i
    L rows henc (start + (i : ℝ) / x.drawing.pathCount) callee s (by omega) hk hfit hwords hbinary hic hcommon hrun.1 hpaths hcall
  rcases hout with hno | hyes
  · have hnot := alg511_reject_of_no_successor hG ⟨L, htheta⟩
      (round_theta_lt hG.1 hrun.2.2.1 start) hno.2
    let sz := st.setReg 6000 0
    have hez : Exec w (.assign 6000 (.const 0)) st sz 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
    have hcZ : alg511BinaryLoopCommon x (sb :: b) (si :: d) base (i + 1) sz := hc.update
      (by
        intro r hr
        apply State.setReg_regs_ne
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (fun _ _ => rfl) (by simpa only [sz, State.setReg_regs_ne _ _ (by decide : (6002 : ℕ) ≠ 6000)] using hc.1.trans (Nat.le_succ i))
      hc.2.2.2.2.2.2.1 (hc.2.2.2.2.2.2.2.mono (Nat.add_le_add_left (Nat.le_succ i) base))
    obtain ⟨t, ug, heg, htg, ht, hcounterG⟩ := alg511_binary_guard_rejected_exec rep sb b (si :: d) base (i + 1) steps increment start number sz
      hw hsize hsb hb hcZ (by simp [sz]) hnot
    have hcounterT : t.regs 6002 = s.regs 6002 :=
      (hcounterG.trans (State.setReg_regs_ne _ _ (by decide))).trans hcounter
    refine ⟨t, 1 + (uc + ((1 + 2) + ug)), .ite_true (Crossing.eval_reg hrun.2.1 (by omega)) (by decide)
      (.seq hec (.seq (.ite_false (Crossing.eval_reg hno.1 (Nat.two_pow_pos w)) hez) heg)), ?_, ht, hcounterT⟩
    omega
  · obtain ⟨hone, M, rs, hrows, hthetaM, hencM⟩ := hyes
    have hLM : alg511BinaryLoopLinkage rep start (i + 1) st :=
      ⟨M, rs, hrows, hencM, by simpa only [round_theta_succ] using hthetaM⟩
    obtain ⟨sa, ua, hea, hta, hcA, hvalue, hfA, hcounterA, hpA⟩ :=
      alg511_binary_increment_exec (sb :: b) si d base i st hw (by omega) hsi hd hdb hc
    have hvalueA : gm06Alg511BinaryRowValue (sa.arrs 2800) = number + ((i + 1 : ℕ) : ℤ) * increment := by
      rw [hvalue, hcurrent, hrun.2.2.2.1, hval]
      push_cast
      ring
    obtain ⟨t, ug, heg, htg, ht, hcounterG⟩ := alg511_binary_guard_linkage_exec rep sb b (si :: d) base (i + 1) steps increment start number sa
      hw hsize hsb hb hinc (Nat.succ_le_of_lt hrun.2.2.1) hcA (hfA.trans hf) hvalueA htarget (hLM.frame hpA)
    have hcounterT : t.regs 6002 = s.regs 6002 :=
      (hcounterG.trans hcounterA).trans hcounter
    refine ⟨t, 1 + (uc + ((1 + ua) + ug)), .ite_true (Crossing.eval_reg hrun.2.1 (by omega)) (by decide)
      (.seq hec (.seq (.ite_true (Crossing.eval_reg hone (by omega)) (by decide) hea) heg)), ?_, ht, hcounterT⟩
    omega

end GraphMinor.GM06
