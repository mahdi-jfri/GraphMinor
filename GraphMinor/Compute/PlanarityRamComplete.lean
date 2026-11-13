module

public import GraphMinor.Compute.PlanarityRamBoundedFinish

/-!
# Completing a DFS vertex

Completion removes the exhausted frame, appends its vertex, and finishes
the incoming edge when present. The incoming pointer and all record fields
are bounded by the search data invariant. No record is allocated here.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- Finish the incoming edge of a completed vertex, when it exists. -/
def finishIncoming (search : Search) (v : ℕ) : Search :=
  match search.parentEdge[v]?.join with
  | none => search
  | some p => finishEdge search p

/-- The incoming-edge part of completion takes at most seventy-eight steps
under the bounded-data invariant and a linear word bound. -/
theorem finishIncomingProg_refines {N M w : ℕ} {s : State} {search : Search}
    {stack : List Frame} (h : DfsSearchAt N M s search) (hf : FramesAt N s stack)
    (hb : SearchBounded N search) (v : ℕ) (hv : v < N) (hr : s.regs 41 = v)
    (hw : 2 * (N + search.edges.size + 1) < 2 ^ w) :
    ∃ s' t, Exec w finishIncomingProg s s' t ∧ t ≤ 78 ∧ FramesAt N s' stack ∧
      DfsSearchAt N M s' (finishIncoming search v) := by
  have hvp : v < search.parentEdge.size := by rw [hb.2.2.1]; exact hv
  have hvw : v < 2 ^ w := by omega
  have hz : 0 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hprefix : PrefixAt s Field.parentEdge.array N (search.parentEdge.toList.map optionWord) :=
    h.2.2.2.2.2.2.2.1
  cases hpar : search.parentEdge[v]?.join with
  | none =>
    have hraw : search.parentEdge[v] = none := by
      simpa only [Array.getElem?_eq_getElem hvp, Option.join_some] using hpar
    have eread : (Expr.read Field.parentEdge.array (.reg 41)).eval w s = some 0 := by
      simpa only [hraw, optionWord] using hprefix.read_option_reg hvp hr hvw
        (by simpa only [hraw, optionWord] using hz)
    let s1 := s.setReg 45 0
    have hx1 : Exec w (.assign 45 (.read Field.parentEdge.array (.reg 41))) s s1 3 :=
      Exec.assign eread
    have hx2 : Exec w (.ite (.reg 45)
        (.seq (.assign 45 (.op .sub (.reg 45) (.const 1))) finishEdgeProg) .skip) s1 s1 2 :=
      Exec.ite_false (by simp [Expr.eval, s1]) (Exec.skip s1)
    refine ⟨s1, 5, Exec.seq hx1 hx2, by omega, hf.setReg 45 0 (by decide), ?_⟩
    simp only [finishIncoming, hpar]
    change SearchAt N M s1 (reversePostorder search)
    exact h.setReg 45 0 (by decide) (by decide)
  | some p =>
    have hp : p < search.edges.size := hb.2.2.2.2.2.1 ⟨v, hv⟩ p hpar
    have hpw : p + 1 < 2 ^ w := by omega
    have hraw : search.parentEdge[v] = some p := by
      simpa only [Array.getElem?_eq_getElem hvp, Option.join_some] using hpar
    have eread : (Expr.read Field.parentEdge.array (.reg 41)).eval w s = some (p + 1) := by
      simpa only [hraw, optionWord] using hprefix.read_option_reg hvp hr hvw
        (by simpa only [hraw, optionWord] using hpw)
    let s1 := s.setReg 45 (p + 1)
    let s2 := s1.setReg 45 p
    have h2 : DfsSearchAt N M s2 search :=
      (h.setReg 45 (p + 1) (by decide) (by decide)).setReg 45 p (by decide) (by decide)
    have hf2 : FramesAt N s2 stack := (hf.setReg 45 (p + 1) (by decide)).setReg 45 p (by decide)
    have hx1 : Exec w (.assign 45 (.read Field.parentEdge.array (.reg 41))) s s1 3 :=
      Exec.assign eread
    have hx2 : Exec w (.assign 45 (.op .sub (.reg 45) (.const 1))) s1 s2 4 := by
      apply Exec.assign
      simp [Expr.eval, s1, BinOp.eval, BinOp.raw, checkWord_of_lt hpw,
        checkWord_of_lt hone, checkWord_of_lt (show p < 2 ^ w by omega)]
    obtain ⟨s3, t3, hx3, ht3, hf3, hs3⟩ := finishEdgeProg_refines_bounded h2 hf2 hb p hp
      (by simp [s2]) hw
    have hcond : (Expr.reg 45).eval w s1 = some (p + 1) := by
      simpa [Expr.eval, s1] using checkWord_of_lt hpw
    refine ⟨s3, 3 + (1 + (4 + t3)), Exec.seq hx1
      (Exec.ite_true hcond (by omega) (Exec.seq hx2 hx3)), by omega, hf3, ?_⟩
    simpa only [finishIncoming, hpar] using hs3

/-- Completing a loaded vertex takes at most eighty-nine steps. The bounds
also ask for one free postorder slot and a bounded nonempty frame count. -/
theorem completeFrameProg_refines {N M w : ℕ} {s : State} {search : Search}
    {stack : List Frame} {f : Frame} (h : DfsSearchAt N M s search)
    (hf : FramesAt N s (f :: stack)) (hb : SearchBounded N search)
    (hv : f.vertex < N) (hr : s.regs 41 = f.vertex)
    (hpost : search.postorder.length < N) (hcount : stack.length + 1 < 2 ^ w)
    (hpostw : search.postorder.length + 1 < 2 ^ w)
    (hw : 2 * (N + search.edges.size + 1) < 2 ^ w) :
    ∃ s' t, Exec w completeFrameProg s s' t ∧ t ≤ 89 ∧ FramesAt N s' stack ∧
      DfsSearchAt N M s'
        (finishIncoming { search with postorder := f.vertex :: search.postorder } f.vertex) := by
  obtain ⟨hx1, hf1, hs1⟩ := popFrameProg_refines hf h hcount
  let s1 := s.setReg 38 stack.length
  have hr1 : s1.regs 41 = f.vertex := by simpa [s1] using hr
  have hvw : f.vertex < 2 ^ w := by omega
  obtain ⟨s2, hx2, hs2⟩ := appendPostorderProg_refines hs1 f.vertex hr1 hpost hvw hpostw
  have hf2 := hf1.appendPostorder_exec hx2
  have hr2 : s2.regs 41 = f.vertex := (hx2.regs_eq_of_not_mem_writtenRegs
    (by simp [appendPostorderProg, Cmd.writtenRegs])).trans hr1
  obtain ⟨s3, t3, hx3, ht3, hf3, hs3⟩ := finishIncomingProg_refines hs2 hf2 hb f.vertex hv hr2 hw
  exact ⟨s3, 4 + (7 + t3), Exec.seq hx1 (Exec.seq hx2 hx3), by omega, hf3, hs3⟩

end GraphMinor.Compute.PlanarityRam
