module

public import GraphMinor.Compute.GM06CutRowEncoding

/-!
# Decoding the current cut position

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) distinguishes
interior, initial, terminal and nonlinkage vertices by their incoming
and outgoing path marks. This command makes that distinction from
the two stored plus-one marks. It installs the local kind, cuff ends
and left interval bounds. The proof splits on those two zero tests.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Decode one vertex's four computed table entries. -/
def gm06CutPositionOfMarks (a b cp cn : ℕ) : Option GM06CutPosition :=
  if a = 0 then if b = 0 then none else some (.start (b - 1) cp cn)
  else if b = 0 then some (.terminal (a - 1) cp cn)
  else some (.interior (a - 1) (b - 1))

/-- Decoding at a vertex is exactly decoding its four table entries. -/
theorem gm06CutPositionAt_eq_ofMarks (marks : GM06CutTables) (v : ℕ) :
    gm06CutPositionAt marks v = gm06CutPositionOfMarks
      (marks.incoming[v]?.getD 0) (marks.outgoing[v]?.getD 0)
      (marks.cuffPositive[v]?.getD 0) (marks.cuffNegative[v]?.getD 0) := rfl

/-- The two path marks are recovered unchanged by their decoded position. -/
theorem gm06CutPositionOfMarks_ends (a b cp cn : ℕ) :
    gm06CutPositionIncoming (gm06CutPositionOfMarks a b cp cn) = a ∧
    gm06CutPositionOutgoing (gm06CutPositionOfMarks a b cp cn) = b := by
  unfold gm06CutPositionOfMarks
  split_ifs <;> simp only [gm06CutPositionIncoming, gm06CutPositionOutgoing] <;> omega

/-- Final local-register data, with irrelevant cuff entries set to zero. -/
def gm06CutDecodedState (s : State) (p : Option GM06CutPosition) : State :=
  ((((s.setReg 668 (gm06CutPositionKind p)).setReg 671 (gm06CutPositionCuffs p).1).setReg 672
    (gm06CutPositionCuffs p).2).setReg 673 (gm06CutPositionBounds p).1).setReg 674
      (gm06CutPositionBounds p).2

/-- Install a case's fixed kind and its two computed interval bounds. -/
def gm06CutInstallPositionProg (kind : ℕ) (clearCuffs : Bool) (first last : Expr) : Cmd :=
  .seq (.assign 668 (.const kind))
    (.seq (.assign 671 (if clearCuffs then .const 0 else .reg 671))
      (.seq (.assign 672 (if clearCuffs then .const 0 else .reg 672))
        (.seq (.assign 673 first) (.assign 674 last))))

/-- Decode the current vertex's marks in 669--672. No side test is supplied. -/
def gm06CutDecodePositionProg : Cmd :=
  .ite (.reg 669)
    (.ite (.reg 670)
      (gm06CutInstallPositionProg 0 true (.op .sub (.reg 670) (.const 1))
        (.op .sub (.reg 669) (.const 1)))
      (gm06CutInstallPositionProg 1 false (.reg 671) (.op .sub (.reg 669) (.const 1))))
    (.ite (.reg 670)
      (gm06CutInstallPositionProg 1 false (.op .sub (.reg 670) (.const 1)) (.reg 671))
      (gm06CutInstallPositionProg 2 true (.const 0) (.const 0)))

/-- A branch installs the designated data by five assignments. The
four expressions are evaluated in their actual intermediate states. -/
private theorem install_exec {w kind cp cn first last : ℕ} (clear : Bool)
    (ef el : Expr) (s : State) (hw : kind < 2 ^ w)
    (hcp : (if clear then Expr.const 0 else .reg 671).eval w (s.setReg 668 kind) = some cp)
    (hcn : (if clear then Expr.const 0 else .reg 672).eval w
      ((s.setReg 668 kind).setReg 671 cp) = some cn)
    (hf : ef.eval w (((s.setReg 668 kind).setReg 671 cp).setReg 672 cn) = some first)
    (hl : el.eval w ((((s.setReg 668 kind).setReg 671 cp).setReg 672 cn).setReg 673 first) = some last) :
    Exec w (gm06CutInstallPositionProg kind clear ef el) s
      (((((s.setReg 668 kind).setReg 671 cp).setReg 672 cn).setReg 673 first).setReg 674 last)
      (5 + 1 + (if clear then Expr.const 0 else .reg 671).cost +
        (if clear then Expr.const 0 else .reg 672).cost + ef.cost + el.cost) := by
  have he := Exec.seq (Exec.assign (GraphMinor.Compute.Crossing.eval_const hw))
    (.seq (.assign hcp) (.seq (.assign hcn) (.seq (.assign hf) (.assign (r := 674) hl))))
  have ht : (Expr.const kind).cost + 1 +
      ((if clear then Expr.const 0 else .reg 671).cost + 1 +
        ((if clear then Expr.const 0 else .reg 672).cost + 1 + (ef.cost + 1 + (el.cost + 1)))) =
      5 + 1 + (if clear then Expr.const 0 else .reg 671).cost +
        (if clear then Expr.const 0 else .reg 672).cost + ef.cost + el.cost := by
    simp only [Expr.cost]
    omega
  rw [ht] at he
  simpa only [gm06CutInstallPositionProg] using he

/-- Exact execution of the local decoder in at most sixteen steps.
All case data is read from the two path marks and signed cuff words. -/
theorem gm06CutDecodePositionProg_exec {w a b cp cn : ℕ} (s : State)
    (hw : 2 < 2 ^ w) (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (hcp : cp < 2 ^ w) (hcn : cn < 2 ^ w)
    (h669 : s.regs 669 = a) (h670 : s.regs 670 = b)
    (h671 : s.regs 671 = cp) (h672 : s.regs 672 = cn) :
    ∃ t, Exec w gm06CutDecodePositionProg s
      (gm06CutDecodedState s (gm06CutPositionOfMarks a b cp cn)) t ∧ t ≤ 16 := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw0 := Nat.two_pow_pos w
  have hea := GraphMinor.Compute.Crossing.eval_reg h669 ha
  have heb := GraphMinor.Compute.Crossing.eval_reg h670 hb
  by_cases haz : a = 0 <;> by_cases hbz : b = 0
  · have he := install_exec (w := w) (kind := 2) (cp := 0) (cn := 0) (first := 0) (last := 0)
      true (.const 0) (.const 0) s hw
      (GraphMinor.Compute.Crossing.eval_const hw0) (GraphMinor.Compute.Crossing.eval_const hw0)
      (GraphMinor.Compute.Crossing.eval_const hw0) (GraphMinor.Compute.Crossing.eval_const hw0)
    refine ⟨12, ?_, by decide⟩
    simpa only [gm06CutDecodePositionProg, gm06CutDecodedState, gm06CutPositionOfMarks,
      haz, hbz, ↓reduceIte, gm06CutPositionKind, gm06CutPositionCuffs, gm06CutPositionBounds,
      Expr.cost, Nat.reduceAdd, Bool.false_eq_true, ↓reduceIte] using
      (Exec.ite_false (cond := .reg 669) (by simpa only [haz] using hea) (Exec.ite_false (cond := .reg 670) (by simpa only [hbz] using heb) he))
  · have he := install_exec (w := w) (kind := 1) (cp := cp) (cn := cn) (first := b - 1) (last := cp)
      false (.op .sub (.reg 670) (.const 1)) (.reg 671) s hw1
      (GraphMinor.Compute.Crossing.eval_reg (by simp [h671]) hcp)
      (GraphMinor.Compute.Crossing.eval_reg (by simp [h672]) hcn)
      (GraphMinor.Compute.Crossing.eval_sub (GraphMinor.Compute.Crossing.eval_reg (by simp [h670]) hb)
        (GraphMinor.Compute.Crossing.eval_const hw1))
      (GraphMinor.Compute.Crossing.eval_reg (by simp) hcp)
    refine ⟨14, ?_, by decide⟩
    simpa only [gm06CutDecodePositionProg, gm06CutDecodedState, gm06CutPositionOfMarks,
      haz, hbz, ↓reduceIte, gm06CutPositionKind, gm06CutPositionCuffs, gm06CutPositionBounds,
      GM06CutPosition.leftBounds, Expr.cost, Nat.reduceAdd, Bool.false_eq_true, ↓reduceIte] using
      (Exec.ite_false (cond := .reg 669) (by simpa only [haz] using hea) (Exec.ite_true (cond := .reg 670) heb hbz he))
  · have he := install_exec (w := w) (kind := 1) (cp := cp) (cn := cn) (first := cp) (last := a - 1)
      false (.reg 671) (.op .sub (.reg 669) (.const 1)) s hw1
      (GraphMinor.Compute.Crossing.eval_reg (by simp [h671]) hcp)
      (GraphMinor.Compute.Crossing.eval_reg (by simp [h672]) hcn)
      (GraphMinor.Compute.Crossing.eval_reg (by simp) hcp)
      (GraphMinor.Compute.Crossing.eval_sub (GraphMinor.Compute.Crossing.eval_reg (by simp [h669]) ha)
        (GraphMinor.Compute.Crossing.eval_const hw1))
    refine ⟨14, ?_, by decide⟩
    simpa only [gm06CutDecodePositionProg, gm06CutDecodedState, gm06CutPositionOfMarks,
      haz, hbz, ↓reduceIte, gm06CutPositionKind, gm06CutPositionCuffs, gm06CutPositionBounds,
      GM06CutPosition.leftBounds, Expr.cost, Nat.reduceAdd, Bool.false_eq_true, ↓reduceIte] using
      (Exec.ite_true (cond := .reg 669) hea haz (Exec.ite_false (cond := .reg 670) (by simpa only [hbz] using heb) he))
  · have he := install_exec (w := w) (kind := 0) (cp := 0) (cn := 0) (first := b - 1) (last := a - 1)
      true (.op .sub (.reg 670) (.const 1)) (.op .sub (.reg 669) (.const 1)) s hw0
      (GraphMinor.Compute.Crossing.eval_const hw0) (GraphMinor.Compute.Crossing.eval_const hw0)
      (GraphMinor.Compute.Crossing.eval_sub (GraphMinor.Compute.Crossing.eval_reg (by simp [h670]) hb)
        (GraphMinor.Compute.Crossing.eval_const hw1))
      (GraphMinor.Compute.Crossing.eval_sub (GraphMinor.Compute.Crossing.eval_reg (by simp [h669]) ha)
        (GraphMinor.Compute.Crossing.eval_const hw1))
    refine ⟨16, ?_, by decide⟩
    simpa only [gm06CutDecodePositionProg, gm06CutDecodedState, gm06CutPositionOfMarks,
      haz, hbz, ↓reduceIte, gm06CutPositionKind, gm06CutPositionCuffs, gm06CutPositionBounds,
      GM06CutPosition.leftBounds, Expr.cost, Nat.reduceAdd, Bool.false_eq_true, ↓reduceIte] using (Exec.ite_true (cond := .reg 669) hea haz (Exec.ite_true (cond := .reg 670) heb hbz he))

/-- Load the four computed table entries for vertex 666. -/
def gm06CutLoadPositionProg : Cmd :=
  .seq (.assign 669 (.read 620 (.reg 666)))
    (.seq (.assign 670 (.read 621 (.reg 666)))
      (.seq (.assign 671 (.read 623 (.reg 666))) (.assign 672 (.read 624 (.reg 666)))))

/-- The state after loading one vertex's incoming, outgoing and cuff words. -/
def gm06CutLoadedState (s : State) (marks : GM06CutTables) (v : ℕ) : State :=
  (((s.setReg 669 (marks.incoming[v]?.getD 0)).setReg 670 (marks.outgoing[v]?.getD 0)).setReg 671
    (marks.cuffPositive[v]?.getD 0)).setReg 672 (marks.cuffNegative[v]?.getD 0)

private theorem table_word_eval {w n v src : ℕ} (table : List ℕ) (s : State)
    (hn : n < 2 ^ w) (hv : v < n) (hlen : table.length = n)
    (hwords : ∀ x ∈ table, x < 2 ^ w) (ha : s.arrs src = table) (hr : s.regs 666 = v) :
    (Expr.read src (.reg 666)).eval w s = some (table[v]?.getD 0) := by
  have hi : v < table.length := hlen ▸ hv
  have he := GraphMinor.Compute.Crossing.eval_read (a := src) (s := s)
    (GraphMinor.Compute.Crossing.eval_reg hr (hv.trans hn))
    (by simpa only [ha] using hi) (by simpa only [ha] using hwords _ (List.getElem_mem hi))
  simpa only [ha, List.getElem?_eq_getElem hi, Option.getD_some] using he

/-- The table reads give the exact four stored words in twelve steps. -/
theorem gm06CutLoadPositionProg_exec {w n v : ℕ} (marks : GM06CutTables) (s : State)
    (hn : n < 2 ^ w) (hv : v < n)
    (hlens : marks.incoming.length = n ∧ marks.outgoing.length = n ∧
      marks.cuffPositive.length = n ∧ marks.cuffNegative.length = n)
    (hwords : ∀ x ∈ marks.incoming ++ marks.outgoing ++ marks.cuffPositive ++ marks.cuffNegative, x < 2 ^ w)
    (h620 : s.arrs 620 = marks.incoming) (h621 : s.arrs 621 = marks.outgoing)
    (h623 : s.arrs 623 = marks.cuffPositive) (h624 : s.arrs 624 = marks.cuffNegative)
    (h666 : s.regs 666 = v) :
    Exec w gm06CutLoadPositionProg s (gm06CutLoadedState s marks v) 12 := by
  have he₁ := table_word_eval marks.incoming s hn hv hlens.1
    (fun x hx => hwords x (by simp [hx])) h620 h666
  let s₁ := s.setReg 669 (marks.incoming[v]?.getD 0)
  have he₂ := table_word_eval marks.outgoing s₁ hn hv hlens.2.1
    (fun x hx => hwords x (by simp [hx])) h621 (by simpa [s₁] using h666)
  let s₂ := s₁.setReg 670 (marks.outgoing[v]?.getD 0)
  have he₃ := table_word_eval marks.cuffPositive s₂ hn hv hlens.2.2.1
    (fun x hx => hwords x (by simp [hx])) h623 (by simpa [s₂, s₁] using h666)
  let s₃ := s₂.setReg 671 (marks.cuffPositive[v]?.getD 0)
  have he₄ := table_word_eval marks.cuffNegative s₃ hn hv hlens.2.2.2
    (fun x hx => hwords x (by simp [hx])) h624 (by simpa [s₃, s₂, s₁] using h666)
  exact .seq (.assign he₁) (.seq (.assign he₂) (.seq (.assign he₃) (.assign he₄)))

/-- Read and decode the current vertex's four computed cut-table entries. -/
def gm06CutPreparePositionProg : Cmd := .seq gm06CutLoadPositionProg gm06CutDecodePositionProg

/-- Full local decoding from the computed arrays, with no supplied
position or case tag. The exact state describes every changed register. -/
theorem gm06CutPreparePositionProg_exec {w n v : ℕ} (marks : GM06CutTables) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hv : v < n)
    (hlens : marks.incoming.length = n ∧ marks.outgoing.length = n ∧
      marks.cuffPositive.length = n ∧ marks.cuffNegative.length = n)
    (hwords : ∀ x ∈ marks.incoming ++ marks.outgoing ++ marks.cuffPositive ++ marks.cuffNegative, x < 2 ^ w)
    (h620 : s.arrs 620 = marks.incoming) (h621 : s.arrs 621 = marks.outgoing)
    (h623 : s.arrs 623 = marks.cuffPositive) (h624 : s.arrs 624 = marks.cuffNegative)
    (h666 : s.regs 666 = v) :
    ∃ t, Exec w gm06CutPreparePositionProg s
      (gm06CutDecodedState (gm06CutLoadedState s marks v) (gm06CutPositionAt marks v)) t ∧ t ≤ 28 := by
  have he₁ := gm06CutLoadPositionProg_exec marks s hn hv hlens hwords h620 h621 h623 h624 h666
  have ha := table_word_eval marks.incoming s hn hv hlens.1
    (fun x hx => hwords x (by simp [hx])) h620 h666
  have hb := table_word_eval marks.outgoing s hn hv hlens.2.1
    (fun x hx => hwords x (by simp [hx])) h621 h666
  have hcp := table_word_eval marks.cuffPositive s hn hv hlens.2.2.1
    (fun x hx => hwords x (by simp [hx])) h623 h666
  have hcn := table_word_eval marks.cuffNegative s hn hv hlens.2.2.2
    (fun x hx => hwords x (by simp [hx])) h624 h666
  obtain ⟨t, he, ht⟩ := gm06CutDecodePositionProg_exec (gm06CutLoadedState s marks v)
    hw (Expr.eval_lt ha) (Expr.eval_lt hb) (Expr.eval_lt hcp) (Expr.eval_lt hcn)
    (by simp [gm06CutLoadedState]) (by simp [gm06CutLoadedState])
    (by simp [gm06CutLoadedState]) (by simp [gm06CutLoadedState])
  refine ⟨12 + t, ?_, by omega⟩
  simpa only [gm06CutPreparePositionProg, ← gm06CutPositionAt_eq_ofMarks] using (Exec.seq he₁ he)

/-- Loading changes only the four local input registers. -/
theorem gm06CutLoadedState_keeps (s : State) (marks : GM06CutTables) (v : ℕ) :
    Keeps [669, 670, 671, 672] [] s (gm06CutLoadedState s marks v) := by
  exact ((((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _).setReg
    (by simp) _).setReg (by simp) _

/-- Decoding changes only the kind, cuff and interval-bound registers. -/
theorem gm06CutDecodedState_keeps (s : State) (position : Option GM06CutPosition) :
    Keeps [668, 671, 672, 673, 674] [] s (gm06CutDecodedState s position) := by
  exact (((((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _).setReg
    (by simp) _).setReg (by simp) _).setReg (by simp) _

/-- Decoding valid input words creates only valid local words. -/
theorem gm06CutPositionOfMarks_word_bounds {w a b cp cn : ℕ}
    (hw : 2 < 2 ^ w) (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (hcp : cp < 2 ^ w) (hcn : cn < 2 ^ w) :
    let p := gm06CutPositionOfMarks a b cp cn
    ∀ x ∈ [gm06CutPositionKind p, gm06CutPositionIncoming p, gm06CutPositionOutgoing p,
      (gm06CutPositionCuffs p).1, (gm06CutPositionCuffs p).2,
      (gm06CutPositionBounds p).1, (gm06CutPositionBounds p).2], x < 2 ^ w := by
  dsimp only
  have hw0 : w ≠ 0 := by
    intro h
    have he : 2 ^ w = 1 := by simp [h]
    omega
  by_cases haz : a = 0 <;> by_cases hbz : b = 0 <;>
    simp [gm06CutPositionOfMarks, haz, hbz, hw0, gm06CutPositionKind,
      gm06CutPositionIncoming, gm06CutPositionOutgoing, gm06CutPositionCuffs,
      gm06CutPositionBounds, GM06CutPosition.leftBounds] <;> omega

/-- Looking up a table of words, with zero as default, gives a word. -/
theorem gm06CutTableWord_lt {w : ℕ} (table : List ℕ) (v : ℕ)
    (hwords : ∀ x ∈ table, x < 2 ^ w) : table[v]?.getD 0 < 2 ^ w := by
  cases h : table[v]? with
  | none => simpa only [h, Option.getD_none] using Nat.two_pow_pos w
  | some x => simpa only [h, Option.getD_some] using hwords x (List.mem_of_getElem? h)

/-- Every decoded local field is a word whenever the four source
arrays contain words, including at an unused permanent vertex slot. -/
theorem gm06CutPositionAt_word_bounds {w : ℕ} (marks : GM06CutTables) (v : ℕ)
    (hw : 2 < 2 ^ w)
    (hwords : ∀ x ∈ marks.incoming ++ marks.outgoing ++ marks.cuffPositive ++ marks.cuffNegative, x < 2 ^ w) :
    let p := gm06CutPositionAt marks v
    ∀ x ∈ [gm06CutPositionKind p, gm06CutPositionIncoming p, gm06CutPositionOutgoing p,
      (gm06CutPositionCuffs p).1, (gm06CutPositionCuffs p).2,
      (gm06CutPositionBounds p).1, (gm06CutPositionBounds p).2], x < 2 ^ w := by
  rw [gm06CutPositionAt_eq_ofMarks]
  exact gm06CutPositionOfMarks_word_bounds hw
    (gm06CutTableWord_lt _ _ (fun x hx => hwords x (by simp [hx])))
    (gm06CutTableWord_lt _ _ (fun x hx => hwords x (by simp [hx])))
    (gm06CutTableWord_lt _ _ (fun x hx => hwords x (by simp [hx])))
    (gm06CutTableWord_lt _ _ (fun x hx => hwords x (by simp [hx])))

end GraphMinor.Compute
