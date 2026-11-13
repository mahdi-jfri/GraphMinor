module

public import GraphMinor.Compute.GM06TerminalPhase
public import GraphMinor.Compute.GM06FaceSuccessors
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Small steps of the terminal phase

The terminal phase of VI (5.7), page 133, builds the row of path $i$
from the terminal path $Q_i$ and the next original path $P_{i+1}$
(Section 16 of our proof of VI (5.7), outlined in `GraphMinor/GM06/Alg57Algorithm.lean`).
Besides the programs of the other phases, it needs four small steps, proved here.

* `gm06TerminalEndProg` reads the end vertex $u_i$ of $Q_i$: the head of
  its last dart, or the source when $Q_i$ is empty.
* `gm06TerminalIndexProg` finds the position of $u_i$ on the right copy
  of $P_{i+1}$. It counts the entries before the first match, so it
  returns the index of $u_i$ in the first `length P_{i+1}` entries.
* `gm06TerminalOutputInitProg` allocates the output buffer and writes
  the number of rows.
* `gm06TerminalEmitProg` appends one row, with its length, to the buffer.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-! ### The end vertex -/

/-- Read the end vertex of the terminal path in array 607 into register 702. -/
def gm06TerminalEndProg : Cmd :=
  .seq (.ite (.len 607) (.assign 701 (.read 607 (.op .sub (.len 607) (.const 1))))
      (.assign 701 (.reg 667)))
    (.assign 702 (.read 626 (gm06DartMateExpr (.reg 701))))

/-- The end-vertex step returns `gm06TerminalPathEnd`. -/
theorem gm06TerminalEndProg_exec {w M cuff : ℕ} (origins path : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hM : 2 * M < 2 ^ w) (horg : origins.length = 2 * M)
    (hwords : ∀ v ∈ origins, v < 2 ^ w)
    (hpath : ∀ d ∈ path, d < 2 * M) (hcuff : cuff < 2 * M) (hlen : path.length < 2 ^ w)
    (h607 : s.arrs 607 = path) (h626 : s.arrs 626 = origins) (h667 : s.regs 667 = cuff) :
    ∃ sf t, Exec w gm06TerminalEndProg s sf t ∧ t ≤ 30 ∧ Keeps [701, 702] [] s sf ∧
      sf.regs 702 = gm06TerminalPathEnd origins cuff path := by
  have hlast : path.getLastD cuff < 2 * M := by
    rw [List.getLastD_eq_getLast?]
    cases hl : path.getLast? with
    | none => exact hcuff
    | some d => exact hpath d (List.mem_of_getLast? hl)
  obtain ⟨t₁, he₁⟩ : ∃ t₁, Exec w (.ite (.len 607) (.assign 701 (.read 607 (.op .sub (.len 607) (.const 1))))
      (.assign 701 (.reg 667))) s (s.setReg 701 (path.getLastD cuff)) t₁ ∧ t₁ ≤ 8 := by
    have hlen' := Crossing.eval_len (w := w) h607 hlen
    cases path with
    | nil =>
      refine ⟨_, .ite_false hlen' (.assign (Crossing.eval_reg h667 (by omega))), ?_⟩
      simp
    | cons d ds =>
      have hidx : (List.length (d :: ds) - 1) < (s.arrs 607).length := by rw [h607]; simp
      have hval : (s.arrs 607)[List.length (d :: ds) - 1] = (d :: ds).getLastD cuff := by
        simp only [h607, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
        simp
      have hvalw : (s.arrs 607)[List.length (d :: ds) - 1] < 2 ^ w := by
        rw [hval]; omega
      have hread := Crossing.eval_read (a := 607)
        (Crossing.eval_sub hlen' (Crossing.eval_const (w := w) (s := s) (c := 1) (by omega))) hidx hvalw
      rw [hval] at hread
      exact ⟨_, .ite_true hlen' (by simp) (.assign hread), by simp⟩
  obtain ⟨he₁, ht₁⟩ := he₁
  let s₁ := s.setReg 701 (path.getLastD cuff)
  have hmate := gm06DartMateExpr_eval (s := s₁) (D := .reg 701) hw hM hlast
    (Crossing.eval_reg (by simp [s₁]) (by omega))
  have hmlt : gm06DartMate (path.getLastD cuff) < (s₁.arrs 626).length := by
    simp only [s₁, State.setReg_arrs, h626, horg]
    exact gm06DartMate_lt hlast
  have hread := Crossing.eval_read (a := 626) hmate hmlt
    (hwords _ (by simp only [s₁, State.setReg_arrs, h626] at hmlt ⊢; exact List.getElem_mem _))
  refine ⟨_, _, .seq he₁ (.assign hread), ?_, ?_, ?_⟩
  · simp only [gm06DartMateExpr, Expr.cost] at ht₁ ⊢; omega
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [s₁, hr.1, hr.2]
    · intro a _
      rfl
  · simp only [State.setReg_regs_self, s₁, State.setReg_arrs, h626, gm06TerminalPathEnd,
      gm06CutNeighbourHead]
    rw [List.getElem?_eq_getElem (by rw [horg]; exact gm06DartMate_lt hlast), Option.getD_some]

/-! ### The position of the end vertex -/

/-- One round of the index scan: count until the first match. -/
def gm06TerminalIndexBody : Cmd :=
  .ite (.reg 703) .skip
    (.ite (.op .eq (.read 608 (.reg 704)) (.reg 702)) (.assign 703 (.const 1))
      (.assign 678 (.op .add (.reg 678) (.const 1))))

/-- Find the position of register 702 among the first `length (arrs 610)`
entries of array 608, in register 678. -/
def gm06TerminalIndexProg : Cmd :=
  .seq (.assign 678 (.const 0))
    (.seq (.assign 703 (.const 0))
      (.seq (.assign 704 (.const 0)) (forUp 704 (.len 610) gm06TerminalIndexBody)))

/-- The index scan returns the index in the prefix of the length of
the path. -/
theorem gm06TerminalIndexProg_exec {w u : ℕ} (upper path : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hlen : path.length ≤ upper.length) (hfit : upper.length + 1 < 2 ^ w)
    (hwords : ∀ v ∈ upper, v < 2 ^ w) (hu : u < 2 ^ w)
    (h608 : s.arrs 608 = upper) (h610 : s.arrs 610 = path) (h702 : s.regs 702 = u) :
    ∃ sf t, Exec w gm06TerminalIndexProg s sf t ∧ t ≤ 10 + 20 * (path.length + 1) ∧
      Keeps [678, 703, 704] [] s sf ∧ sf.regs 678 = (upper.take path.length).idxOf u := by
  let s₁ := ((s.setReg 678 0).setReg 703 0).setReg 704 0
  let I : ℕ → State → Prop := fun p st =>
    Keeps [678, 703, 704] [] s st ∧ st.regs 704 = p ∧
      st.regs 678 = (upper.take p).idxOf u ∧
      st.regs 703 = (if u ∈ upper.take p then 1 else 0)
  have hk₁ : Keeps [678, 703, 704] [] s s₁ :=
    (((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _).setReg (by simp) _
  have hI₀ : I 0 s₁ := ⟨hk₁, by simp [s₁], by simp [s₁], by simp [s₁]⟩
  have hN : path.length < 2 ^ w := by omega
  obtain ⟨sf, tf, hef, htf, hIf⟩ := Crossing.forUp_exec' (r_i := 704) (hi := .len 610)
    (body := gm06TerminalIndexBody) I path.length 10 hw hN
    (fun p _ st hst => ⟨hst.2.1, Crossing.eval_len ((hst.1.2 610 (by simp)).trans h610) hN⟩)
    (by
      intro p hp st hst
      obtain ⟨hk, h704, h678, h703⟩ := hst
      have hpu : p < upper.length := by omega
      have htake : upper.take (p + 1) = upper.take p ++ [upper[p]] := List.take_succ_eq_append_getElem hpu
      have htakeLen : (upper.take p).length = p := by simp only [List.length_take]; omega
      have h608' : st.arrs 608 = upper := (hk.2 608 (by simp)).trans h608
      have h702' : st.regs 702 = u := (hk.1 702 (by simp)).trans h702
      have hpw : p < 2 ^ w := by omega
      by_cases hmem : u ∈ upper.take p
      · rw [if_pos hmem] at h703
        refine ⟨st, 2, .ite_true (Crossing.eval_reg h703 (by omega)) (by decide) (.skip st), by omega,
          ⟨(hk.setReg (by simp) _), by simp, ?_, ?_⟩, h704⟩
        · rw [State.setReg_regs_ne _ _ (by decide), h678, htake, List.idxOf_append_of_mem hmem]
        · rw [State.setReg_regs_ne _ _ (by decide), h703, if_pos (by rw [htake]; exact List.mem_append_left _ hmem)]
      · rw [if_neg hmem] at h703
        have hidx : p < (st.arrs 608).length := by rw [h608']; exact hpu
        have hval : (st.arrs 608)[p] = upper[p] := by simp only [h608']
        have hread := Crossing.eval_read (a := 608) (Crossing.eval_reg h704 hpw) hidx
          (by rw [hval]; exact hwords _ (List.getElem_mem _))
        rw [hval] at hread
        have heq := Crossing.eval_eq hread (Crossing.eval_reg h702' hu) hw
        have hnot : (upper.take p).idxOf u = p := by rw [List.idxOf_eq_length hmem, htakeLen]
        by_cases hm : upper[p] = u
        · rw [if_pos hm] at heq
          refine ⟨st.setReg 703 1, _, .ite_false (Crossing.eval_reg h703 (by omega))
            (.ite_true heq (by decide) (.assign (Crossing.eval_const (by omega)))), by simp,
            ⟨((hk.setReg (by simp) _).setReg (by simp) _), by simp, ?_, ?_⟩, by simp [h704]⟩
          · simp only [State.setReg_regs_ne _ _ (by decide : (678 : ℕ) ≠ 704),
              State.setReg_regs_ne _ _ (by decide : (678 : ℕ) ≠ 703), h678, hnot]
            rw [htake, List.idxOf_append_of_notMem hmem, hm, htakeLen]
            simp
          · simp only [State.setReg_regs_ne _ _ (by decide : (703 : ℕ) ≠ 704), State.setReg_regs_self]
            rw [if_pos (by rw [htake, hm]; simp)]
        · rw [if_neg hm] at heq
          have hadd := Crossing.eval_add (Crossing.eval_reg (w := w) (s := st) h678 (by rw [hnot]; exact hpw))
            (Crossing.eval_const (w := w) (s := st) (c := 1) (by omega)) (by rw [hnot]; omega)
          refine ⟨st.setReg 678 ((upper.take p).idxOf u + 1), _, .ite_false (Crossing.eval_reg h703 (by omega))
            (.ite_false heq (.assign hadd)), by simp,
            ⟨((hk.setReg (by simp) _).setReg (by simp) _), by simp, ?_, ?_⟩, by simp [h704]⟩
          · simp only [State.setReg_regs_ne _ _ (by decide : (678 : ℕ) ≠ 704), State.setReg_regs_self, hnot]
            have hmem' : u ∉ upper.take (p + 1) := by
              rw [htake]; simp only [List.mem_append, List.mem_singleton, not_or]
              exact ⟨hmem, fun h => hm h.symm⟩
            rw [List.idxOf_eq_length hmem', List.length_take]
            omega
          · simp only [State.setReg_regs_ne _ _ (by decide : (703 : ℕ) ≠ 704),
              State.setReg_regs_ne _ _ (by decide : (703 : ℕ) ≠ 678), h703]
            rw [if_neg]
            rw [htake]; simp only [List.mem_append, List.mem_singleton, not_or]
            exact ⟨hmem, fun h => hm h.symm⟩)
    s₁ hI₀
  refine ⟨sf, 2 + (2 + (2 + tf)), .seq (.assign (Crossing.eval_const (by omega)))
    (.seq (.assign (Crossing.eval_const (by omega))) (.seq (.assign (Crossing.eval_const (by omega))) hef)),
    ?_, hIf.1, hIf.2.2.1⟩
  · simp only [Expr.cost] at htf
    nlinarith only [htf]

/-! ### The output buffer -/

/-- Writing into the first free cell of a zero-padded buffer. -/
theorem gm06_set_padded (A : List ℕ) (v r : ℕ) :
    (A ++ List.replicate (r + 1) 0).set A.length v = (A ++ [v]) ++ List.replicate r 0 := by
  rw [List.set_append_right _ _ (le_refl _), Nat.sub_self, List.replicate_succ]
  simp

/-- The buffer capacity: one count word, then at most
`1 + 2 * regs 683 + length (arrs 642)` words per row. -/
def gm06TerminalOutputCapExpr : Expr :=
  .op .add (.const 1) (.op .mul (.reg 685)
    (.op .add (.const 1) (.op .add (.op .mul (.const 2) (.reg 683)) (.len 642))))

/-- Allocate the output buffer 643, store the row count, and set the
cursor 700 after it. -/
def gm06TerminalOutputInitProg : Cmd :=
  .seq (.alloc 643 gm06TerminalOutputCapExpr)
    (.seq (.write 643 (.const 0) (.reg 685)) (.assign 700 (.const 1)))

/-- The buffer starts with the row count and zero padding. -/
theorem gm06TerminalOutputInitProg_exec {w k a c : ℕ} (s : State) (hw : 2 < 2 ^ w)
    (hrow : 1 + (2 * a + c) < 2 ^ w) (hfit : 1 + k * (1 + (2 * a + c)) < 2 ^ w)
    (h685 : s.regs 685 = k) (h683 : s.regs 683 = a) (h642 : (s.arrs 642).length = c) :
    ∃ sf t, Exec w gm06TerminalOutputInitProg s sf t ∧ t ≤ 30 + k * (1 + (2 * a + c)) ∧
      Keeps [700] [643] s sf ∧
      sf.arrs 643 = [k] ++ List.replicate (k * (1 + (2 * a + c))) 0 ∧ sf.regs 700 = 1 := by
  have hk : k < 2 ^ w := by
    rcases Nat.eq_zero_or_pos k with h | h
    · omega
    · have : k ≤ k * (1 + (2 * a + c)) := Nat.le_mul_of_pos_right _ (by omega)
      omega
  have h2a : 2 * a < 2 ^ w := by omega
  have hcap : gm06TerminalOutputCapExpr.eval w s = some (1 + k * (1 + (2 * a + c))) := by
    have hc := Crossing.eval_len (w := w) (s := s) (a := 642) rfl (by rw [h642]; omega)
    rw [h642] at hc
    exact Crossing.eval_add (Crossing.eval_const (c := 1) (by omega))
      (Crossing.eval_mul (Crossing.eval_reg h685 hk)
        (Crossing.eval_add (Crossing.eval_const (c := 1) (by omega))
          (Crossing.eval_add (Crossing.eval_mul (Crossing.eval_const (c := 2) (by omega))
            (Crossing.eval_reg h683 (by omega)) h2a) hc (by omega)) hrow) (by omega)) hfit
  let s₁ := s.setArr 643 (List.replicate (1 + k * (1 + (2 * a + c))) 0)
  let s₂ := s₁.writeArr 643 0 k
  have he₂ : Exec w (.write 643 (.const 0) (.reg 685)) s₁ s₂ 3 :=
    .write (Crossing.eval_const (by omega)) (Crossing.eval_reg (by simp [s₁, h685]) hk)
      (by simp [s₁])
  refine ⟨s₂.setReg 700 1, _, .seq (.alloc hcap) (.seq he₂ (.assign (Crossing.eval_const (by omega)))),
    ?_, ?_, ?_, by simp⟩
  · simp only [gm06TerminalOutputCapExpr, Expr.cost]
    omega
  · constructor
    · intro r hr
      simp only [List.mem_singleton] at hr
      simp [s₂, s₁, State.setReg_regs_ne _ _ hr]
    · intro a' ha
      simp only [List.mem_singleton] at ha
      simp [s₂, s₁, State.writeArr_arrs_ne _ _ _ ha, State.setArr_arrs_ne _ _ ha]
  · simp only [s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, State.setArr_arrs_self]
    rw [Nat.add_comm 1, List.replicate_succ]
    simp

/-- Append `length (arrs 637)` and then array 637 to the buffer 643 at
the cursor 700, and advance the cursor. -/
def gm06TerminalEmitProg : Cmd :=
  .seq (.write 643 (.reg 700) (.len 637))
    (.seq (.assign 700 (.op .add (.reg 700) (.const 1)))
      (.seq (.assign 705 (.const 0))
        (.seq (forUp 705 (.len 637)
            (.write 643 (.op .add (.reg 700) (.reg 705)) (.read 637 (.reg 705))))
          (.assign 700 (.op .add (.reg 700) (.len 637))))))

/-- Appending one row keeps the zero padding after the written words. -/
theorem gm06TerminalEmitProg_exec {w q : ℕ} (out row : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hcap : out.length + 1 + row.length + q < 2 ^ w)
    (hwords : ∀ a ∈ row, a < 2 ^ w)
    (h643 : s.arrs 643 = out ++ List.replicate (1 + row.length + q) 0)
    (h700 : s.regs 700 = out.length) (h637 : s.arrs 637 = row) :
    ∃ sf t, Exec w gm06TerminalEmitProg s sf t ∧ t ≤ 30 + 20 * row.length ∧
      Keeps [700, 705] [643] s sf ∧
      sf.arrs 643 = (out ++ gm06EncodeNatList row) ++ List.replicate q 0 ∧
      sf.regs 700 = (out ++ gm06EncodeNatList row).length := by
  let L := row.length
  have hlenw : L < 2 ^ w := by omega
  have hlen := Crossing.eval_len (w := w) h637 hlenw
  -- First the length word.
  let s₁ := s.writeArr 643 out.length L
  have he₁ : Exec w (.write 643 (.reg 700) (.len 637)) s s₁ 3 :=
    .write (Crossing.eval_reg h700 (by omega)) hlen (by rw [h643]; simp)
  have h643₁ : s₁.arrs 643 = (out ++ [L]) ++ List.replicate (L + q) 0 := by
    simp only [s₁, State.writeArr_arrs_self, h643]
    rw [show 1 + row.length + q = (L + q) + 1 by omega, gm06_set_padded]
  let s₂ := s₁.setReg 700 (out.length + 1)
  have he₂ : Exec w (.assign 700 (.op .add (.reg 700) (.const 1))) s₁ s₂ 4 :=
    .assign (Crossing.eval_add (Crossing.eval_reg (by simp [s₁, h700]) (by omega))
      (Crossing.eval_const (by omega)) (by omega))
  let s₃ := s₂.setReg 705 0
  have he₃ : Exec w (.assign 705 (.const 0)) s₂ s₃ 2 := .assign (Crossing.eval_const (by omega))
  let I : ℕ → State → Prop := fun p st =>
    Keeps [700, 705] [643] s st ∧ st.regs 705 = p ∧ st.regs 700 = out.length + 1 ∧
      st.arrs 643 = (out ++ [L] ++ row.take p) ++ List.replicate (L - p + q) 0
  have hI₀ : I 0 s₃ := by
    refine ⟨?_, by simp [s₃], by simp [s₃, s₂], ?_⟩
    · constructor
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [s₃, s₂, s₁, hr.1, hr.2]
      · intro a ha
        simp only [List.mem_singleton] at ha
        simp [s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha]
    · simp only [s₃, s₂, State.setReg_arrs, h643₁, List.take_zero, List.append_nil, Nat.sub_zero]
  obtain ⟨s₄, t₄, he₄, ht₄, hI₄⟩ := Crossing.forUp_exec' (r_i := 705) (hi := .len 637)
    (body := .write 643 (.op .add (.reg 700) (.reg 705)) (.read 637 (.reg 705))) I L 6 hw hlenw
    (fun p _ st hst => ⟨hst.2.1, Crossing.eval_len ((hst.1.2 637 (by simp)).trans h637) hlenw⟩)
    (by
      intro p hp st hst
      obtain ⟨hk, h705, h700', h643'⟩ := hst
      have h637' : st.arrs 637 = row := (hk.2 637 (by simp)).trans h637
      have hpw : p < 2 ^ w := by omega
      have hidx : p < (st.arrs 637).length := by rw [h637']; exact hp
      have hval : (st.arrs 637)[p] = row[p] := by simp only [h637']
      have hread := Crossing.eval_read (a := 637) (Crossing.eval_reg h705 hpw) hidx
        (by rw [hval]; exact hwords _ (List.getElem_mem _))
      rw [hval] at hread
      have hpos := Crossing.eval_add (Crossing.eval_reg (w := w) (s := st) h700' (by omega))
        (Crossing.eval_reg h705 hpw) (show out.length + 1 + p < 2 ^ w by omega)
      have htakeLen : (row.take p).length = p := by simp only [List.length_take]; omega
      have hbound : out.length + 1 + p < (st.arrs 643).length := by
        rw [h643']; simp only [List.length_append, List.length_singleton, List.length_replicate]
        omega
      refine ⟨st.writeArr 643 (out.length + 1 + p) row[p], _, .write hpos hread hbound, by simp,
        ⟨?_, by simp, by simp [h700'], ?_⟩, by simp [h705]⟩
      · exact (hk.writeArr (by simp) _ _).setReg (by simp) _
      · simp only [State.setReg_arrs, State.writeArr_arrs_self, h643']
        have hlenA : (out ++ [L] ++ row.take p).length = out.length + 1 + p := by
          simp only [List.length_append, List.length_singleton, htakeLen]
        rw [show L - p + q = (L - (p + 1) + q) + 1 by omega, ← hlenA, gm06_set_padded,
          List.take_succ_eq_append_getElem hp, List.append_assoc (out ++ [L])])
    s₃ hI₀
  obtain ⟨hk₄, _, h700₄, h643₄⟩ := hI₄
  have hrowtake : row.take L = row := List.take_length
  let sf := s₄.setReg 700 (out.length + 1 + L)
  have he₅ : Exec w (.assign 700 (.op .add (.reg 700) (.len 637))) s₄ sf 4 :=
    .assign (Crossing.eval_add (Crossing.eval_reg h700₄ (by omega))
      (Crossing.eval_len ((hk₄.2 637 (by simp)).trans h637) hlenw) (by omega))
  refine ⟨sf, _, .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ he₅))), ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost] at ht₄
    have : L * (1 + 6 + 6) ≤ 13 * L := by omega
    omega
  · exact hk₄.setReg (by simp) _
  · simp only [sf, State.setReg_arrs, h643₄, hrowtake, Nat.sub_self, Nat.zero_add, gm06EncodeNatList]
    simp [L]
  · simp [sf, gm06EncodeNatList, L]
    omega

end GraphMinor.Compute
