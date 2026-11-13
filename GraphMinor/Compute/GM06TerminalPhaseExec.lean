module

public import GraphMinor.Compute.GM06TerminalPhaseProgram
import GraphMinor.Compute.CrossingOpsBasic
import GraphMinor.Compute.GM06CutCSR
import GraphMinor.Compute.GM06RowPositions
import GraphMinor.Compute.GM06CutSplitRows
import GraphMinor.Compute.GM06CutFaceFacts

/-!
# Execution of the whole terminal phase of VI (5.7)

This file proves that `gm06TerminalPhaseProg` writes exactly the rows
`gm06TerminalPhase x m` into array 8, sets the answer register 0 to 1,
changes only its reserved memory, and runs in time cubic in
`gm06PhaseSize`.

The proof follows the program. One round of its loop reads the record
of component $K_i$, computes the face $F_i$, builds the new row $i$
(`gm06TerminalRowProg_exec`) and appends it to the output buffer. The
loop invariant says that the buffer holds the row count and the
encoded rows $0, \dots, i-1$, followed by zero padding. Each row has at
most `2 * (2 * aug) + length (code of the linkage)` words, which is what
the allocated capacity allows.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

/-! ### Rows and the buffer -/

/-- A face selected in a computed component has distinct darts, all of
them labels of the copied space, and contains its selecting dart. -/
theorem gm06PhaseComponent_face_facts {m target : ℕ} (x : GM06SuccessorInput)
    (horig : x.endpoints.length = 2 * m) (hvalues : ∀ v ∈ x.endpoints, v < x.vertexCount)
    (hinner : ∀ v ∈ x.innerCuff, v < x.vertexCount) (houter : ∀ v ∈ x.outerCuff, v < x.vertexCount)
    (hrows : x.rotations.length = x.vertexCount) (hnd : x.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (part : GM06CutData) (hp : part ∈ gm06PhaseComponents x m) {face incV incE : List ℕ}
    (hface : gm06CutFaceIncidence (2 * x.vertexCount)
      (2 * (m + x.innerCuff.length + x.outerCuff.length)) part target = some (face, incV, incE)) :
    face.length ≤ 4 * (m + x.innerCuff.length + x.outerCuff.length) ∧
      (∀ d ∈ face, d < 4 * (m + x.innerCuff.length + x.outerCuff.length)) ∧ target ∈ face := by
  obtain ⟨_, _, _, hpnd, hcanon, hpair⟩ := gm06PhaseComponents_encoding x hnd part hp
  obtain ⟨_, _, _, hpkeys⟩ :=
    gm06PhaseComponents_sizes x hrows horig hvalues hinner houter hnd hkeys part hp
  have hcover : ∀ d, d ∈ part.activeDarts ↔ d ∈ part.rotations.flatten := by
    intro d
    rw [hcanon, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact and_iff_right_of_imp (hpkeys d)
  have hkeys' : ∀ d ∈ part.rotations.flatten,
      d < 2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) := by
    intro d hd; have := hpkeys d hd; omega
  have hactive' : ∀ d ∈ part.activeDarts,
      d < 2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) :=
    fun d hd => hkeys' d ((hcover d).mp hd)
  have ht := gm06CutFaceIncidence_target_mem part hpnd hkeys' hactive' hcover hpair hface
  have hlt : target < 2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) := by
    by_contra hge
    unfold gm06CutFaceIncidence at hface
    simp [hge] at hface
  obtain ⟨_, _, _, hflen, hfmem, _⟩ := gm06CutFaceIncidence_some_facts part hpnd hkeys' hactive'
    hcover hpair hlt hface
  refine ⟨by omega, fun d hd => ?_, ht⟩
  have := hkeys' d (hfmem d hd)
  omega

/-- Each terminal row is short, and its words are labels of the copied
dart space. -/
theorem gm06TerminalPhaseRow_facts {m i : ℕ} (x : GM06SuccessorInput)
    (horig : x.endpoints.length = 2 * m) (hvalues : ∀ v ∈ x.endpoints, v < x.vertexCount)
    (hdarts : ∀ d ∈ x.linkage.flatten, d < 2 * m)
    (hinner : ∀ v ∈ x.innerCuff, v < x.vertexCount) (houter : ∀ v ∈ x.outerCuff, v < x.vertexCount)
    (hcount : x.linkage.length = x.innerCuff.length)
    (hrows : x.rotations.length = x.vertexCount) (hnd : x.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (hi : i < x.innerCuff.length) :
    (gm06TerminalPhaseRow x m i).length ≤
        2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) + (gm06EncodeRows x.linkage).length ∧
      ∀ a ∈ gm06TerminalPhaseRow x m i, a < 4 * (m + x.innerCuff.length + x.outerCuff.length) := by
  have hlen : (gm06PhaseComponents x m).length = x.innerCuff.length := gm06PhaseComponents_length x m
  have hik : i < (gm06PhaseComponents x m).length := by omega
  have hp : (gm06PhaseComponents x m)[i] ∈ gm06PhaseComponents x m := List.getElem_mem hik
  have hrow : gm06TerminalPhaseRow x m i =
      gm06TerminalPhaseComponent x m i (gm06PhaseComponents x m)[i] := by
    simp only [gm06TerminalPhaseRow, List.getElem?_eq_getElem hik]
  rw [hrow]
  have hcode := gm06FaceCode_length x.linkage
  have hk0 : 0 < x.innerCuff.length := by omega
  have hnextPath : gm06PhaseNext x i < x.linkage.length := by
    have := Nat.mod_lt (i + 1) hk0; unfold gm06PhaseNext; omega
  cases hface : gm06CutFaceIncidence (2 * x.vertexCount)
      (2 * (m + x.innerCuff.length + x.outerCuff.length)) (gm06PhaseComponents x m)[i]
      (4 * (m + i) + 1) with
  | none =>
    rw [gm06TerminalPhaseComponent_of_none hface]
    simp
  | some res =>
    obtain ⟨face, incV, incE⟩ := res
    rw [gm06TerminalPhaseComponent_of_some hface]
    obtain ⟨hflen, hfd, hc⟩ := gm06PhaseComponent_face_facts x horig hvalues hinner houter hrows hnd
      hkeys _ hp hface
    obtain ⟨hQlen, hQmem⟩ := gm06TerminalPath_sublist_face (2 * x.vertexCount)
      (gm06PhaseComponents x m)[i].origins face (gm06PhaseBoundaryVertices x i 0)
      (gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1) (4 * (m + i) + 1) hc
    have hPlen : (x.linkage[gm06PhaseNext x i]?.getD []).length ≤ x.linkage.flatten.length := by
      rw [List.getElem?_eq_getElem hnextPath, Option.getD_some]
      exact gm06Row_length_le_flatten (List.getElem_mem _)
    refine ⟨(gm06Apply4Row_length_le _ _ _ _).trans (by omega), ?_⟩
    intro a ha
    simp only [gm06Apply4Row, List.mem_append, List.mem_map] at ha
    rcases ha with ⟨d, hd, rfl⟩ | ha
    · exact (gm06ProjectCutDart_le d).trans_lt (hfd d (hQmem d hd))
    · rw [List.getElem?_eq_getElem hnextPath, Option.getD_some] at ha
      have := hdarts a (List.mem_flatten.mpr ⟨_, List.getElem_mem hnextPath, List.mem_of_mem_drop ha⟩)
      omega

/-- Encoded rows of bounded length fill at most their share of the buffer. -/
theorem gm06EncodeRowsPayload_length_le (rows : List (List ℕ)) (W : ℕ)
    (h : ∀ r ∈ rows, r.length + 1 ≤ W) : (gm06EncodeRowsPayload rows).length ≤ rows.length * W := by
  induction rows with
  | nil => simp [gm06EncodeRowsPayload]
  | cons r rows ih =>
    have hr := h r List.mem_cons_self
    have ht := ih (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    simp only [gm06EncodeRowsPayload, List.flatMap_cons, List.length_append, gm06EncodeNatList,
      List.length_cons] at ht ⊢
    rw [Nat.succ_mul]
    omega

/-- The first `i + 1` encoded rows extend the first `i` by row `i`. -/
theorem gm06EncodeRowsPayload_take_succ (rows : List (List ℕ)) {i : ℕ} (hi : i < rows.length) :
    gm06EncodeRowsPayload (rows.take (i + 1)) =
      gm06EncodeRowsPayload (rows.take i) ++ gm06EncodeNatList rows[i] := by
  rw [List.take_succ_eq_append_getElem hi, gm06EncodeRowsPayload_append]
  simp [gm06EncodeRowsPayload]

/-! ### One round of the loop -/

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 8192 in
/-- One round for component `i`: read its record, select its face,
build its row and append it to the output buffer. -/
private theorem terminal_body {w m i : ℕ} (x : GM06SuccessorInput) (tail : List ℕ) (s : State)
    (horig : x.endpoints.length = 2 * m) (hvalues : ∀ v ∈ x.endpoints, v < x.vertexCount)
    (hdarts : ∀ d ∈ x.linkage.flatten, d < 2 * m)
    (hinner : ∀ v ∈ x.innerCuff, v < x.vertexCount) (houter : ∀ v ∈ x.outerCuff, v < x.vertexCount)
    (hcount : x.linkage.length = x.innerCuff.length)
    (hrows : x.rotations.length = x.vertexCount) (hnd : x.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (hword : 10000 * gm06PhaseSize x m ^ 3 < 2 ^ w)
    (hi : i < x.innerCuff.length)
    (h640 : s.arrs 640 = x.innerCuff.length ::
      (((gm06PhaseComponents x m).map GM06CutData.rotations).flatMap gm06EncodeRows ++ tail))
    (h640len : (s.arrs 640).length < 2 ^ w) (h640words : ∀ a ∈ s.arrs 640, a < 2 ^ w)
    (h693 : s.regs 693 = 1 +
      ((((gm06PhaseComponents x m).map GM06CutData.rotations).take i).flatMap gm06EncodeRows).length)
    (h641 : s.arrs 641 = (gm06CutDataOfLinkage x.vertexCount m x.endpoints x.linkage x.innerCuff
      x.outerCuff x.rotations (List.range x.vertexCount)).origins)
    (h642 : s.arrs 642 = gm06EncodeRows x.linkage)
    (h3 : s.arrs 3 = x.endpoints) (h6 : s.arrs 6 = x.innerCuff)
    (h681 : s.regs 681 = i) (h685 : s.regs 685 = x.innerCuff.length)
    (h682 : s.regs 682 = 2 * x.vertexCount)
    (h683 : s.regs 683 = 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (h684 : s.regs 684 = m)
    (h643 : s.arrs 643 = (x.innerCuff.length :: gm06EncodeRowsPayload ((gm06TerminalPhase x m).take i)) ++
      List.replicate (x.innerCuff.length *
        (1 + (2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) + (gm06EncodeRows x.linkage).length)) -
          (gm06EncodeRowsPayload ((gm06TerminalPhase x m).take i)).length) 0)
    (h700 : s.regs 700 = 1 + (gm06EncodeRowsPayload ((gm06TerminalPhase x m).take i)).length) :
    ∃ s' t, Exec w gm06TerminalPhaseBody s s' t ∧ t ≤ 30000 * gm06PhaseSize x m ^ 2 ∧
      s'.arrs 640 = s.arrs 640 ∧ s'.arrs 641 = s.arrs 641 ∧ s'.arrs 642 = s.arrs 642 ∧
      s'.arrs 3 = s.arrs 3 ∧ s'.arrs 6 = s.arrs 6 ∧
      s'.regs 682 = s.regs 682 ∧ s'.regs 683 = s.regs 683 ∧ s'.regs 684 = s.regs 684 ∧
      s'.regs 685 = s.regs 685 ∧ s'.regs 681 = i ∧
      s'.regs 693 = 1 +
        ((((gm06PhaseComponents x m).map GM06CutData.rotations).take (i + 1)).flatMap
          gm06EncodeRows).length ∧
      s'.arrs 643 = (x.innerCuff.length ::
          gm06EncodeRowsPayload ((gm06TerminalPhase x m).take (i + 1))) ++
        List.replicate (x.innerCuff.length *
          (1 + (2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) +
            (gm06EncodeRows x.linkage).length)) -
          (gm06EncodeRowsPayload ((gm06TerminalPhase x m).take (i + 1))).length) 0 ∧
      s'.regs 700 = 1 + (gm06EncodeRowsPayload ((gm06TerminalPhase x m).take (i + 1))).length := by
  obtain ⟨hnN, haugN, hpathN, hrotN, _, _, hflatN, hN⟩ := gm06PhaseSize_facts x m
  have hN2 : gm06PhaseSize x m ≤ gm06PhaseSize x m ^ 2 := by
    rw [sq]; exact Nat.le_mul_of_pos_left _ hN
  have hw : 4 < 2 ^ w := gm06PhaseSize_fit x hword (by omega)
  have hw1 : 1 < 2 ^ w := by omega
  let comps := gm06PhaseComponents x m
  let R := comps.map GM06CutData.rotations
  have hlen : comps.length = x.innerCuff.length := gm06PhaseComponents_length x m
  have hik : i < comps.length := by omega
  have hRlen : i < R.length := by simp only [R, List.length_map]; omega
  let part := comps[i]
  have hp : part ∈ comps := List.getElem_mem hik
  have hRi : R[i] = part.rotations := by simp only [R, part, List.getElem_map]
  have hrowEq : gm06TerminalPhaseRow x m i = gm06TerminalPhaseComponent x m i part := by
    simp only [gm06TerminalPhaseRow, List.getElem?_eq_getElem hik, part, comps]
  -- Facts about the component.
  obtain ⟨_, horgEq, _, hpnd, hcanon, hpair⟩ := gm06PhaseComponents_encoding x hnd part hp
  obtain ⟨_, hporigLen, hporigVals, hpkeys⟩ :=
    gm06PhaseComponents_sizes x hrows horig hvalues hinner houter hnd hkeys part hp
  have hpcode := gm06PhaseComponents_code_length x hnd part hp
  have hpwords := gm06PhaseComponents_code_words (w := w) x hnd hkeys
    (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega)) part hp
  have horiginsFit : part.origins.length < 2 ^ w := by
    rw [hporigLen]; exact gm06PhaseSize_fit x hword (by omega)
  have horiginsWords : ∀ a ∈ part.origins, a < 2 ^ w :=
    fun a ha => (hporigVals a ha).trans (gm06PhaseSize_fit x hword (by omega))
  -- Split the record buffer at component `i`.
  let pre := x.innerCuff.length :: (R.take i).flatMap gm06EncodeRows
  let rest := (R.drop (i + 1)).flatMap gm06EncodeRows ++ tail
  have hsplit : s.arrs 640 = pre ++ gm06EncodeRows part.rotations ++ rest := by
    rw [h640]
    change x.innerCuff.length :: (R.flatMap gm06EncodeRows ++ tail) = _
    rw [gm06PhaseRecords_split hRlen, hRi]
    simp only [pre, rest, List.cons_append, List.append_assoc]
  have hprelen : pre.length = 1 + ((R.take i).flatMap gm06EncodeRows).length := by
    simp only [pre, List.length_cons]; omega
  have hpreFit : pre.length < 2 ^ w := by
    have hl := congrArg List.length hsplit
    simp only [List.length_append] at hl
    omega
  have hcodeFit : pre.length + (gm06EncodeRows part.rotations).length < 2 ^ w := by
    have hl := congrArg List.length hsplit
    simp only [List.length_append] at hl
    omega
  -- Step 1: the record cursor.
  let s₀ := s.setReg 661 pre.length
  have he₀ : Exec w (.assign 661 (.reg 693)) s s₀ 2 :=
    .assign (Crossing.eval_reg (h693.trans hprelen.symm) hpreFit)
  -- Step 2: read the record.
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hr₁, hpos₁⟩ := gm06PhaseReadRecordProg_exec 640 625
    (by decide) (by decide) (by decide) (by decide) (by decide) pre rest part.rotations s₀ hw1
    hsplit h640len h640words (by simp [s₀])
  -- Step 3: save the cursor.
  let s₂ := s₁.setReg 693 (pre.length + (gm06EncodeRows part.rotations).length)
  have he₂ : Exec w (.assign 693 (.reg 661)) s₁ s₂ 2 := .assign (Crossing.eval_reg hpos₁ hcodeFit)
  have e₀₂ := Exec.seq he₀ (Exec.seq he₁ he₂)
  -- Step 4: the counts.
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, h668₃, h647₃, h648₃, h649₃, h672₃, h673₃⟩ :=
    gm06PhaseComponentCountsProg_exec (n := 2 * x.vertexCount)
      (aug := m + x.innerCuff.length + x.outerCuff.length)
      (m := m) (i := i) s₂ hw (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega))
      (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega))
      ((e₀₂.regs_eq_of_not_mem_writtenRegs (r := 682) (by decide)).trans h682)
      ((e₀₂.regs_eq_of_not_mem_writtenRegs (r := 683) (by decide)).trans h683)
      ((e₀₂.regs_eq_of_not_mem_writtenRegs (r := 684) (by decide)).trans h684)
      ((e₀₂.regs_eq_of_not_mem_writtenRegs (r := 681) (by decide)).trans h681)
  have h625₃ : s₃.arrs 625 = gm06EncodeRows part.rotations := (hk₃.2 625 (by simp)).trans hr₁
  have e₀₃ := Exec.seq e₀₂ he₃
  have h641₃ : s₃.arrs 641 = part.origins := by
    rw [e₀₃.arrs_eq_of_not_mem_writtenArrs (a := 641) (by decide), h641, horgEq]
  -- Step 5: face and incidence.
  have hquery : 4 * (m + i) + 1 < 4 * (m + x.innerCuff.length + x.outerCuff.length) := by omega
  obtain ⟨s₄, t₄, he₄, ht₄, _, hres₄⟩ := gm06PhaseComponentFacesProg_exec
    (n := 2 * x.vertexCount) (aug := m + x.innerCuff.length + x.outerCuff.length) (base := m) (i := i)
    part s₃ hw (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega)) hpnd hpkeys
    hcanon hpair hporigLen hporigVals hquery (gm06PhaseSize_fit x hword (by omega)) hpwords h625₃ h641₃
    h647₃ h648₃ h649₃ h672₃ h673₃
  have h626₄ : s₄.arrs 626 = part.origins :=
    gm06PhaseComponentFacesProg_origins part.origins s₃ s₄ hw1 horiginsFit horiginsWords h641₃ he₄
  have e₀₄ := Exec.seq e₀₃ he₄
  have hfacesCost := ht₄.trans (gm06PhaseComponentFacesCost_le_size x hnd part hp)
  -- Step 6: the row of component `i`.
  obtain ⟨s₅, t₅, he₅, ht₅, h637₅⟩ : ∃ s₅ t₅,
      Exec w (.ite (.reg 668) gm06TerminalRowProg (.alloc 637 (.const 0))) s₄ s₅ t₅ ∧
        t₅ ≤ 2 + 10000 * gm06PhaseSize x m ∧ s₅.arrs 637 = gm06TerminalPhaseRow x m i := by
    rw [hrowEq]
    cases hface : gm06CutFaceIncidence (2 * x.vertexCount)
        (2 * (m + x.innerCuff.length + x.outerCuff.length)) part (4 * (m + i) + 1) with
    | none =>
      have h668 : s₄.regs 668 = 0 := by
        rw [hface] at hres₄
        unfold gm06SelectedIncidenceResult at hres₄
        by_contra hne
        simp only [hne, ↓reduceIte, reduceCtorEq] at hres₄
      refine ⟨_, _, .ite_false (Crossing.eval_reg h668 (by omega))
        (.alloc (Crossing.eval_const (c := 0) (by omega))), by simp, ?_⟩
      rw [gm06TerminalPhaseComponent_of_none hface]
      simp
    | some res =>
      obtain ⟨face, incV, incE⟩ := res
      have hsel : gm06SelectedIncidenceResult s₄ = some (face, incV, incE) := hres₄.trans hface
      have h668 : s₄.regs 668 ≠ 0 := by
        intro hz
        simp only [gm06SelectedIncidenceResult, hz, ↓reduceIte, reduceCtorEq] at hsel
      have hsel' : (s₄.arrs 600, s₄.arrs 606, s₄.arrs 607) = (face, incV, incE) := by
        simpa only [gm06SelectedIncidenceResult, h668, ↓reduceIte, Option.some.injEq] using hsel
      have h600 : s₄.arrs 600 = face := congrArg Prod.fst hsel'
      have h668w : s₄.regs 668 < 2 ^ w := gm06Exec_reg_lt he₄ 668 (by rw [h668₃]; omega)
      obtain ⟨s₅, t₅, he₅, ht₅, hrow₅⟩ := gm06TerminalRowProg_exec x part s₄ face incV incE horig hvalues
        hdarts hinner houter hcount hrows hnd hkeys hword hi hp hface
        ((e₀₄.arrs_eq_of_not_mem_writtenArrs (a := 3) (by decide)).trans h3)
        ((e₀₄.arrs_eq_of_not_mem_writtenArrs (a := 6) (by decide)).trans h6)
        ((e₀₄.arrs_eq_of_not_mem_writtenArrs (a := 642) (by decide)).trans h642) h626₄ h600
        ((e₀₄.regs_eq_of_not_mem_writtenRegs (r := 681) (by decide)).trans h681)
        ((e₀₄.regs_eq_of_not_mem_writtenRegs (r := 685) (by decide)).trans h685)
        ((e₀₄.regs_eq_of_not_mem_writtenRegs (r := 682) (by decide)).trans h682)
        ((e₀₄.regs_eq_of_not_mem_writtenRegs (r := 684) (by decide)).trans h684)
      have hc : (Expr.reg 668).cost ≤ 2 := by decide
      exact ⟨s₅, _, .ite_true (Crossing.eval_reg rfl h668w) h668 he₅, by omega, hrow₅⟩
  have e₀₅ := Exec.seq e₀₄ he₅
  -- Step 7: append the row.
  have hrowsLen : (gm06TerminalPhase x m).length = x.innerCuff.length := gm06TerminalPhase_length x m
  have hrowsi : (gm06TerminalPhase x m)[i]'(by omega) = gm06TerminalPhaseRow x m i := gm06TerminalPhase_getElem x m i hi
  obtain ⟨hrowLen, hrowWords⟩ := gm06TerminalPhaseRow_facts x horig hvalues hdarts hinner houter hcount
    hrows hnd hkeys hi
  have hallRows : ∀ r ∈ gm06TerminalPhase x m, r.length + 1 ≤ (1 + (2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) + (gm06EncodeRows x.linkage).length)) := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    have := (gm06TerminalPhaseRow_facts x horig hvalues hdarts hinner houter hcount hrows hnd hkeys
      (List.mem_range.mp hj)).1
    omega
  have hpay := gm06EncodeRowsPayload_take_succ (gm06TerminalPhase x m) (i := i) (by omega)
  rw [hrowsi] at hpay
  have hpayLen : (gm06EncodeRowsPayload ((gm06TerminalPhase x m).take (i + 1))).length =
      (gm06EncodeRowsPayload ((gm06TerminalPhase x m).take i)).length + 1 + (gm06TerminalPhaseRow x m i).length := by
    rw [hpay]; simp [gm06EncodeNatList]; omega
  have hpayLe : (gm06EncodeRowsPayload ((gm06TerminalPhase x m).take (i + 1))).length ≤ x.innerCuff.length * (1 + (2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) + (gm06EncodeRows x.linkage).length)) := by
    have h := gm06EncodeRowsPayload_length_le ((gm06TerminalPhase x m).take (i + 1)) (1 + (2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) + (gm06EncodeRows x.linkage).length))
      (fun r hr => hallRows r (List.mem_of_mem_take hr))
    have hl : ((gm06TerminalPhase x m).take (i + 1)).length = i + 1 := by simp only [List.length_take]; omega
    rw [hl] at h
    exact h.trans (Nat.mul_le_mul_right _ (by omega))
  have hkW : 1 + x.innerCuff.length * (1 + (2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) + (gm06EncodeRows x.linkage).length)) < 2 ^ w := by
    apply gm06PhaseSize_fit x hword
    have := gm06_mul_le_sq (a := x.innerCuff.length) (b := gm06PhaseSize x m) (N := gm06PhaseSize x m)
      (by omega) le_rfl
    have hW : (1 + (2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) + (gm06EncodeRows x.linkage).length)) ≤ 6 * gm06PhaseSize x m := by omega
    have := Nat.mul_le_mul_left x.innerCuff.length hW
    have hsq : x.innerCuff.length * (6 * gm06PhaseSize x m) = 6 * (x.innerCuff.length * gm06PhaseSize x m) := by ring
    omega
  have hcnt : x.innerCuff.length * (1 + (2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) + (gm06EncodeRows x.linkage).length)) -
      (gm06EncodeRowsPayload ((gm06TerminalPhase x m).take i)).length =
      1 + (gm06TerminalPhaseRow x m i).length + (x.innerCuff.length * (1 + (2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) + (gm06EncodeRows x.linkage).length)) -
        (gm06EncodeRowsPayload ((gm06TerminalPhase x m).take (i + 1))).length) := by
    omega
  obtain ⟨s₆, t₆, he₆, ht₆, hk₆, h643₆, h700₆⟩ := gm06TerminalEmitProg_exec
    (q := x.innerCuff.length * (1 + (2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) + (gm06EncodeRows x.linkage).length)) - (gm06EncodeRowsPayload ((gm06TerminalPhase x m).take (i + 1))).length)
    (x.innerCuff.length :: gm06EncodeRowsPayload ((gm06TerminalPhase x m).take i)) (gm06TerminalPhaseRow x m i) s₅ hw1
    (by simp only [List.length_cons]; omega)
    (fun a ha => (hrowWords a ha).trans (gm06PhaseSize_fit x hword (by omega)))
    (by
      rw [e₀₅.arrs_eq_of_not_mem_writtenArrs (a := 643) (by decide), h643, hcnt])
    (by rw [e₀₅.regs_eq_of_not_mem_writtenRegs (r := 700) (by decide), h700]; simp; omega) h637₅
  have he : Exec w gm06TerminalPhaseBody s s₆ (2 + (t₁ + (2 + (t₃ + (t₄ + (t₅ + t₆)))))) :=
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ he₆)))))
  have hout : x.innerCuff.length :: gm06EncodeRowsPayload ((gm06TerminalPhase x m).take i) ++
      gm06EncodeNatList (gm06TerminalPhaseRow x m i) =
      x.innerCuff.length :: gm06EncodeRowsPayload ((gm06TerminalPhase x m).take (i + 1)) := by
    rw [hpay]; simp
  have e₁₆ := Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))
  refine ⟨s₆, _, he, ?_, he.arrs_eq_of_not_mem_writtenArrs (by decide),
    he.arrs_eq_of_not_mem_writtenArrs (by decide), he.arrs_eq_of_not_mem_writtenArrs (by decide),
    he.arrs_eq_of_not_mem_writtenArrs (by decide), he.arrs_eq_of_not_mem_writtenArrs (by decide),
    he.regs_eq_of_not_mem_writtenRegs (by decide), he.regs_eq_of_not_mem_writtenRegs (by decide),
    he.regs_eq_of_not_mem_writtenRegs (by decide), he.regs_eq_of_not_mem_writtenRegs (by decide),
    (he.regs_eq_of_not_mem_writtenRegs (r := 681) (by decide)).trans h681, ?_, ?_, ?_⟩
  · have hreadCost : t₁ ≤ 30 + 80 * gm06PhaseSize x m := by omega
    have hrowL : (gm06TerminalPhaseRow x m i).length ≤ 5 * gm06PhaseSize x m := by omega
    omega
  · rw [e₁₆.regs_eq_of_not_mem_writtenRegs (r := 693) (by decide)]
    simp only [s₂, State.setReg_regs_self]
    rw [gm06PhaseRecords_take_succ hRlen, hRi, hprelen]
    omega
  · rw [h643₆, hout]
  · rw [h700₆, hout]
    simp only [List.length_cons]
    omega

/-! ### The loop over all components -/

/-- What holds before round `i` of the loop: the saved inputs are
unchanged, the record cursor sits at record `i`, and the output buffer
holds the first `i` rows. -/
private def LoopInv (x : GM06SuccessorInput) (m : ℕ) (s₀ : State) (i : ℕ) (s : State) : Prop :=
  s.arrs 640 = s₀.arrs 640 ∧ s.arrs 641 = s₀.arrs 641 ∧ s.arrs 642 = s₀.arrs 642 ∧
    s.arrs 3 = s₀.arrs 3 ∧ s.arrs 6 = s₀.arrs 6 ∧
    s.regs 682 = s₀.regs 682 ∧ s.regs 683 = s₀.regs 683 ∧ s.regs 684 = s₀.regs 684 ∧
    s.regs 685 = s₀.regs 685 ∧ s.regs 681 = i ∧
    s.regs 693 = 1 +
      ((((gm06PhaseComponents x m).map GM06CutData.rotations).take i).flatMap gm06EncodeRows).length ∧
    s.arrs 643 = (x.innerCuff.length :: gm06EncodeRowsPayload ((gm06TerminalPhase x m).take i)) ++
      List.replicate (x.innerCuff.length * (1 + (2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) + (gm06EncodeRows x.linkage).length)) -
        (gm06EncodeRowsPayload ((gm06TerminalPhase x m).take i)).length) 0 ∧
    s.regs 700 = 1 + (gm06EncodeRowsPayload ((gm06TerminalPhase x m).take i)).length

set_option maxRecDepth 8192 in
/-- The loop runs the round once for each component. -/
private theorem terminal_loop {w m : ℕ} (x : GM06SuccessorInput) (tail : List ℕ) (s₀ : State)
    (horig : x.endpoints.length = 2 * m) (hvalues : ∀ v ∈ x.endpoints, v < x.vertexCount)
    (hdarts : ∀ d ∈ x.linkage.flatten, d < 2 * m)
    (hinner : ∀ v ∈ x.innerCuff, v < x.vertexCount) (houter : ∀ v ∈ x.outerCuff, v < x.vertexCount)
    (hcount : x.linkage.length = x.innerCuff.length)
    (hrows : x.rotations.length = x.vertexCount) (hnd : x.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (hword : 10000 * gm06PhaseSize x m ^ 3 < 2 ^ w)
    (h640 : s₀.arrs 640 = x.innerCuff.length ::
      (((gm06PhaseComponents x m).map GM06CutData.rotations).flatMap gm06EncodeRows ++ tail))
    (h640len : (s₀.arrs 640).length < 2 ^ w) (h640words : ∀ a ∈ s₀.arrs 640, a < 2 ^ w)
    (h641 : s₀.arrs 641 = (gm06CutDataOfLinkage x.vertexCount m x.endpoints x.linkage x.innerCuff
      x.outerCuff x.rotations (List.range x.vertexCount)).origins)
    (h642 : s₀.arrs 642 = gm06EncodeRows x.linkage)
    (h3 : s₀.arrs 3 = x.endpoints) (h6 : s₀.arrs 6 = x.innerCuff)
    (h685 : s₀.regs 685 = x.innerCuff.length)
    (h682 : s₀.regs 682 = 2 * x.vertexCount)
    (h683 : s₀.regs 683 = 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (h684 : s₀.regs 684 = m) (hstart : LoopInv x m s₀ 0 s₀) :
    ∃ sf t, Exec w (forUp 681 (.reg 685) gm06TerminalPhaseBody) s₀ sf t ∧
      t ≤ 3 + x.innerCuff.length * (7 + 30000 * gm06PhaseSize x m ^ 2) ∧
      LoopInv x m s₀ x.innerCuff.length sf := by
  obtain ⟨_, haugN, _, _, _, _, _, _⟩ := gm06PhaseSize_facts x m
  have hw1 : 1 < 2 ^ w := gm06PhaseSize_fit x hword (by omega)
  have hkw : x.innerCuff.length < 2 ^ w := gm06PhaseSize_fit x hword (by omega)
  have hcost : (Expr.reg 685).cost = 1 := rfl
  obtain ⟨sf, t, he, ht, hI⟩ := Crossing.forUp_exec' (LoopInv x m s₀) x.innerCuff.length
    (30000 * gm06PhaseSize x m ^ 2) (r_i := 681) (hi := .reg 685) (body := gm06TerminalPhaseBody)
    hw1 hkw
    (fun i _ st hst => ⟨hst.2.2.2.2.2.2.2.2.2.1,
      Crossing.eval_reg (hst.2.2.2.2.2.2.2.2.1.trans h685) hkw⟩)
    (fun i hi st hst => by
      obtain ⟨a640, a641, a642, a3, a6, r682, r683, r684, r685, r681, r693, a643, r700⟩ := hst
      obtain ⟨s', t', he', ht', b640, b641, b642, b3, b6, c682, c683, c684, c685, c681, c693, b643,
        c700⟩ := terminal_body x tail st horig hvalues hdarts hinner houter hcount hrows hnd hkeys
          hword hi (a640.trans h640) (by rw [a640]; exact h640len) (by rw [a640]; exact h640words)
          r693 (a641.trans h641) (a642.trans h642) (a3.trans h3) (a6.trans h6) r681
          (r685.trans h685) (r682.trans h682) (r683.trans h683) (r684.trans h684) a643 r700
      refine ⟨s', t', he', ht', ?_, c681⟩
      simp only [LoopInv, State.setReg_arrs, State.setReg_regs_self,
        State.setReg_regs_ne _ _ (show (682 : ℕ) ≠ 681 by decide),
        State.setReg_regs_ne _ _ (show (683 : ℕ) ≠ 681 by decide),
        State.setReg_regs_ne _ _ (show (684 : ℕ) ≠ 681 by decide),
        State.setReg_regs_ne _ _ (show (685 : ℕ) ≠ 681 by decide),
        State.setReg_regs_ne _ _ (show (693 : ℕ) ≠ 681 by decide),
        State.setReg_regs_ne _ _ (show (700 : ℕ) ≠ 681 by decide)]
      exact ⟨b640.trans a640, b641.trans a641, b642.trans a642, b3.trans a3, b6.trans a6,
        c682.trans r682, c683.trans r683, c684.trans r684, c685.trans r685, trivial, c693, b643, c700⟩)
    s₀ hstart
  refine ⟨sf, t, he, ?_, hI⟩
  rw [hcost] at ht
  omega

/-! ### The whole terminal phase -/

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 8192 in
/-- **The terminal phase runs as specified.** On the loop state of VI
(5.7), the program writes the encoded rows `gm06TerminalPhase x m` to
array 8 and sets register 0 to 1. It changes only register 0, array 8
and the reserved block, and its time is cubic in the input size. -/
theorem gm06TerminalPhaseProg_exec {w m : ℕ} (x : GM06SuccessorInput) (s : State)
    (horig : x.endpoints.length = 2 * m) (hvalues : ∀ v ∈ x.endpoints, v < x.vertexCount)
    (hdarts : ∀ d ∈ x.linkage.flatten, d < 2 * m)
    (hinner : ∀ v ∈ x.innerCuff, v < x.vertexCount) (houter : ∀ v ∈ x.outerCuff, v < x.vertexCount)
    (hcount : x.linkage.length = x.innerCuff.length)
    (hrows : x.rotations.length = x.vertexCount) (hnd : x.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (hword : 10000 * gm06PhaseSize x m ^ 3 < 2 ^ w)
    (h100 : s.regs 100 = x.vertexCount) (h12 : (s.arrs 12).length = m)
    (h4 : s.arrs 4 = gm06EncodeRows x.rotations) (h3 : s.arrs 3 = x.endpoints)
    (h8 : s.arrs 8 = gm06EncodeRows x.linkage) (h6 : s.arrs 6 = x.innerCuff)
    (h7 : s.arrs 7 = x.outerCuff) :
    ∃ sf t, Exec w gm06TerminalPhaseProg s sf t ∧
      t ≤ 10000000 * gm06PhaseSize x m ^ 3 ∧
      Keeps gm06TerminalPhaseRegs gm06TerminalPhaseArrs s sf ∧
      sf.arrs 8 = gm06EncodeRows (gm06TerminalPhase x m) ∧ sf.regs 0 = 1 := by
  obtain ⟨hnN, haugN, hpathN, hrotN, _, _, _, hN⟩ := gm06PhaseSize_facts x m
  have hw : 4 < 2 ^ w := gm06PhaseSize_fit x hword (by omega)
  have hrecCap := gm06PhaseRecordCapacity_le x m
  have hsearchFit : (2 * x.vertexCount) * (2 * x.vertexCount) + 2 < 2 ^ w := by
    have := gm06_mul_le_sq hnN hnN
    have hsq : 2 * x.vertexCount * (2 * x.vertexCount) = 4 * (x.vertexCount * x.vertexCount) := by ring
    exact gm06PhaseSize_fit x hword (by omega)
  have hkN : x.innerCuff.length ≤ gm06PhaseSize x m := by omega
  have hcomponentFit : 3 + x.innerCuff.length * (2 * x.vertexCount + 1) < 2 ^ w := by
    have := gm06_mul_le_sq hkN hnN
    have hsq : x.innerCuff.length * (2 * x.vertexCount + 1) =
        2 * (x.innerCuff.length * x.vertexCount) + x.innerCuff.length := by ring
    exact gm06PhaseSize_fit x hword (by omega)
  have hmaterialFit : 3 + x.innerCuff.length * (1 + 2 * (gm06EncodeRows x.rotations).length) < 2 ^ w :=
    gm06PhaseSize_fit x hword (by omega)
  have hpathWords := gm06PhaseLinkage_words x hdarts hword
  have hrotWords := gm06PhaseRotation_words x hrows hkeys hword
  -- The output buffer has room for `k` rows of at most `W` words.
  have hW : (1 + (2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) + (gm06EncodeRows x.linkage).length)) ≤ 6 * gm06PhaseSize x m := by omega
  have hkW : x.innerCuff.length * (1 + (2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) + (gm06EncodeRows x.linkage).length)) ≤ 6 * gm06PhaseSize x m ^ 2 := by
    have h1 := Nat.mul_le_mul hkN hW
    have h2 : gm06PhaseSize x m * (6 * gm06PhaseSize x m) = 6 * gm06PhaseSize x m ^ 2 := by ring
    omega
  -- The cut.
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hres₁⟩ := gm06PhaseCutProg_exec x s hw (gm06PhaseSize_fit x hword (by omega))
    (gm06PhaseSize_fit x hword (by omega)) horig hvalues hdarts hinner houter hrows hnd hkeys
    (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega)) hpathWords
    (gm06PhaseSize_fit x hword (by omega)) hrotWords hsearchFit hcomponentFit hmaterialFit
    h100 h12 h4 h3 h8 h6 h7
  obtain ⟨h626₁, h601len, h601words⟩ := gm06PhaseCutProg_buffers x s s₁ hw
    (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega)) horig hvalues hdarts hinner houter
    hrows hnd hkeys (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega)) hpathWords
    (gm06PhaseSize_fit x hword (by omega)) hrotWords hsearchFit hmaterialFit h100 h12 h4 h3 h8 h6 h7 he₁
  obtain ⟨tail, h601⟩ := gm06CutAlongLinkageResult_array_records hres₁
  rw [gm06PhaseComponents_length] at h601
  have hdataSizes := gm06CutDataOfLinkage_sizes x.vertexCount m x.endpoints x.linkage x.innerCuff
    x.outerCuff x.rotations (List.range x.vertexCount)
  have horigBounds := gm06CutDataOfLinkage_origin_bounds x.endpoints x.linkage x.innerCuff x.outerCuff
    x.rotations (List.range x.vertexCount) hrows horig hvalues hinner houter
  have hca : ∀ a, a ∉ gm06PhaseCutProg.writtenArrs → s₁.arrs a = s.arrs a :=
    fun a ha => he₁.arrs_eq_of_not_mem_writtenArrs ha
  have hcr : ∀ r, r ∉ gm06PhaseCutProg.writtenRegs → s₁.regs r = s.regs r :=
    fun r hr => he₁.regs_eq_of_not_mem_writtenRegs hr
  -- Save the cut output.
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, h640₂, h641₂, h642₂, h682₂, h683₂, h684₂, h685₂, h693₂, h681₂, _⟩ :=
    gm06Reduction4PhaseSaveProg_exec (n := x.vertexCount) (m := m) x.innerCuff x.outerCuff (s₁.arrs 601)
      (s₁.arrs 626) x.linkage s₁ (by omega) (gm06PhaseSize_fit x hword (by omega))
      (gm06PhaseSize_fit x hword (by omega)) (by rw [h601len]; exact gm06PhaseSize_fit x hword (by omega))
      (by rw [h626₁, hdataSizes.2.1]; exact gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega))
      h601words (by rw [h626₁]; exact fun a ha => (horigBounds a ha).trans (gm06PhaseSize_fit x hword (by omega)))
      hpathWords rfl rfl ((hca 8 (by decide)).trans h8) ((hcr 100 (by decide)).trans h100)
      (by rw [hca 12 (by decide)]; exact h12) ((hca 6 (by decide)).trans h6) ((hca 7 (by decide)).trans h7)
  have hs₂a : ∀ a, a ∉ gm06Reduction4PhaseSaveProg.writtenArrs → s₂.arrs a = s₁.arrs a :=
    fun a ha => he₂.arrs_eq_of_not_mem_writtenArrs ha
  -- The output buffer.
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, h643₃, h700₃⟩ := gm06TerminalOutputInitProg_exec
    (k := x.innerCuff.length) (a := 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (c := (gm06EncodeRows x.linkage).length) s₂ (by omega)
    (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega)) h685₂ h683₂
    (by rw [h642₂])
  have hs₃a : ∀ a, a ≠ 643 → s₃.arrs a = s₂.arrs a := fun a ha => hk₃.2 a (by simpa using ha)
  have hs₃r : ∀ r, r ≠ 700 → s₃.regs r = s₂.regs r := fun r hr => hk₃.1 r (by simpa using hr)
  -- The loop.
  obtain ⟨s₄, t₄, he₄, ht₄, hI⟩ := terminal_loop x tail s₃ horig hvalues hdarts hinner houter hcount
    hrows hnd hkeys hword
    ((hs₃a 640 (by decide)).trans (h640₂.trans h601))
    (by rw [hs₃a 640 (by decide), h640₂, h601len]; exact gm06PhaseSize_fit x hword (by omega))
    (by rw [hs₃a 640 (by decide), h640₂]; exact h601words)
    ((hs₃a 641 (by decide)).trans (h641₂.trans h626₁))
    ((hs₃a 642 (by decide)).trans h642₂)
    ((hs₃a 3 (by decide)).trans ((hs₂a 3 (by decide)).trans ((hca 3 (by decide)).trans h3)))
    ((hs₃a 6 (by decide)).trans ((hs₂a 6 (by decide)).trans ((hca 6 (by decide)).trans h6)))
    ((hs₃r 685 (by decide)).trans h685₂) ((hs₃r 682 (by decide)).trans h682₂)
    ((hs₃r 683 (by decide)).trans h683₂) ((hs₃r 684 (by decide)).trans h684₂)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, (hs₃r 681 (by decide)).trans h681₂,
      by rw [hs₃r 693 (by decide), h693₂]; simp,
      by rw [h643₃]; simp [gm06EncodeRowsPayload], by rw [h700₃]; simp [gm06EncodeRowsPayload]⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h643₄, h700₄⟩ := hI
  have htake : (gm06TerminalPhase x m).take x.innerCuff.length = gm06TerminalPhase x m :=
    List.take_of_length_le (by rw [gm06TerminalPhase_length])
  rw [htake] at h643₄ h700₄
  -- Copy the rows to array 8.
  have hpayLe : (gm06EncodeRowsPayload (gm06TerminalPhase x m)).length ≤
      x.innerCuff.length * (1 + (2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) + (gm06EncodeRows x.linkage).length)) := by
    have h := gm06EncodeRowsPayload_length_le (gm06TerminalPhase x m) (1 + (2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) + (gm06EncodeRows x.linkage).length)) (by
      intro r hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have := (gm06TerminalPhaseRow_facts x horig hvalues hdarts hinner houter hcount hrows hnd hkeys
        (List.mem_range.mp hj)).1
      omega)
    rwa [gm06TerminalPhase_length] at h
  have hxsLen : (gm06EncodeRows (gm06TerminalPhase x m)).length =
      1 + (gm06EncodeRowsPayload (gm06TerminalPhase x m)).length := by
    simp only [gm06EncodeRows, List.length_cons]; omega
  have hxsFit : (gm06EncodeRows (gm06TerminalPhase x m)).length < 2 ^ w :=
    gm06PhaseSize_fit x hword (by omega)
  have hxsWords : ∀ a ∈ gm06EncodeRows (gm06TerminalPhase x m), a < 2 ^ w := by
    apply gm06EncodeRows_words
    · rw [gm06TerminalPhase_length]; exact gm06PhaseSize_fit x hword (by omega)
    · intro r hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have := (gm06TerminalPhaseRow_facts x horig hvalues hdarts hinner houter hcount hrows hnd hkeys
        (List.mem_range.mp hj)).1
      exact gm06PhaseSize_fit x hword (by omega)
    · intro d hd
      obtain ⟨r, hr, hdr⟩ := List.mem_flatten.mp hd
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have := (gm06TerminalPhaseRow_facts x horig hvalues hdarts hinner houter hcount hrows hnd hkeys
        (List.mem_range.mp hj)).2 d hdr
      exact gm06PhaseSize_fit x hword (by omega)
  have hxs : gm06EncodeRows (gm06TerminalPhase x m) =
      x.innerCuff.length :: gm06EncodeRowsPayload (gm06TerminalPhase x m) := by
    rw [gm06EncodeRows, gm06TerminalPhase_length]
  obtain ⟨s₅, t₅, he₅, ht₅, _, h8₅⟩ := gm06PhaseCopyPrefixProg_exec 643 8 (by decide) (.reg 700)
    (gm06EncodeRows (gm06TerminalPhase x m)) _ s₄ (by omega) hxsFit hxsWords
    (by rw [h643₄, hxs])
    (fun st hst => Crossing.eval_reg ((hst.1 700 (by decide)).trans (h700₄.trans hxsLen.symm)) hxsFit)
  -- Answer 1.
  have he₆ : Exec w (.assign 0 (.const 1)) s₅ (s₅.setReg 0 1) _ :=
    .assign (Crossing.eval_const (by omega))
  have he : Exec w gm06TerminalPhaseProg s (s₅.setReg 0 1) (t₁ + (t₂ + (t₃ + (t₄ + (t₅ + _))))) :=
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ he₆))))
  refine ⟨_, _, he, ?_, gm06TerminalPhaseProg_frame he, by rw [State.setReg_arrs, h8₅],
    State.setReg_regs_self _ _ _⟩
  have hc := ht₁.trans (gm06PhaseCutCost_le_size x m)
  have hs : t₂ ≤ 50 + 14 * (4 * gm06PhaseSize x m ^ 2 + 4 * gm06PhaseSize x m +
      gm06PhaseSize x m) := by
    rw [h601len, h626₁, hdataSizes.2.1] at ht₂
    omega
  have hcost : (Expr.reg 700).cost = 1 := rfl
  have hcost' : (Expr.const 1).cost = 1 := rfl
  rw [hcost] at ht₅
  rw [hcost']
  have hloop : x.innerCuff.length * (7 + 30000 * gm06PhaseSize x m ^ 2) ≤
      30007 * gm06PhaseSize x m ^ 3 := by
    have h1 := Nat.mul_le_mul_right (7 + 30000 * gm06PhaseSize x m ^ 2) hkN
    have h2 : gm06PhaseSize x m * (7 + 30000 * gm06PhaseSize x m ^ 2) =
        7 * gm06PhaseSize x m + 30000 * gm06PhaseSize x m ^ 3 := by ring
    have h3 : gm06PhaseSize x m ≤ gm06PhaseSize x m ^ 3 := by
      calc gm06PhaseSize x m = gm06PhaseSize x m ^ 1 := (pow_one _).symm
        _ ≤ gm06PhaseSize x m ^ 3 := Nat.pow_le_pow_right hN (by decide)
    omega
  have hsq : gm06PhaseSize x m ^ 2 ≤ gm06PhaseSize x m ^ 3 := Nat.pow_le_pow_right hN (by decide)
  have hlin : gm06PhaseSize x m ≤ gm06PhaseSize x m ^ 3 := by
    calc gm06PhaseSize x m = gm06PhaseSize x m ^ 1 := (pow_one _).symm
      _ ≤ gm06PhaseSize x m ^ 3 := Nat.pow_le_pow_right hN (by decide)
  omega

end GraphMinor.Compute
