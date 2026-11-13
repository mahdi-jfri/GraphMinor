module

public import GraphMinor.Compute.CrossingClassSweepInsert

/-!
# The full bridge-candidate sweep

This file implements the full loop of the bridge-candidate sweep in Section 5.2 of
`docs/crossing/crossing_extractor.tex`. The execution theorems follow the stored candidates and
bound the
number of Word RAM steps.
-/

@[expose] public section

namespace GraphMinor.Compute

open GraphMinor.Crossing

/-! ### 7. Full sweep loop: `sweepStepProg`, `sweepWhile`, and `sweepProg` -/

theorem length_cleanStack_le (l : ℕ) (st : List Block) :
    (cleanStack l st).length ≤ st.length := by
  induction st with
  | nil => simp [cleanStack]
  | cons B rest ih =>
    simp only [cleanStack]
    split_ifs
    · exact le_trans ih (by simp)
    · simp

theorem length_insertCandidate_le (I : Candidate) (st : List Block) :
    (insertCandidate I st).length ≤ st.length + 1 := by
  cases st with
  | nil => simp [insertCandidate]
  | cons B rest =>
    simp only [insertCandidate]
    split_ifs <;> simp

theorem storedCandidates_insertCandidate_perm (I : Candidate) (st : List Block) :
    (storedCandidates (insertCandidate I st)).Perm (I :: storedCandidates st) := by
  cases st with
  | nil => simp [insertCandidate, storedCandidates]
  | cons B rest =>
    simp only [insertCandidate]
    split_ifs
    · simp only [storedCandidates, List.flatMap_cons, List.append_assoc, List.singleton_append]
      exact List.perm_middle
    · simp [storedCandidates]

/-- A candidate list `sorted` has at most 6 active candidates of any single color `γ` at any cut
position `l₀`. -/
def BoundedActivePerColor (sorted : List Candidate) : Prop :=
  ∀ γ l₀, (sorted.filter (fun J => (J.γ == γ) && decide (J.l ≤ l₀ ∧ l₀ < J.r))).length ≤ 6

theorem block_length_le_six_of_boundedActive {sorted : List Candidate}
    (hBound : BoundedActivePerColor sorted)
    {st : List Block} (hInv : StackInv st) (l₀ : ℕ)
    (hl_le : ∀ J ∈ storedCandidates st, J.l ≤ l₀)
    (hcnt : ∀ P : Candidate → Bool, ((storedCandidates st).filter P).length ≤ (sorted.filter P).length) :
    ∀ B' ∈ cleanStack l₀ st, B'.items.length ≤ 6 := by
  intro B' hB'
  set st₁ := cleanStack l₀ st
  have hst₁ : StackInv st₁ := cleanStack_stackInv l₀ hInv
  have hsub_items := (Block.items_sublist_storedCandidates_filter hst₁ hB').length_le
  set P : Candidate → Bool := fun J => (J.γ == B'.γ) && decide (J.l ≤ l₀ ∧ l₀ < J.r)
  have hfilt_eq :
      (storedCandidates st₁).filter (fun J => J.γ == B'.γ) = (storedCandidates st₁).filter P := by
    apply List.filter_congr
    intro J hJ
    have hmem := (mem_storedCandidates_cleanStack_iff l₀ hInv J).mp hJ
    have hJl : J.l ≤ l₀ := hl_le J hmem.1
    have hJr : l₀ < J.r := hmem.2
    simp [P, hJl, hJr]
  have hsub_clean := ((storedCandidates_cleanStack_sublist l₀ st).filter P).length_le
  have hle_sorted := hcnt P
  have hle_six := hBound B'.γ l₀
  rw [hfilt_eq] at hsub_items
  exact le_trans hsub_items (le_trans hsub_clean (le_trans hle_sorted hle_six))

/-- One iteration of the sweep loop at index `rSweepIdx`. -/
def sweepStepProg : Cmd :=
  .seq (.assign rCurL (.read aCandL (.reg rSweepIdx)))
  (.seq (.assign rCurR (.read aCandR (.reg rSweepIdx)))
  (.seq (.assign rCurG (.read aCandG (.reg rSweepIdx)))
  (.seq cleanStackProg
  (.seq firstDiffProg
  (.ite (.op .eq (.reg rDiffFound) (.const 1))
    (.seq minRightProg
    (.ite (.op .lt (.reg rMinR) (.reg rCurR))
      (.seq (.assign rSweepFound (.const 1))
      (.seq (.assign rOutI1L (.reg rMinL))
      (.seq (.assign rOutI1R (.reg rMinR))
      (.seq (.assign rOutI1G (.reg rMinG))
      (.seq (.assign rOutI2L (.reg rCurL))
      (.seq (.assign rOutI2R (.reg rCurR))
      (.seq (.assign rOutI2G (.reg rCurG))
            (.assign rSweepIdx (.reg rNumCand)))))))))
      (.seq insertCandProg
            (.assign rSweepIdx (.op .add (.reg rSweepIdx) (.const 1))))))
    (.seq insertCandProg
          (.assign rSweepIdx (.op .add (.reg rSweepIdx) (.const 1)))))))))

/-- While loop of `sweepProg`. -/
def sweepWhile : Cmd :=
  .while (.op .lt (.reg rSweepIdx) (.reg rNumCand)) sweepStepProg

/-- Complete sweep program over `(aCandL, aCandR, aCandG)` of length `rNumCand` with stack capacity
`rCandCap`: allocates the 6 stack arrays, initializes `rBlkCnt := 0`, `rItemCnt := 0`,
`rSweepIdx := 0`, `rSweepFound := 0`, and runs `sweepWhile`. -/
def sweepProg : Cmd :=
  .seq (.alloc aBlkG (.reg rCandCap))
  (.seq (.alloc aBlkSt (.reg rCandCap))
  (.seq (.alloc aBlkEn (.reg rCandCap))
  (.seq (.alloc aItemL (.reg rCandCap))
  (.seq (.alloc aItemR (.reg rCandCap))
  (.seq (.alloc aItemG (.reg rCandCap))
  (.seq (.assign rBlkCnt (.const 0))
  (.seq (.assign rItemCnt (.const 0))
  (.seq (.assign rSweepIdx (.const 0))
  (.seq (.assign rSweepFound (.const 0))
        sweepWhile)))))))))

private theorem blk_color_lt_of_items {w : ℕ} {st : List Block} (hInv : StackInv st)
    (hItemsW : ∀ J ∈ storedCandidates st, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w) :
    ∀ B ∈ st, B.γ < 2 ^ w := by
  intro B hB
  obtain ⟨hne, hmono⟩ := hInv.wf B hB
  obtain ⟨J, hJ⟩ := List.exists_mem_of_ne_nil B.items hne
  have hJ_st : J ∈ storedCandidates st := List.mem_flatMap.mpr ⟨B, hB, hJ⟩
  rw [← hmono J hJ]
  exact (hItemsW J hJ_st).2.2

private theorem sweep_arr_ne_1 {a : Arr} (ha : a < 120) :
    a ≠ aBlkEn ∧ a ≠ aItemL ∧ a ≠ aItemR ∧ a ≠ aItemG := by
  revert a ha; decide

private theorem sweep_arr_ne_2 {a : Arr} (ha : a < 120) :
    a ≠ aBlkG ∧ a ≠ aBlkSt ∧ a ≠ aBlkEn ∧ a ≠ aItemL ∧ a ≠ aItemR ∧ a ≠ aItemG := by
  revert a ha; decide

private theorem sweep_reg_ne_clean {r : Reg} (hr : r < 105) :
    r ≠ rG ∧ r ≠ rM ∧ r ≠ rTmp1 ∧ r ≠ rTmp2 ∧ r ≠ rTmp3 ∧ r ≠ rTmp4 ∧
    r ≠ rCandTmp1 ∧ r ≠ rCandTmp2 ∧ r ≠ rBlkCnt ∧ r ≠ rItemCnt := by
  revert r hr; decide

private theorem sweep_reg_ne_diff {r : Reg} (hr : r < 105) :
    r ≠ rDiffFound ∧ r ≠ rDiffSt ∧ r ≠ rDiffEn ∧ r ≠ rG ∧ r ≠ rM ∧ r ≠ rTmp1 ∧ r ≠ rTmp2 := by
  revert r hr; decide

private theorem sweep_reg_ne_min {r : Reg} (hr : r < 105) :
    r ≠ rMinL ∧ r ≠ rMinR ∧ r ≠ rMinG ∧ r ≠ rTmp2 ∧ r ≠ rM ∧ r ≠ rCandTmp1 ∧ r ≠ rCandTmp2 := by
  revert r hr; decide

private theorem sweep_reg_ne_ins {r : Reg} (hr : r < 105) :
    r ≠ rBlkCnt ∧ r ≠ rItemCnt ∧ r ≠ rG ∧ r ≠ rTmp1 ∧ r ≠ rTmp2 := by
  revert r hr; decide

private theorem sweep_reg_ne_cur {r : Reg} (hr : r < 105) :
    r ≠ rSweepIdx ∧ r ≠ rCurL ∧ r ≠ rCurR ∧ r ≠ rCurG := by
  revert r hr; decide

private theorem sweep_reg_ne_out {r : Reg} (hr : r < 105) :
    r ≠ rSweepIdx ∧ r ≠ rOutI2G ∧ r ≠ rOutI2R ∧ r ≠ rOutI2L ∧
    r ≠ rOutI1G ∧ r ≠ rOutI1R ∧ r ≠ rOutI1L ∧ r ≠ rSweepFound := by
  revert r hr; decide

private theorem sweep_reg_ne_init {r : Reg} (hr : r < 105) :
    r ≠ rSweepFound ∧ r ≠ rSweepIdx ∧ r ≠ rItemCnt ∧ r ≠ rBlkCnt := by
  revert r hr; decide

/-- Execution of a single sweep step `sweepStepProg`. -/
private theorem sweepStepProg_exec {w : ℕ} (cap i : ℕ) (sorted : List Candidate)
    (hi : i < sorted.length) (st : List Block) (s : State)
    (hw : 1 < 2 ^ w) (hcap : cap < 2 ^ w)
    (hCand : IsCandArray sorted cap aCandL aCandR aCandG rNumCand s)
    (hrIdx : s.regs rSweepIdx = i)
    (hrFound : s.regs rSweepFound = 0)
    (hst : IsBlockStack cap st s)
    (hble : st.length ≤ i)
    (henle : (storedCandidates st).length ≤ i)
    (hInv : StackInv st)
    (hItemsW : ∀ J ∈ storedCandidates st, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w)
    (hSortedW : ∀ J ∈ sorted, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w)
    (hSix : ∀ B' ∈ cleanStack (sorted[i]'hi).l st, B'.items.length ≤ 6) :
    ∃ s' t, Exec w sweepStepProg s s' t ∧
      t ≤ 650 + 85 * ((storedCandidates st).length -
        (storedCandidates (cleanStack (sorted[i]'hi).l st)).length) ∧
      IsCandArray sorted cap aCandL aCandR aCandG rNumCand s' ∧
      (∀ r < 105, s'.regs r = s.regs r) ∧
      (∀ a < 120, s'.arrs a = s.arrs a) ∧
      match sweepStep st (sorted[i]'hi) with
      | Sum.inr (J, I') =>
        s'.regs rSweepFound = 1 ∧
        s'.regs rSweepIdx = sorted.length ∧
        s'.regs rOutI1L = J.l ∧ s'.regs rOutI1R = J.r ∧ s'.regs rOutI1G = J.γ ∧
        s'.regs rOutI2L = I'.l ∧ s'.regs rOutI2R = I'.r ∧ s'.regs rOutI2G = I'.γ
      | Sum.inl st' =>
        s'.regs rSweepFound = 0 ∧
        s'.regs rSweepIdx = i + 1 ∧
        IsBlockStack cap st' s' ∧
        st'.length ≤ i + 1 ∧
        (storedCandidates st').length ≤ i + 1 ∧
        (∀ J ∈ storedCandidates st', J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w) := by
  set I := sorted[i]'hi with hI_def
  set st₁ := cleanStack I.l st with hst₁_def
  have hrCnt : s.regs rNumCand = sorted.length := hCand.1
  have hsorted_le : sorted.length ≤ cap := hCand.2.2.2.2.1
  obtain ⟨hIl, hIr, hIγ⟩ := hSortedW I (List.getElem_mem hi)
  obtain ⟨hCandL_i, hCandR_i, hCandG_i⟩ := hCand.2.2.2.2.2 i hi
  let s₁ := s.setReg rCurL I.l
  have he1 : (Expr.read aCandL (.reg rSweepIdx)).eval w s = some I.l :=
    read_reg_eval hrIdx (by omega) hCandL_i hIl
  let s₂ := s₁.setReg rCurR I.r
  have he2 : (Expr.read aCandR (.reg rSweepIdx)).eval w s₁ = some I.r :=
    read_reg_eval (by simp [s₁, hrIdx]) (by omega) hCandR_i hIr
  let s₃ := s₂.setReg rCurG I.γ
  have he3 : (Expr.read aCandG (.reg rSweepIdx)).eval w s₂ = some I.γ :=
    read_reg_eval (by simp [s₂, s₁, hrIdx]) (by omega) hCandG_i hIγ
  have hst₃ : IsBlockStack cap st s₃ :=
    hst.setReg_other _ _ ⟨by decide, by decide⟩
      |>.setReg_other _ _ ⟨by decide, by decide⟩
      |>.setReg_other _ _ ⟨by decide, by decide⟩
  rcases cleanStackProg_exec cap I.l st s₃ hw hcap hIl hInv hItemsW hSix hst₃
    (by simp [s₃, s₂, s₁]) with
    ⟨s₄, tClean, hexClean, htClean, hst₄, hCurL₄, hRegs₄, hArrs₄⟩
  rw [← hst₁_def] at htClean hst₄
  have hCurR₄ : s₄.regs rCurR = I.r := by
    rw [hRegs₄ rCurR ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide⟩]
    simp [s₃, s₂]
  have hCurG₄ : s₄.regs rCurG = I.γ := by
    rw [hRegs₄ rCurG ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide⟩]
    simp [s₃]
  have hst₁_inv : StackInv st₁ := cleanStack_stackInv I.l hInv
  have hItemsW₁ : ∀ J ∈ storedCandidates st₁, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w := by
    intro J hJ
    exact hItemsW J ((storedCandidates_cleanStack_sublist I.l st).subset hJ)
  have hBlkW₁ : ∀ B ∈ st₁, B.γ < 2 ^ w := blk_color_lt_of_items hst₁_inv hItemsW₁
  rcases firstDiffProg_exec cap I.γ st₁ s₄ hw hcap hIγ hBlkW₁ hst₄ hCurG₄ with
    ⟨s₅, tDiff, hexDiff, htDiff, hst₅, hRegs₅, hArrs₅, hDiffSpec⟩
  have hCurL₅ : s₅.regs rCurL = I.l := by
    rw [hRegs₅ rCurL ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩]
    exact hCurL₄
  have hCurR₅ : s₅.regs rCurR = I.r := by
    rw [hRegs₅ rCurR ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩]
    exact hCurR₄
  have hCurG₅ : s₅.regs rCurG = I.γ := by
    rw [hRegs₅ rCurG ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩]
    exact hCurG₄
  have hrIdx₅ : s₅.regs rSweepIdx = i := by
    rw [hRegs₅ rSweepIdx ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
        hRegs₄ rSweepIdx ⟨by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide⟩]
    simp [s₃, s₂, s₁, hrIdx]
  have hrCnt₅ : s₅.regs rNumCand = sorted.length := by
    rw [hRegs₅ rNumCand ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
        hRegs₄ rNumCand ⟨by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide⟩]
    simp [s₃, s₂, s₁, hrCnt]
  have hrFound₅ : s₅.regs rSweepFound = 0 := by
    rw [hRegs₅ rSweepFound ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
        hRegs₄ rSweepFound ⟨by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, by decide⟩]
    simp [s₃, s₂, s₁, hrFound]
  have hst₁_len : st₁.length ≤ i := le_trans (length_cleanStack_le I.l st) hble
  have hst₁_stored_len : (storedCandidates st₁).length ≤ i :=
    le_trans (storedCandidates_cleanStack_sublist I.l st).length_le henle
  cases hfirst : firstDiffBlock I.γ st₁ with
  | none =>
    rw [hfirst] at hDiffSpec
    have hcondDiff : (Expr.op .eq (.reg rDiffFound) (.const 1)).eval w s₅ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hDiffSpec, hw,
        show (0 : ℕ) < 2 ^ w by omega]
    rcases insertCandProg_exec cap I st₁ s₅ hw hcap ⟨hIl, hIr, hIγ⟩ hBlkW₁ hst₅
      (by omega) (by omega) hCurL₅ hCurR₅ hCurG₅ with
      ⟨s₆, tIns, hexIns, htIns, hst₆, hRegs₆, hArrs₆⟩
    have hrIdx₆ : s₆.regs rSweepIdx = i := by
      rw [hRegs₆ rSweepIdx ⟨by decide, by decide, by decide, by decide, by decide⟩]
      exact hrIdx₅
    let s₇ := s₆.setReg rSweepIdx (i + 1)
    have he7 : (Expr.op .add (.reg rSweepIdx) (.const 1)).eval w s₆ = some (i + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrIdx₆, hw,
        show i < 2 ^ w by omega, show i + 1 < 2 ^ w by omega]
    have hex : Exec w sweepStepProg s s₇ _ :=
      .seq (.assign he1) (.seq (.assign he2) (.seq (.assign he3)
        (.seq hexClean (.seq hexDiff
          (.ite_false hcondDiff (.seq hexIns (.assign he7)))))))
    have hArrs_lt120 : ∀ a < 120, s₇.arrs a = s.arrs a := by
      intro a ha
      simp only [s₇, State.setReg_arrs]
      rw [hArrs₆ a (sweep_arr_ne_2 ha), hArrs₅ a, hArrs₄ a (sweep_arr_ne_1 ha)]
      rfl
    have hrCnt₇ : s₇.regs rNumCand = s.regs rNumCand := by
      simp only [s₇, State.setReg_regs_ne _ _ (by decide : rNumCand ≠ rSweepIdx)]
      rw [hRegs₆ rNumCand ⟨by decide, by decide, by decide, by decide, by decide⟩, hrCnt₅, hrCnt]
    refine ⟨s₇, _, hex, by dsimp [Expr.cost]; omega, ?_, ?_, hArrs_lt120, ?_⟩
    · exact hCand.of_eq hrCnt₇ (hArrs_lt120 aCandL (by decide))
        (hArrs_lt120 aCandR (by decide)) (hArrs_lt120 aCandG (by decide))
    · intro r hr
      have hr_cur := sweep_reg_ne_cur hr
      simp only [s₇, State.setReg_regs_ne _ _ hr_cur.1]
      rw [hRegs₆ r (sweep_reg_ne_ins hr), hRegs₅ r (sweep_reg_ne_diff hr),
          hRegs₄ r (sweep_reg_ne_clean hr)]
      simp [s₃, s₂, s₁, hr_cur.2.1, hr_cur.2.2.1, hr_cur.2.2.2]
    · simp only [sweepStep, ← hst₁_def, hfirst]
      refine ⟨?_, by simp [s₇],
        hst₆.setReg_other _ _ ⟨by decide, by decide⟩,
        le_trans (length_insertCandidate_le I st₁) (by omega),
        by rw [length_storedCandidates_insertCandidate]; omega, ?_⟩
      · simp only [s₇, State.setReg_regs_ne _ _ (by decide : rSweepFound ≠ rSweepIdx)]
        rw [hRegs₆ rSweepFound ⟨by decide, by decide, by decide, by decide, by decide⟩]
        exact hrFound₅
      · intro J hJ
        rcases (mem_storedCandidates_insertCandidate_iff I st₁ J).mp hJ with rfl | hJ₁
        · exact ⟨hIl, hIr, hIγ⟩
        · exact hItemsW₁ J hJ₁
  | some B =>
    rw [hfirst] at hDiffSpec
    rcases hDiffSpec with ⟨hrDiffFound, st₀, hrDiffSt, hrDiffEn, hst₀_le, hBItems⟩
    have hB_mem : B ∈ st₁ := (firstDiffBlock_mem_and_ne hfirst).1
    have hB_ne : B.items ≠ [] := (hst₁_inv.wf B hB_mem).1
    have hB_six : B.items.length ≤ 6 := hSix B hB_mem
    have hB_W : ∀ J ∈ B.items, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w := by
      intro J hJ
      exact hItemsW₁ J (List.mem_flatMap.mpr ⟨B, hB_mem, hJ⟩)
    have hcondDiff : (Expr.op .eq (.reg rDiffFound) (.const 1)).eval w s₅ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrDiffFound, hw]
    rcases minRightProg_exec st₀ B.items hB_ne s₅ hw (by omega) hB_W hrDiffSt hrDiffEn hBItems with
      ⟨s₆, tMin, J_min, hexMin, htMin, hMinEq, hrMinL, hrMinR, hrMinG, hRegsMin, hArrsMin⟩
    have hJmin_mem : J_min ∈ B.items := minRightCandidate_mem hMinEq
    obtain ⟨hJmin_l, hJmin_r, hJmin_γ⟩ := hB_W J_min hJmin_mem
    have hst₆ : IsBlockStack cap st₁ s₆ := by
      rcases hst₅ with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
      refine ⟨by rw [hArrsMin]; exact h1, by rw [hArrsMin]; exact h2, by rw [hArrsMin]; exact h3,
        by rw [hArrsMin]; exact h4, by rw [hArrsMin]; exact h5, by rw [hArrsMin]; exact h6,
        ?_, ?_, h9, h10, ?_⟩
      · rw [hRegsMin rBlkCnt ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩]
        exact h7
      · rw [hRegsMin rItemCnt ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩]
        exact h8
      · refine h11.of_agree_below (fun _ _ => by rw [hArrsMin]) (fun _ _ => by rw [hArrsMin])
          (fun _ _ => by rw [hArrsMin]) (fun _ _ => by rw [hArrsMin])
          (fun _ _ => by rw [hArrsMin]) (fun _ _ => by rw [hArrsMin])
    have hCurL₆ : s₆.regs rCurL = I.l := by
      rw [hRegsMin rCurL ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩]
      exact hCurL₅
    have hCurR₆ : s₆.regs rCurR = I.r := by
      rw [hRegsMin rCurR ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩]
      exact hCurR₅
    have hCurG₆ : s₆.regs rCurG = I.γ := by
      rw [hRegsMin rCurG ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩]
      exact hCurG₅
    have hrIdx₆ : s₆.regs rSweepIdx = i := by
      rw [hRegsMin rSweepIdx ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩]
      exact hrIdx₅
    have hrCnt₆ : s₆.regs rNumCand = sorted.length := by
      rw [hRegsMin rNumCand ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩]
      exact hrCnt₅
    have hrFound₆ : s₆.regs rSweepFound = 0 := by
      rw [hRegsMin rSweepFound ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩]
      exact hrFound₅
    by_cases hlt_r : J_min.r < I.r
    · have hcondCross : (Expr.op .lt (.reg rMinR) (.reg rCurR)).eval w s₆ = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrMinR, hCurR₆, hJmin_r, hIr, hlt_r, hw]
      let s₇ := s₆.setReg rSweepFound 1
      have he7 : (Expr.const 1).eval w s₆ = some 1 := by simp [Expr.eval, checkWord, hw]
      let s₈ := s₇.setReg rOutI1L J_min.l
      have he8 : (Expr.reg rMinL).eval w s₇ = some J_min.l := by
        simp [Expr.eval, s₇, hrMinL, checkWord, hJmin_l]
      let s₉ := s₈.setReg rOutI1R J_min.r
      have he9 : (Expr.reg rMinR).eval w s₈ = some J_min.r := by
        simp [Expr.eval, s₈, s₇, hrMinR, checkWord, hJmin_r]
      let s₁₀ := s₉.setReg rOutI1G J_min.γ
      have he10 : (Expr.reg rMinG).eval w s₉ = some J_min.γ := by
        simp [Expr.eval, s₉, s₈, s₇, hrMinG, checkWord, hJmin_γ]
      let s₁₁ := s₁₀.setReg rOutI2L I.l
      have he11 : (Expr.reg rCurL).eval w s₁₀ = some I.l := by
        simp [Expr.eval, s₁₀, s₉, s₈, s₇, hCurL₆, checkWord, hIl]
      let s₁₂ := s₁₁.setReg rOutI2R I.r
      have he12 : (Expr.reg rCurR).eval w s₁₁ = some I.r := by
        simp [Expr.eval, s₁₁, s₁₀, s₉, s₈, s₇, hCurR₆, checkWord, hIr]
      let s₁₃ := s₁₂.setReg rOutI2G I.γ
      have he13 : (Expr.reg rCurG).eval w s₁₂ = some I.γ := by
        simp [Expr.eval, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, hCurG₆, checkWord, hIγ]
      let s₁₄ := s₁₃.setReg rSweepIdx sorted.length
      have he14 : (Expr.reg rNumCand).eval w s₁₃ = some sorted.length := by
        simp [Expr.eval, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, hrCnt₆, checkWord,
          show sorted.length < 2 ^ w by omega]
      have hex : Exec w sweepStepProg s s₁₄ _ :=
        .seq (.assign he1) (.seq (.assign he2) (.seq (.assign he3)
          (.seq hexClean (.seq hexDiff
            (.ite_true hcondDiff (by dsimp [Expr.cost]; omega)
              (.seq hexMin
                (.ite_true hcondCross (by dsimp [Expr.cost]; omega)
                  (.seq (.assign he7) (.seq (.assign he8) (.seq (.assign he9)
                  (.seq (.assign he10) (.seq (.assign he11) (.seq (.assign he12)
                  (.seq (.assign he13) (.assign he14)))))))))))))))
      have hArrs_lt120 : ∀ a < 120, s₁₄.arrs a = s.arrs a := by
        intro a ha
        simp only [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, State.setReg_arrs]
        rw [hArrsMin a, hArrs₅ a, hArrs₄ a (sweep_arr_ne_1 ha)]
        rfl
      have hrCnt₁₄ : s₁₄.regs rNumCand = s.regs rNumCand := by
        simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇, hrCnt₆, hrCnt]
      refine ⟨s₁₄, _, hex, by dsimp [Expr.cost]; omega, ?_, ?_, hArrs_lt120, ?_⟩
      · exact hCand.of_eq hrCnt₁₄ (hArrs_lt120 aCandL (by decide))
          (hArrs_lt120 aCandR (by decide)) (hArrs_lt120 aCandG (by decide))
      · intro r hr
        have hr_ne := sweep_reg_ne_out hr
        have hr_cur := sweep_reg_ne_cur hr
        simp only [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇,
          State.setReg_regs_ne _ _ hr_ne.1,
          State.setReg_regs_ne _ _ hr_ne.2.1,
          State.setReg_regs_ne _ _ hr_ne.2.2.1,
          State.setReg_regs_ne _ _ hr_ne.2.2.2.1,
          State.setReg_regs_ne _ _ hr_ne.2.2.2.2.1,
          State.setReg_regs_ne _ _ hr_ne.2.2.2.2.2.1,
          State.setReg_regs_ne _ _ hr_ne.2.2.2.2.2.2.1,
          State.setReg_regs_ne _ _ hr_ne.2.2.2.2.2.2.2]
        rw [hRegsMin r (sweep_reg_ne_min hr), hRegs₅ r (sweep_reg_ne_diff hr),
            hRegs₄ r (sweep_reg_ne_clean hr)]
        simp [s₃, s₂, s₁, hr_cur.2.1, hr_cur.2.2.1, hr_cur.2.2.2]
      · simp only [sweepStep, ← hst₁_def, hfirst, hMinEq, hlt_r, ↓reduceIte]
        refine ⟨by simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈, s₇],
          by simp [s₁₄],
          by simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉, s₈],
          by simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, s₉],
          by simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀],
          by simp [s₁₄, s₁₃, s₁₂, s₁₁],
          by simp [s₁₄, s₁₃, s₁₂],
          by simp [s₁₄, s₁₃]⟩
    · have hcondCross : (Expr.op .lt (.reg rMinR) (.reg rCurR)).eval w s₆ = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrMinR, hCurR₆, hJmin_r, hIr, hlt_r,
          show (0 : ℕ) < 2 ^ w by omega]
      rcases insertCandProg_exec cap I st₁ s₆ hw hcap ⟨hIl, hIr, hIγ⟩ hBlkW₁ hst₆
        (by omega) (by omega) hCurL₆ hCurR₆ hCurG₆ with
        ⟨s₇, tIns, hexIns, htIns, hst₇, hRegs₇, hArrs₇⟩
      have hrIdx₇ : s₇.regs rSweepIdx = i := by
        rw [hRegs₇ rSweepIdx ⟨by decide, by decide, by decide, by decide, by decide⟩]
        exact hrIdx₆
      let s₈ := s₇.setReg rSweepIdx (i + 1)
      have he8 : (Expr.op .add (.reg rSweepIdx) (.const 1)).eval w s₇ = some (i + 1) := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrIdx₇, hw,
          show i < 2 ^ w by omega, show i + 1 < 2 ^ w by omega]
      have hex : Exec w sweepStepProg s s₈ _ :=
        .seq (.assign he1) (.seq (.assign he2) (.seq (.assign he3)
          (.seq hexClean (.seq hexDiff
            (.ite_true hcondDiff (by dsimp [Expr.cost]; omega)
              (.seq hexMin
                (.ite_false hcondCross (.seq hexIns (.assign he8)))))))))
      have hArrs_lt120 : ∀ a < 120, s₈.arrs a = s.arrs a := by
        intro a ha
        simp only [s₈, State.setReg_arrs]
        rw [hArrs₇ a (sweep_arr_ne_2 ha), hArrsMin a, hArrs₅ a, hArrs₄ a (sweep_arr_ne_1 ha)]
        rfl
      have hrCnt₈ : s₈.regs rNumCand = s.regs rNumCand := by
        simp only [s₈, State.setReg_regs_ne _ _ (by decide : rNumCand ≠ rSweepIdx)]
        rw [hRegs₇ rNumCand ⟨by decide, by decide, by decide, by decide, by decide⟩, hrCnt₆, hrCnt]
      refine ⟨s₈, _, hex, by dsimp [Expr.cost]; omega, ?_, ?_, hArrs_lt120, ?_⟩
      · exact hCand.of_eq hrCnt₈ (hArrs_lt120 aCandL (by decide))
          (hArrs_lt120 aCandR (by decide)) (hArrs_lt120 aCandG (by decide))
      · intro r hr
        have hr_cur := sweep_reg_ne_cur hr
        simp only [s₈, State.setReg_regs_ne _ _ hr_cur.1]
        rw [hRegs₇ r (sweep_reg_ne_ins hr), hRegsMin r (sweep_reg_ne_min hr),
            hRegs₅ r (sweep_reg_ne_diff hr), hRegs₄ r (sweep_reg_ne_clean hr)]
        simp [s₃, s₂, s₁, hr_cur.2.1, hr_cur.2.2.1, hr_cur.2.2.2]
      · simp only [sweepStep, ← hst₁_def, hfirst, hMinEq, hlt_r, ↓reduceIte]
        refine ⟨?_, by simp [s₈],
          hst₇.setReg_other _ _ ⟨by decide, by decide⟩,
          le_trans (length_insertCandidate_le I st₁) (by omega),
          by rw [length_storedCandidates_insertCandidate]; omega, ?_⟩
        · simp only [s₈, State.setReg_regs_ne _ _ (by decide : rSweepFound ≠ rSweepIdx)]
          rw [hRegs₇ rSweepFound ⟨by decide, by decide, by decide, by decide, by decide⟩]
          exact hrFound₆
        · intro J hJ
          rcases (mem_storedCandidates_insertCandidate_iff I st₁ J).mp hJ with rfl | hJ₁
          · exact ⟨hIl, hIr, hIγ⟩
          · exact hItemsW₁ J hJ₁

/-- Execution of `sweepWhile` by induction on `d = sorted.length - i`. -/
private theorem sweepWhile_exec {w : ℕ} (cap i : ℕ) (sorted : List Candidate)
    (hi : i ≤ sorted.length) (st : List Block) (s : State)
    (hw : 1 < 2 ^ w) (hcap : cap < 2 ^ w)
    (hCand : IsCandArray sorted cap aCandL aCandR aCandG rNumCand s)
    (hrIdx : s.regs rSweepIdx = i)
    (hrFound : s.regs rSweepFound = 0)
    (hst : IsBlockStack cap st s)
    (hble : st.length ≤ i)
    (henle : (storedCandidates st).length ≤ i)
    (hInv : StackInv st)
    (hItemsW : ∀ J ∈ storedCandidates st, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w)
    (hSortedW : ∀ J ∈ sorted, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w)
    (hBound : BoundedActivePerColor sorted)
    (hpw : (sorted.drop i).Pairwise CandidateOrder)
    (hprev : ∀ J ∈ storedCandidates st, ∀ K ∈ sorted.drop i, J.l ≤ K.l)
    (hcnt : ∀ P : Candidate → Bool,
      ((storedCandidates st).filter P).length + ((sorted.drop i).filter P).length ≤
        (sorted.filter P).length) :
    ∃ s' t, Exec w sweepWhile s s' t ∧
      t ≤ 3 + 660 * (sorted.drop i).length + 85 * sweepRemovals st (sorted.drop i) ∧
      IsCandArray sorted cap aCandL aCandR aCandG rNumCand s' ∧
      (∀ r < 105, s'.regs r = s.regs r) ∧
      (∀ a < 120, s'.arrs a = s.arrs a) ∧
      match sweepLoop st (sorted.drop i) with
      | none => s'.regs rSweepFound = 0
      | some (J, I) =>
        s'.regs rSweepFound = 1 ∧
        s'.regs rOutI1L = J.l ∧ s'.regs rOutI1R = J.r ∧ s'.regs rOutI1G = J.γ ∧
        s'.regs rOutI2L = I.l ∧ s'.regs rOutI2R = I.r ∧ s'.regs rOutI2G = I.γ := by
  induction hd : sorted.length - i generalizing i st s with
  | zero =>
    have hieq : i = sorted.length := by omega
    subst hieq
    have hrCnt : s.regs rNumCand = sorted.length := hCand.1
    have hsorted_le : sorted.length ≤ cap := hCand.2.2.2.2.1
    have hcond : (Expr.op .lt (.reg rSweepIdx) (.reg rNumCand)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrIdx, hrCnt,
        show sorted.length < 2 ^ w by omega, show (0 : ℕ) < 2 ^ w by omega]
    refine ⟨s, 3, .while_false hcond, by simp, hCand, fun _ _ => rfl,
      fun _ _ => rfl, by simp [sweepLoop, hrFound]⟩
  | succ d ih =>
    have hilt : i < sorted.length := by omega
    have hrCnt : s.regs rNumCand = sorted.length := hCand.1
    have hsorted_le : sorted.length ≤ cap := hCand.2.2.2.2.1
    have hdrop_eq : sorted.drop i = sorted[i] :: sorted.drop (i + 1) := List.drop_eq_getElem_cons hilt
    set I := sorted[i]'hilt with hI_def
    have hcond : (Expr.op .lt (.reg rSweepIdx) (.reg rNumCand)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrIdx, hrCnt, hilt, hw,
        show i < 2 ^ w by omega, show sorted.length < 2 ^ w by omega]
    have hl_le : ∀ J ∈ storedCandidates st, J.l ≤ I.l := by
      intro J hJ
      apply hprev J hJ I
      rw [hdrop_eq]
      exact List.mem_cons_self
    have hcnt_st : ∀ P : Candidate → Bool,
        ((storedCandidates st).filter P).length ≤ (sorted.filter P).length := by
      intro P
      have := hcnt P
      omega
    have hSix : ∀ B' ∈ cleanStack I.l st, B'.items.length ≤ 6 :=
      block_length_le_six_of_boundedActive hBound hInv I.l hl_le hcnt_st
    rcases sweepStepProg_exec cap i sorted hilt st s hw hcap hCand hrIdx hrFound
      hst hble henle hInv hItemsW hSortedW hSix with
      ⟨s₁, t₁, hex₁, ht₁, hCand₁, hRegs₁, hArrs₁, hStepSpec⟩
    rw [← hI_def] at ht₁ hStepSpec
    have hspec := sweepStep_spec hInv I
    rw [hdrop_eq] at hpw hprev hcnt ⊢
    have hpw_cons := List.pairwise_cons.mp hpw
    cases hstep : sweepStep st I with
    | inr pair =>
      rcases pair with ⟨J, I'⟩
      rw [hstep] at hStepSpec
      rcases hStepSpec with ⟨hrFound₁, hrIdx₁, hOut1L, hOut1R, hOut1G, hOut2L, hOut2R, hOut2G⟩
      have hrCnt₁ : s₁.regs rNumCand = sorted.length := hCand₁.1
      have hcond₂ : (Expr.op .lt (.reg rSweepIdx) (.reg rNumCand)).eval w s₁ = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrIdx₁, hrCnt₁,
          show sorted.length < 2 ^ w by omega, show (0 : ℕ) < 2 ^ w by omega]
      refine ⟨s₁, _, .while_true hcond (by dsimp [Expr.cost]; omega) hex₁ (.while_false hcond₂),
        ?_, hCand₁, hRegs₁, hArrs₁, ?_⟩
      · simp only [sweepRemovals, hstep, List.length_cons, Expr.cost]
        omega
      · simp only [sweepLoop, hstep]
        exact ⟨hrFound₁, hOut1L, hOut1R, hOut1G, hOut2L, hOut2R, hOut2G⟩
    | inl st' =>
      rw [hstep] at hStepSpec hspec
      rcases hStepSpec with ⟨hrFound₁, hrIdx₁, hst₁, hble₁, henle₁, hItemsW₁⟩
      rcases hspec with ⟨hInv₁, hmem₁, _⟩
      have hst'_eq : st' = insertCandidate I (cleanStack I.l st) := by
        dsimp only [sweepStep] at hstep
        cases hfirst : firstDiffBlock I.γ (cleanStack I.l st) with
        | none => rw [hfirst] at hstep; exact Sum.inl.inj hstep.symm
        | some B =>
          rw [hfirst] at hstep; dsimp only at hstep
          cases hmin : minRightCandidate B.items with
          | none => rw [hmin] at hstep; exact Sum.inl.inj hstep.symm
          | some J =>
            rw [hmin] at hstep; dsimp only at hstep
            split_ifs at hstep
            exact Sum.inl.inj hstep.symm
      have hprev₁ : ∀ J ∈ storedCandidates st', ∀ K ∈ sorted.drop (i + 1), J.l ≤ K.l := by
        intro J hJ K hK
        rcases (hmem₁ J).mp hJ with rfl | ⟨hJ_st, _⟩
        · rcases hpw_cons.1 K hK with hlt | ⟨heq, _⟩ <;> omega
        · exact hprev J hJ_st K (List.mem_cons_of_mem I hK)
      have hcnt₁ : ∀ P : Candidate → Bool,
          ((storedCandidates st').filter P).length + ((sorted.drop (i + 1)).filter P).length ≤
            (sorted.filter P).length := by
        intro P
        have hperm := ((storedCandidates_insertCandidate_perm I (cleanStack I.l st)).filter P).length_eq
        have hsub := ((storedCandidates_cleanStack_sublist I.l st).filter P).length_le
        have hprev_cnt := hcnt P
        rw [hst'_eq, hperm]
        simp only [List.filter_cons] at hprev_cnt ⊢
        split_ifs at hprev_cnt ⊢ <;> simp at hprev_cnt ⊢ <;> omega
      rcases ih (i + 1) (by omega) st' s₁ hCand₁ hrIdx₁ hrFound₁ hst₁ hble₁ henle₁
        hInv₁ hItemsW₁ hpw_cons.2 hprev₁ hcnt₁ (by omega) with
        ⟨s₂, t₂, hex₂, ht₂, hCand₂, hRegs₂, hArrs₂, hLoopSpec⟩
      refine ⟨s₂, _, .while_true hcond (by dsimp [Expr.cost]; omega) hex₁ hex₂, ?_, hCand₂,
        fun r hr => (hRegs₂ r hr).trans (hRegs₁ r hr),
        fun a ha => (hArrs₂ a ha).trans (hArrs₁ a ha), ?_⟩
      · simp only [sweepRemovals, hstep, List.length_cons, Expr.cost]
        omega
      · simp only [sweepLoop, hstep]
        exact hLoopSpec

/-- Total-correctness specification of `sweepProg`: given
`IsCandArray sorted cap aCandL aCandR aCandG rNumCand s` and `s.regs rCandCap = cap`, computes
`sweepCandidates sorted` in `O(cap + sorted.length + 1)` Word RAM steps. -/
theorem sweepProg_exec {w : ℕ} (cap : ℕ) (sorted : List Candidate) (s : State)
    (hw : 1 < 2 ^ w) (hcap : cap < 2 ^ w)
    (hCand : IsCandArray sorted cap aCandL aCandR aCandG rNumCand s)
    (hrCap : s.regs rCandCap = cap)
    (hSortedW : ∀ J ∈ sorted, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w)
    (hpw : sorted.Pairwise CandidateOrder)
    (hBound : BoundedActivePerColor sorted) :
    ∃ s' t, Exec w sweepProg s s' t ∧
      t ≤ 30 + 6 * cap + 750 * sorted.length ∧
      IsCandArray sorted cap aCandL aCandR aCandG rNumCand s' ∧
      (∀ r < 105, s'.regs r = s.regs r) ∧
      (∀ a < 120, s'.arrs a = s.arrs a) ∧
      match sweepCandidates sorted with
      | none => s'.regs rSweepFound = 0
      | some (J, I) =>
        s'.regs rSweepFound = 1 ∧
        s'.regs rOutI1L = J.l ∧ s'.regs rOutI1R = J.r ∧ s'.regs rOutI1G = J.γ ∧
        s'.regs rOutI2L = I.l ∧ s'.regs rOutI2R = I.r ∧ s'.regs rOutI2G = I.γ := by
  let s₁ := s.setArr aBlkG (List.replicate cap 0)
  have ha1 : (Expr.reg rCandCap).eval w s = some cap := by
    simp [Expr.eval, hrCap, checkWord, hcap]
  let s₂ := s₁.setArr aBlkSt (List.replicate cap 0)
  have ha2 : (Expr.reg rCandCap).eval w s₁ = some cap := ha1
  let s₃ := s₂.setArr aBlkEn (List.replicate cap 0)
  have ha3 : (Expr.reg rCandCap).eval w s₂ = some cap := ha1
  let s₄ := s₃.setArr aItemL (List.replicate cap 0)
  have ha4 : (Expr.reg rCandCap).eval w s₃ = some cap := ha1
  let s₅ := s₄.setArr aItemR (List.replicate cap 0)
  have ha5 : (Expr.reg rCandCap).eval w s₄ = some cap := ha1
  let s₆ := s₅.setArr aItemG (List.replicate cap 0)
  have ha6 : (Expr.reg rCandCap).eval w s₅ = some cap := ha1
  have he0 : (Expr.const 0).eval w s₆ = some 0 := by
    simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega]
  let s₇ := s₆.setReg rBlkCnt 0
  let s₈ := s₇.setReg rItemCnt 0
  let s₉ := s₈.setReg rSweepIdx 0
  let s₁₀ := s₉.setReg rSweepFound 0
  have hst₀ : IsBlockStack cap [] s₁₀ := by
    refine ⟨by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁],
      by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂],
      by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃],
      by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄],
      by simp [s₁₀, s₉, s₈, s₇, s₆, s₅],
      by simp [s₁₀, s₉, s₈, s₇, s₆],
      by simp [s₁₀, s₉, s₈, s₇],
      by simp [s₁₀, s₉, s₈, storedCandidates],
      Nat.zero_le cap, Nat.zero_le cap, trivial⟩
  have hCand₁₀ : IsCandArray sorted cap aCandL aCandR aCandG rNumCand s₁₀ :=
    hCand.of_eq
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁])
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁])
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁])
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁])
  rcases sweepWhile_exec cap 0 sorted (Nat.zero_le _) [] s₁₀ hw hcap hCand₁₀
    (by simp [s₁₀, s₉])
    (by simp [s₁₀])
    hst₀ le_rfl le_rfl StackInv.nil (by simp [storedCandidates]) hSortedW hBound
    (by simpa using hpw) (by simp [storedCandidates]) (by simp [storedCandidates]) with
    ⟨s', tWhile, hexWhile, htWhile, hCand', hRegs', hArrs', hSpec⟩
  have hex : Exec w sweepProg s s' _ :=
    .seq (.alloc ha1) (.seq (.alloc ha2) (.seq (.alloc ha3)
    (.seq (.alloc ha4) (.seq (.alloc ha5) (.seq (.alloc ha6)
    (.seq (.assign he0) (.seq (.assign he0) (.seq (.assign he0)
    (.seq (.assign he0) hexWhile)))))))))
  have hrem_le : sweepRemovals [] sorted ≤ sorted.length := by
    have := sweepRemovals_le [] sorted
    simpa [storedCandidates] using this
  simp only [List.drop_zero] at htWhile hSpec
  refine ⟨s', _, hex, by dsimp [Expr.cost]; omega, hCand', ?_, ?_, hSpec⟩
  · intro r hr
    have hr_init := sweep_reg_ne_init hr
    rw [hRegs' r hr]
    simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
      hr_init.1, hr_init.2.1, hr_init.2.2.1, hr_init.2.2.2]
  · intro a ha
    have ha_ne := sweep_arr_ne_2 ha
    rw [hArrs' a ha]
    simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
      ha_ne.1, ha_ne.2.1, ha_ne.2.2.1, ha_ne.2.2.2.1, ha_ne.2.2.2.2.1, ha_ne.2.2.2.2.2]

private theorem filter_candsUpTo_active_length_le {n : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] (T : List (Fin n)) (bridges : List (BridgeData (Fin n)))
    (γ l₀ : ℕ) :
    ∀ k ≤ bridges.length,
      ((candsUpTo H T bridges k).filter
        (fun J => (J.γ == γ) && decide (J.l ≤ l₀ ∧ l₀ < J.r))).length ≤
        if γ < k then 6 else 0
  | 0, _ => by simp
  | k + 1, hk => by
    have hlt : k < bridges.length := by omega
    have ih := filter_candsUpTo_active_length_le H T bridges γ l₀ k (by omega)
    rw [candsUpTo_succ H T bridges hlt, List.filter_append, List.length_append]
    by_cases hγk : γ = k
    · subst hγk
      simp only [lt_self_iff_false, ↓reduceIte] at ih
      have hcongr :
          (candidatesOfIndices γ ((bridges[γ]'hlt).attachmentIndices H T)).filter
            (fun J => (J.γ == γ) && decide (J.l ≤ l₀ ∧ l₀ < J.r)) =
          (candidatesOfIndices γ ((bridges[γ]'hlt).attachmentIndices H T)).filter
            (fun J => decide (J.l ≤ l₀ ∧ l₀ < J.r)) := by
        apply List.filter_congr
        intro J hJ
        have hJγ : J.γ = γ := (mem_candidatesOfIndices_lt hJ).2.1
        simp [hJγ]
      rw [hcongr]
      have hsix := (bridges[γ]'hlt).length_active_candidates_le_six H T γ l₀
      simp only [Nat.lt_add_one, ↓reduceIte]
      omega
    · have hnil :
          (candidatesOfIndices k ((bridges[k]'hlt).attachmentIndices H T)).filter
            (fun J => (J.γ == γ) && decide (J.l ≤ l₀ ∧ l₀ < J.r)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro J hJ
        have hJγ : J.γ = k := (mem_candidatesOfIndices_lt hJ).2.1
        simp [hJγ, Ne.symm hγk]
      rw [hnil, List.length_nil, Nat.add_zero]
      have hiff : γ < k + 1 ↔ γ < k := by omega
      simpa [hiff] using ih

/-- Every sorted bridge-candidate list satisfies `BoundedActivePerColor`. -/
theorem boundedActivePerColor_sortCandidates_allBridgeCandidates {n : ℕ}
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (T : List (Fin n))
    (bridges : List (BridgeData (Fin n))) :
    BoundedActivePerColor (sortCandidates T.length (allBridgeCandidates H T bridges)) := by
  intro γ l₀
  let cs := allBridgeCandidates H T bridges
  have hcs_lt : ∀ I ∈ cs, I.l < T.length ∧ I.r < T.length := by
    intro I hI
    obtain ⟨_, hl_r, hr_lt, _, _⟩ := mem_allBridgeCandidates_spec H hI
    exact ⟨lt_trans hl_r hr_lt, hr_lt⟩
  have hperm := (sortCandidates_perm hcs_lt).filter
    (fun J => (J.γ == γ) && decide (J.l ≤ l₀ ∧ l₀ < J.r))
  rw [hperm.length_eq]
  dsimp only [cs]
  rw [← candsUpTo_length H T bridges]
  have hle := filter_candsUpTo_active_length_le H T bridges γ l₀ bridges.length le_rfl
  split_ifs at hle <;> omega

end GraphMinor.Compute
