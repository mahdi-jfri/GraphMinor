module

public import GraphMinor.Compute.CrossingClassAttachCount

/-!
# Filling bridge attachment lists

This file proves that the second attachment scan fills the lists in cycle order and
assembles the two scans and prefix sums that compute the attachment lists of Section 5.1 of
`docs/crossing/crossing_extractor.tex`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph GraphMinor.HP25 GraphMinor.Crossing GraphMinor.Compute.Crossing
  GraphMinor.Compute.TwoPaths
open scoped BigOperators

variable {n : ℕ}

/-! ### Part 7: Execution of Pass 2 (`attFillProg`) and `attachListsProg` -/

/-- State predicate for `(aAttSt, aAttEn, aAttEnt)` during Pass 2 at `(i, j)`. -/
structure AttFillCompOK (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (lists : Fin n → List ℕ)
    (T : List (Fin n)) (segs : List (List (Fin n))) (i j : ℕ) (s : State) : Prop where
  len_st :
    (s.arrs aAttSt).length = (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length
  len_en :
    (s.arrs aAttEn).length = (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length
  len_ent :
    (s.arrs aAttEnt).length =
      totalAttachments H T (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length))
  get_st : ∀ γ < (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length,
    (s.arrs aAttSt)[γ]? =
      some (attOffset H T (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)) γ)
  get_en : ∀ γ < segs.length,
    (s.arrs aAttEn)[γ]? =
      some (attOffset H T (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)) γ +
        (compAttAt H lists T segs i j γ).length)
  get_ent : ∀ (γ : ℕ) (_hγ : γ < segs.length) (k : ℕ)
    (hk : k < (compAttAt H lists T segs i j γ).length),
    (s.arrs aAttEnt)[attOffset H T (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)) γ + k]? =
      some ((compAttAt H lists T segs i j γ)[k]'hk)

theorem AttFillCompOK.of_arrs_eq {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    {lists : Fin n → List ℕ} {T : List (Fin n)} {segs : List (List (Fin n))}
    {i j : ℕ} {s s' : State}
    (h : AttFillCompOK H lists T segs i j s)
    (hst : s'.arrs aAttSt = s.arrs aAttSt)
    (hen : s'.arrs aAttEn = s.arrs aAttEn)
    (hent : s'.arrs aAttEnt = s.arrs aAttEnt) :
    AttFillCompOK H lists T segs i j s' where
  len_st := by rw [hst, h.len_st]
  len_en := by rw [hen, h.len_en]
  len_ent := by rw [hent, h.len_ent]
  get_st := fun γ hγ => by rw [hst]; exact h.get_st γ hγ
  get_en := fun γ hγ => by rw [hen]; exact h.get_en γ hγ
  get_ent := fun γ hγ k hk => by rw [hent]; exact h.get_ent γ hγ k hk

/-- Execution of `attFillBody` for one neighbour `y` of `T[i]`. -/
theorem attFillBody_exec {w : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lists : Fin n → List ℕ) (T : List (Fin n)) (hT : T.Nodup)
    (segs : List (List (Fin n))) (items : List ℕ)
    (s₀ : State) (hpre : ChordPre H lists T s₀)
    (hcomp : CompSegsOK H T segs items s₀)
    (hall : ∀ x : Fin n, x ∉ T → x.1 ∈ items)
    (hnw : 4 * (n + (s₀.arrs aEnt).length + 2) < 2 ^ w)
    (hM_le : totalAdjEntries lists ≤ (s₀.arrs aEnt).length)
    (i : ℕ) (hi : i < T.length) (j : ℕ) (hj : j < (lists (T[i]'hi)).length)
    (hyn : (lists (T[i]'hi))[j]'hj < n)
    (s : State) (hk : Keeps attachScanRegs attachArrs s₀ s)
    (hri : s.regs rI2 = i) (hrx : s.regs rX2 = (T[i]'hi).1)
    (hry : s.regs rY = (lists (T[i]'hi))[j]'hj)
    (hlast : LastAttOK lists T segs i j s)
    (hfill : AttFillCompOK H lists T segs i j s) :
    ∃ s' t, Exec w attFillBody s s' t ∧ t ≤ 38 ∧
      Keeps attachScanRegs attachArrs s₀ s' ∧
      s'.regs rI2 = i ∧ s'.regs rX2 = (T[i]'hi).1 ∧
      s'.regs rK2 = s.regs rK2 ∧ s'.regs rHi2 = s.regs rHi2 ∧
      LastAttOK lists T segs i (j + 1) s' ∧
      AttFillCompOK H lists T segs i (j + 1) s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  have hK_le_n : segs.length ≤ n := hcomp.segs_le_n
  set bridges := bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)
  have htot_le : totalAttachments H T bridges ≤ totalAdjEntries lists :=
    totalAttachments_bridgesOfSegsAndChords_le hpre.adj.2 hT hcomp hall
  set y : Fin n := ⟨(lists (T[i]'hi))[j]'hj, hyn⟩
  have hyw : y.1 < 2 ^ w := by omega
  have hpos_s : s.arrs aPos = posArr T := by rw [hk.2 aPos (by decide)]; exact hpre.pos
  obtain ⟨q, hq⟩ : ∃ q, (if y ∈ T then T.idxOf y + 1 else 0) = q := ⟨_, rfl⟩
  have hqk : q ≤ T.length := by
    rw [← hq]; split_ifs with h
    · exact pos_le h
    · omega
  have hqw : q < 2 ^ w := by omega
  have hread_q : (Expr.read aPos (.reg rY)).eval w s = some q :=
    read_reg_eval hry hyw (by simp [hpos_s, posArr, y.2, hq, y]) hqw
  set s₁ := s.setReg rQ q
  have hex₁ : Exec w (.assign rQ (.read aPos (.reg rY))) s s₁ 3 := .assign hread_q
  have hk₁ : Keeps attachScanRegs attachArrs s₀ s₁ := hk.setReg (by simp [attachScanRegs]) _
  by_cases hyT : y ∈ T
  · have hq_pos : 0 < q := by simp [← hq, hyT]
    have hcond_q : (Expr.op .eq (.reg rQ) (.const 0)).eval w s₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hqw,
        show q ≠ 0 by omega]
    have hex : Exec w attFillBody s s₁ (3 + (3 + 1)) :=
      .seq hex₁ (.ite_false hcond_q (.skip _))
    refine ⟨s₁, _, hex, by omega, hk₁, by simp [s₁, hri], by simp [s₁, hrx],
      by simp [s₁], by simp [s₁],
      (hlast.step_mem_T hcomp hi hj hyn hyT).of_arrs_eq (by simp [s₁]), ?_⟩
    have hcomp_eq : ∀ γ, compAttAt H lists T segs i (j + 1) γ = compAttAt H lists T segs i j γ := by
      intro γ
      simp [compAttAt, seenAt_succ_of_mem_T hcomp hi hj hyn hyT γ]
    refine ⟨by simp [s₁, hfill.len_st], by simp [s₁, hfill.len_en], by simp [s₁, hfill.len_ent],
      fun γ hγ => by simpa [s₁] using hfill.get_st γ hγ,
      fun γ hγ => by simpa [s₁, hcomp_eq γ] using hfill.get_en γ hγ,
      fun γ hγ k hk => ?_⟩
    simp only [hcomp_eq γ] at hk ⊢
    simpa [s₁] using hfill.get_ent γ hγ k hk
  · have hq0 : q = 0 := by simp [← hq, hyT]
    have hcond_q : (Expr.op .eq (.reg rQ) (.const 0)).eval w s₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hq0, hw1]
    obtain ⟨γ₀, hγ₀, _, hy_seg₀, huniq⟩ := hcomp.compOf_spec hall hyT
    have hcomp_s₁ : CompSegsOK H T segs items s₁ :=
      hcomp.of_state (by rw [hk₁.1 _ (by decide)]) (by rw [hk₁.2 _ (by decide)])
        (by rw [hk₁.2 _ (by decide)]) (by rw [hk₁.2 _ (by decide)])
    have hγ₀_w : γ₀ < 2 ^ w := by omega
    have hread_g : (Expr.read aCompOf (.reg rY)).eval w s₁ = some γ₀ :=
      read_reg_eval (by simp [s₁, hry, y]) hyw (hcomp_s₁.compOf_eq γ₀ hγ₀ y hy_seg₀) hγ₀_w
    set s₂ := s₁.setReg rG γ₀
    have hex₂ : Exec w (.assign rG (.read aCompOf (.reg rY))) s₁ s₂ 3 := .assign hread_g
    have hk₂ : Keeps attachScanRegs attachArrs s₀ s₂ := hk₁.setReg (by simp [attachScanRegs]) _
    have hseen_step := seenAt_succ_of_not_mem_T lists T segs hi hj hyn hγ₀ hy_seg₀ huniq
    have hlast_γ₀ := hlast.2 γ₀ hγ₀
    by_cases hseen : seenAt lists T segs i j γ₀ = true
    · simp only [hseen, ↓reduceIte] at hlast_γ₀
      have hread_last : (Expr.read aLastAtt (.reg rG)).eval w s₂ = some (i + 1) :=
        read_reg_eval (by simp [s₂]) hγ₀_w (by simpa [s₂, s₁] using hlast_γ₀) (by omega)
      set s₃ := s₂.setReg rTmp1 (i + 1)
      have hex₃ : Exec w (.assign rTmp1 (.read aLastAtt (.reg rG))) s₂ s₃ 3 := .assign hread_last
      have hk₃ : Keeps attachScanRegs attachArrs s₀ s₃ := hk₂.setReg (by simp [attachScanRegs]) _
      have hcond_sub : (Expr.op .sub (.op .add (.reg rI2) (.const 1)) (.reg rTmp1)).eval w s₃ =
          some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hri, hw1,
          show i < 2 ^ w by omega, show i + 1 < 2 ^ w by omega]
      have hex : Exec w attFillBody s s₃ (3 + (3 + (3 + (3 + (5 + 1))))) :=
        .seq hex₁ (.ite_true hcond_q one_ne_zero
          (.seq hex₂ (.seq hex₃ (.ite_false hcond_sub (.skip _)))))
      have hcomp_eq : ∀ γ < segs.length,
          compAttAt H lists T segs i (j + 1) γ = compAttAt H lists T segs i j γ := by
        intro γ hγ
        by_cases hγ_eq : γ = γ₀
        · subst hγ_eq; simp [compAttAt, hγ, hseen, hseen_step.1]
        · simp [compAttAt, hγ, hseen_step.2 γ hγ hγ_eq]
      refine ⟨s₃, _, hex, by omega, hk₃, by simp [s₃, s₂, s₁, hri], by simp [s₃, s₂, s₁, hrx],
        by simp [s₃, s₂, s₁], by simp [s₃, s₂, s₁], ?_, ?_⟩
      · refine ⟨by simp [s₃, s₂, s₁, hlast.1], fun γ hγ => ?_⟩
        simp only [State.setReg_arrs, s₃, s₂, s₁]
        by_cases hγ_eq : γ = γ₀
        · subst hγ_eq; simp [hseen_step.1, hlast_γ₀]
        · rw [hseen_step.2 γ hγ hγ_eq]; exact hlast.2 γ hγ
      · refine ⟨by simp [s₃, s₂, s₁, hfill.len_st], by simp [s₃, s₂, s₁, hfill.len_en],
          by simp [s₃, s₂, s₁, hfill.len_ent],
          fun γ hγ => by simpa [s₃, s₂, s₁] using hfill.get_st γ hγ,
          fun γ hγ => by simpa [s₃, s₂, s₁, hcomp_eq γ hγ] using hfill.get_en γ hγ,
          fun γ hγ k hk => ?_⟩
        simp only [hcomp_eq γ hγ] at hk ⊢
        simpa [s₃, s₂, s₁] using hfill.get_ent γ hγ k hk
    · simp only [hseen, Bool.false_eq_true, ↓reduceIte] at hlast_γ₀
      obtain ⟨l, hl_le, hlast_l⟩ := hlast_γ₀
      have hread_last : (Expr.read aLastAtt (.reg rG)).eval w s₂ = some l :=
        read_reg_eval (by simp [s₂]) hγ₀_w (by simpa [s₂, s₁] using hlast_l) (by omega)
      set s₃ := s₂.setReg rTmp1 l
      have hex₃ : Exec w (.assign rTmp1 (.read aLastAtt (.reg rG))) s₂ s₃ 3 := .assign hread_last
      have hcond_sub : (Expr.op .sub (.op .add (.reg rI2) (.const 1)) (.reg rTmp1)).eval w s₃ =
          some (i + 1 - l) := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hri, hw1,
          show i < 2 ^ w by omega, show i + 1 < 2 ^ w by omega,
          show l < 2 ^ w by omega, show i + 1 - l < 2 ^ w by omega]
      set s₄ := s₃.writeArr aLastAtt γ₀ (i + 1)
      have hex₄ : Exec w (.write aLastAtt (.reg rG) (.op .add (.reg rI2) (.const 1))) s₃ s₄ 5 :=
        .write (reg_eval (by simp [s₃, s₂]) hγ₀_w)
          (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hri, hw1,
            show i < 2 ^ w by omega, show i + 1 < 2 ^ w by omega])
          (by simp [s₃, s₂, s₁, hlast.1, hγ₀])
      have hγ₀_B : γ₀ < bridges.length := by
        simp [bridges, bridgesOfSegsAndChords, chordBridgesOfPairs]; omega
      set l₀ := compAttAt H lists T segs i j γ₀
      set st₀ := attOffset H T bridges γ₀
      set cur := st₀ + l₀.length
      have hl₀_next : compAttAt H lists T segs i (j + 1) γ₀ = l₀ ++ [i] := by
        simp [l₀, compAttAt, hγ₀, hseen, hseen_step.1]
      have hl₀_lt_att : l₀.length < ((bridges[γ₀]'hγ₀_B).attachmentIndices H T).length := by
        rw [bridgesOfSegsAndChords_comp_attachmentIndices H T segs _ hγ₀]
        have hle_next := length_compAttAt_le_attachmentIndices (j := j + 1) hpre.adj.2 T segs hi
          (by omega) hγ₀
        rw [hl₀_next, List.length_append, List.length_singleton] at hle_next
        omega
      have hcur_lt_tot : cur < totalAttachments H T bridges := by
        have hle_off := attOffset_mono H T bridges (γ₁ := γ₀ + 1) (γ₂ := bridges.length)
          (by omega) le_rfl
        rw [attOffset_succ H T bridges hγ₀_B, attOffset_length H T bridges] at hle_off
        omega
      have hcur_w : cur < 2 ^ w := by omega
      have hγ₀_en : γ₀ < (s₄.arrs aAttEn).length := by
        simp [s₄, s₃, s₂, s₁, hfill.len_en]; exact hγ₀_B
      have hread_cur : (Expr.read aAttEn (.reg rG)).eval w s₄ = some cur :=
        read_reg_eval (by simp [s₄, s₃, s₂]) hγ₀_w
          (by simpa [s₄, s₃, s₂, s₁, cur, st₀, l₀, bridges] using hfill.get_en γ₀ hγ₀) hcur_w
      set s₅ := s₄.setReg rCur cur
      have hex₅ : Exec w (.assign rCur (.read aAttEn (.reg rG))) s₄ s₅ 3 := .assign hread_cur
      set s₆ := s₅.writeArr aAttEnt cur i
      have hex₆ : Exec w (.write aAttEnt (.reg rCur) (.reg rI2)) s₅ s₆ 3 :=
        .write (reg_eval (by simp [s₅]) hcur_w)
          (reg_eval (by simp [s₅, s₄, s₃, s₂, s₁, hri]) (by omega))
          (by simp [s₅, s₄, s₃, s₂, s₁, hfill.len_ent]; exact hcur_lt_tot)
      set s₇ := s₆.writeArr aAttEn γ₀ (cur + 1)
      have hex₇ : Exec w (.write aAttEn (.reg rG) (.op .add (.reg rCur) (.const 1))) s₆ s₇ 5 :=
        .write (reg_eval (by simp [s₆, s₅, s₄, s₃, s₂]) hγ₀_w)
          (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₆, s₅, hcur_w, hw1,
            show cur + 1 < 2 ^ w by omega])
          (by simp [s₆, s₅, hγ₀_en])
      have hex : Exec w attFillBody s s₇ (3 + (3 + (3 + (3 + (5 + (5 + (3 + (3 + 5)))))))) :=
        .seq hex₁ (.ite_true hcond_q one_ne_zero
          (.seq hex₂ (.seq hex₃ (.ite_true hcond_sub (by omega)
            (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))))
      have hk₇ : Keeps attachScanRegs attachArrs s₀ s₇ :=
        (((((hk₂.setReg (by simp [attachScanRegs]) _).writeArr (by simp [attachArrs]) _ _).setReg
          (by simp [attachScanRegs]) _).writeArr (by simp [attachArrs]) _ _).writeArr
          (by simp [attachArrs]) _ _)
      refine ⟨s₇, _, hex, by omega, hk₇,
        by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hri], by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hrx],
        by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁], by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁], ?_, ?_⟩
      · refine ⟨by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hlast.1], fun γ hγ => ?_⟩
        simp only [s₇, s₆, s₅, s₄, s₃, s₂, s₁,
          State.writeArr_arrs_ne _ _ _ (by decide : aLastAtt ≠ aAttEn),
          State.writeArr_arrs_ne _ _ _ (by decide : aLastAtt ≠ aAttEnt),
          State.setReg_arrs, State.writeArr_arrs_self]
        by_cases hγ_eq : γ = γ₀
        · subst hγ_eq
          simp only [hseen_step.1, ↓reduceIte]
          have hlt_l : γ < (s.arrs aLastAtt).length := by rw [hlast.1]; exact hγ
          exact List.getElem?_set_self hlt_l
        · rw [hseen_step.2 γ hγ hγ_eq, List.getElem?_set_ne (Ne.symm hγ_eq)]
          exact hlast.2 γ hγ
      · refine ⟨by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hfill.len_st],
          by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hfill.len_en],
          by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hfill.len_ent],
          fun γ hγ => by simpa [s₇, s₆, s₅, s₄, s₃, s₂, s₁] using hfill.get_st γ hγ,
          fun γ hγ => ?_, fun γ hγ k hk => ?_⟩
        · simp only [s₇, State.writeArr_arrs_self, s₆,
            State.writeArr_arrs_ne _ _ _ (by decide : aAttEn ≠ aAttEnt),
            State.setReg_arrs, s₅, s₄,
            State.writeArr_arrs_ne _ _ _ (by decide : aAttEn ≠ aLastAtt), s₃, s₂, s₁]
          by_cases hγ_eq : γ = γ₀
          · subst hγ_eq
            have hlt_e : γ < (s.arrs aAttEn).length := by rw [hfill.len_en]; exact hγ₀_B
            rw [List.getElem?_set_self hlt_e, hl₀_next]
            simp [cur, st₀, l₀, bridges, Nat.add_assoc]
          · rw [List.getElem?_set_ne (Ne.symm hγ_eq),
              compAttAt_congr_seenAt H lists T segs (hseen_step.2 γ hγ hγ_eq)]
            exact hfill.get_en γ hγ
        · simp only [s₇, State.writeArr_arrs_ne _ _ _ (by decide : aAttEnt ≠ aAttEn),
            s₆, State.writeArr_arrs_self, State.setReg_arrs, s₅, s₄,
            State.writeArr_arrs_ne _ _ _ (by decide : aAttEnt ≠ aLastAtt), s₃, s₂, s₁]
          by_cases hγ_eq : γ = γ₀
          · subst hγ_eq
            simp only [hl₀_next, List.length_append, List.length_singleton] at hk ⊢
            rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt_k | rfl
            · have hne_c : cur ≠ attOffset H T bridges γ + k := by
                simp only [cur, st₀, bridges]; omega
              rw [List.getElem?_set_ne hne_c, List.getElem_append_left hlt_k]
              exact hfill.get_ent γ hγ k hlt_k
            · have hlt_ent : cur < (s.arrs aAttEnt).length := by
                rw [hfill.len_ent]; exact hcur_lt_tot
              change ((s.arrs aAttEnt).set cur i)[cur]? = some (l₀ ++ [i])[l₀.length]
              rw [List.getElem?_set_self hlt_ent]
              simp
          · have hcomp_eq : compAttAt H lists T segs i (j + 1) γ = compAttAt H lists T segs i j γ := by
              simp [compAttAt, hγ, hseen_step.2 γ hγ hγ_eq]
            simp only [hcomp_eq] at hk ⊢
            have hγ_B : γ < bridges.length := by
              simp [bridges, bridgesOfSegsAndChords, chordBridgesOfPairs]; omega
            have hk_att : k < ((bridges[γ]'hγ_B).attachmentIndices H T).length := by
              rw [bridgesOfSegsAndChords_comp_attachmentIndices H T segs _ hγ]
              exact lt_of_lt_of_le hk
                (length_compAttAt_le_attachmentIndices (j := j) hpre.adj.2 T segs hi (by omega) hγ)
            have hne_c : cur ≠ attOffset H T bridges γ + k :=
              attOffset_disjoint H T bridges hγ₀_B hγ_B (Ne.symm hγ_eq) hl₀_lt_att hk_att
            rw [List.getElem?_set_ne hne_c]
            exact hfill.get_ent γ hγ k hk

/-- Execution of `attFillOuter` for cycle index `i < T.length`. -/
theorem attFillOuter_exec {w : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lists : Fin n → List ℕ) (T : List (Fin n)) (hT : T.Nodup)
    (segs : List (List (Fin n))) (items : List ℕ)
    (s₀ : State) (hpre : ChordPre H lists T s₀) (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (hcomp : CompSegsOK H T segs items s₀)
    (hall : ∀ x : Fin n, x ∉ T → x.1 ∈ items)
    (hnw : 4 * (n + (s₀.arrs aEnt).length + 2) < 2 ^ w)
    (hM_le : totalAdjEntries lists ≤ (s₀.arrs aEnt).length)
    (i : ℕ) (hi : i < T.length)
    (s : State) (hk : Keeps attachScanRegs attachArrs s₀ s)
    (hri : s.regs rI2 = i)
    (hlast : LastAttOK lists T segs i 0 s)
    (hfill : AttFillCompOK H lists T segs i 0 s) :
    ∃ s' t, Exec w attFillOuter s s' t ∧
      t ≤ 12 + 48 * (lists T[i]).length ∧
      Keeps attachScanRegs attachArrs s₀ s' ∧
      s'.regs rI2 = i ∧
      LastAttOK lists T segs (i + 1) 0 s' ∧
      AttFillCompOK H lists T segs (i + 1) 0 s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  set x := T[i] with hx
  have hxw : x.1 < 2 ^ w := by have := x.2; omega
  have hcyc_s : s.arrs aCyc = T.map Fin.val := by
    rw [hk.2 aCyc (by decide)]; exact hpre.cyc
  have hread : (Expr.read aCyc (.reg rI2)).eval w s = some x.1 :=
    read_reg_eval hri (by omega) (by simp [hcyc_s, hi, x]) hxw
  set s₁ := s.setReg rX2 x.1
  have hex₁ : Exec w (.assign rX2 (.read aCyc (.reg rI2))) s s₁ 3 := .assign hread
  have hk₁ : Keeps attachScanRegs attachArrs s₀ s₁ := hk.setReg (by simp [attachScanRegs]) _
  obtain ⟨st, en, hlist₀⟩ := hpre.adj.1.2.2 x
  obtain ⟨hmem_lt, -, -, _⟩ := hpre.adj.2 x
  have hlistOf : ∀ st' : State, Keeps attachScanRegs attachArrs s₀ st' →
      IsListAt aStart aEnd aEnt x.1 st en (lists x) st' := fun st' hk' =>
    hlist₀.of_arrs_eq (hk'.2 _ (by decide)) (hk'.2 _ (by decide)) (hk'.2 _ (by decide))
  have hen_w : en < 2 ^ w := by obtain ⟨_, _, hle, _⟩ := hlist₀; omega
  let II : ℕ → State → Prop := fun j st' =>
    Keeps attachScanRegs attachArrs s₀ st' ∧
    st'.regs rI2 = i ∧
    st'.regs rX2 = x.1 ∧
    LastAttOK lists T segs i j st' ∧
    AttFillCompOK H lists T segs i j st'
  have hI0 : II 0 s₁ :=
    ⟨hk₁, by simp [s₁, hri], by simp [s₁], hlast.of_arrs_eq (by simp [s₁]),
      hfill.of_arrs_eq (by simp [s₁]) (by simp [s₁]) (by simp [s₁])⟩
  have hinit : ∀ st', II 0 st' → IsListAt aStart aEnd aEnt x.1 st en (lists x) st' ∧
      st'.regs rX2 = x.1 ∧ II 0 ((st'.setReg rK2 st).setReg rHi2 en) := by
    intro st' ⟨hk', hri', hrx', hl', hf'⟩
    refine ⟨hlistOf st' hk', hrx',
      (hk'.setReg (by simp [attachScanRegs]) st).setReg (by simp [attachScanRegs]) en,
      by simp [hri'], by simp [hrx'], hl'.of_arrs_eq (by simp),
      hf'.of_arrs_eq (by simp) (by simp) (by simp)⟩
  have hfor := Triple.forList_const aStart aEnd aEnt rX2 rK2 rHi2 rY x.1 st en (lists x) II 38
    attFillBody (by decide) (by decide) hw1 hxw hen_w
    (fun z hz => by have := hmem_lt z hz; omega) hinit
    (fun j _ st' hst' => hlistOf st' hst'.1)
    (fun j hj sv ⟨st', ⟨hk', hri', hrx', hl', hf'⟩, hsv, hrk, hrhi⟩ => by
      subst hsv
      have hyn : (lists x)[j] < n := hmem_lt _ (List.getElem_mem hj)
      obtain ⟨s', t, hex, ht, hk'', hri'', hrx'', hrk'', hrhi'', hl'', hf''⟩ :=
        attFillBody_exec H lists T hT segs items s₀ hpre hcomp hall hnw hM_le i hi j hj hyn
          (st'.setReg rY (lists x)[j]) (hk'.setReg (by simp [attachScanRegs]) _)
          (by simp [hri']) (by simp [hrx', hx]) (by simp [hx])
          (hl'.of_arrs_eq (by simp)) (hf'.of_arrs_eq (by simp) (by simp) (by simp))
      refine ⟨s', t, hex, ht,
        ⟨hk''.setReg (by simp [attachScanRegs]) _, by simp [hri''], by simp [hrx'', hx],
         hl''.of_arrs_eq (by simp), hf''.of_arrs_eq (by simp) (by simp) (by simp)⟩,
        by rw [hrk'']; simpa using hrk, by rw [hrhi'']; simpa using hrhi⟩)
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hri₂, -, hl₂, hf₂⟩ := hfor s₁ hI0
  have hl₂' : LastAttOK lists T segs i (lists (T[i]'hi)).length s₂ := hl₂
  refine ⟨s₂, _, .seq hex₁ hex₂, by dsimp only at ht₂; omega, hk₂, hri₂,
    hl₂'.end_inner hi, ?_⟩
  refine ⟨hf₂.len_st, hf₂.len_en, hf₂.len_ent, hf₂.get_st, fun γ hγ => ?_, fun γ hγ k hk => ?_⟩
  · rw [← compAttAt_length hpre.adj.2 T segs hi γ]
    exact hf₂.get_en γ hγ
  · simp only [← compAttAt_length hpre.adj.2 T segs hi γ] at hk ⊢
    exact hf₂.get_ent γ hγ k hk

set_option maxHeartbeats 400000 in
/-- **Execution of Pass 2 (`attFillProg`).** Populates `(aAttSt, aAttEn, aAttEnt)` so that
`IsListFamily bridges.length aAttSt aAttEn aAttEnt (fun γ => bridges[γ.1].attachmentIndices H T)`
holds. -/
theorem attFillProg_exec {w : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lists : Fin n → List ℕ) (T : List (Fin n)) (hT : T.Nodup)
    (segs : List (List (Fin n))) (items : List ℕ)
    (s₀ : State) (hpre : ChordPre H lists T s₀) (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (hcomp : CompSegsOK H T segs items s₀)
    (hall : ∀ x : Fin n, x ∉ T → x.1 ∈ items)
    (hch : ChordsArrOK (s₀.arrs aEnt).length (chordsUpTo lists T T.length) s₀)
    (hnw : 4 * (n + (s₀.arrs aEnt).length + 2) < 2 ^ w)
    (hM_le : totalAdjEntries lists ≤ (s₀.arrs aEnt).length)
    (hlen_st₀ : (s₀.arrs aAttSt).length =
      (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length)
    (hlen_en₀ : (s₀.arrs aAttEn).length =
      (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length)
    (hlen_ent₀ : (s₀.arrs aAttEnt).length =
      totalAttachments H T (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)))
    (hget_st₀ : ∀ γ < (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length,
      (s₀.arrs aAttSt)[γ]? =
        some (attOffset H T (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)) γ))
    (hget_en₀ : ∀ γ < (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length,
      (s₀.arrs aAttEn)[γ]? =
        some (attOffset H T (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)) γ)) :
    ∃ s' t, Exec w attFillProg s₀ s' t ∧
      t ≤ 15 + n + 19 * T.length + 34 * (s₀.arrs aEnt).length + 48 * totalAdjEntries lists ∧
      Keeps attachScanRegs attachArrs s₀ s' ∧
      (s'.arrs aAttEnt).length =
        totalAttachments H T (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)) ∧
      IsListFamily (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length
        aAttSt aAttEn aAttEnt
        (fun γ : Fin (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length =>
          ((bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length))[γ.1]'γ.2).attachmentIndices H T)
        s' := by
  set bridges := bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  have htot_le : totalAttachments H T bridges ≤ totalAdjEntries lists :=
    totalAttachments_bridgesOfSegsAndChords_le hpre.adj.2 hT hcomp hall
  set K := segs.length
  set chordPairs := chordsUpTo lists T T.length
  set M_ch := chordPairs.length
  set B := K + M_ch
  have hB_eq : bridges.length = B := by
    simp [bridges, bridgesOfSegsAndChords, chordBridgesOfPairs, B, K, M_ch, chordPairs]
  have hK_le_n : K ≤ n := hcomp.segs_le_n
  have hM_le_ent : M_ch ≤ (s₀.arrs aEnt).length := hch.pairs_le_M
  have hB_w : B < 2 ^ w := by omega
  have hK_w : K < 2 ^ w := by omega
  have hM_w : M_ch < 2 ^ w := by omega
  set s₁ := s₀.setArr aLastAtt (List.replicate K 0)
  have hex₁ : Exec w (.alloc aLastAtt (.reg rNumComp)) s₀ s₁ (1 + K) :=
    .alloc (reg_eval hcomp.numComp hK_w)
  set s₂ := s₁.setReg rI2 0
  have hex₂ : Exec w (.assign rI2 (.const 0)) s₁ s₂ 2 := .assign (by simp [checkWord])
  let OI : ℕ → State → Prop := fun i st =>
    Keeps attachScanRegs attachArrs s₀ st ∧
    st.regs rI2 = i ∧
    LastAttOK lists T segs i 0 st ∧
    AttFillCompOK H lists T segs i 0 st
  have hOI0 : OI 0 s₂ := by
    refine ⟨((Keeps.refl _ _ s₀).setArr (by simp [attachArrs]) _).setReg
      (by simp [attachScanRegs]) _, by simp [s₂],
      LastAttOK.init lists T segs (by simp [s₂, s₁, K]),
      ⟨by rw [State.setReg_arrs, State.setArr_arrs_ne _ _ (by decide), hlen_st₀],
       by rw [State.setReg_arrs, State.setArr_arrs_ne _ _ (by decide), hlen_en₀],
       by rw [State.setReg_arrs, State.setArr_arrs_ne _ _ (by decide), hlen_ent₀],
       fun γ hγ => by simpa [s₂, s₁] using hget_st₀ γ hγ,
       fun γ hγ => ?_, fun _ _ _ hk => by simp [compAttAt_zero_zero] at hk⟩⟩
    have hγ_B : γ < bridges.length := by rw [hB_eq]; omega
    simpa [s₂, s₁, compAttAt_zero_zero] using hget_en₀ γ hγ_B
  have hloop₁ := Triple.forUp_sum OI T.length
    (fun i => 12 + 48 * degOf lists ((T.map Fin.val).getD i 0))
    (r_i := rI2) (hi := .reg rk) (body := attFillOuter) hw1 (by omega)
    (fun i _ st hst => ⟨hst.2.1, reg_eval (by rw [hst.1.1 rk (by decide), hpre.k]) (by omega)⟩)
    (fun i hi st ⟨hk, hri, hlast, hfill⟩ => by
      obtain ⟨s', t, hex, ht, hk', hri', hlast', hfill'⟩ :=
        attFillOuter_exec H lists T hT segs items s₀ hpre hent hcomp hall hnw hM_le
          i hi st hk hri hlast hfill
      refine ⟨s', t, hex, ?_,
        ⟨hk'.setReg (by simp [attachScanRegs]) _, by simp,
         hlast'.of_arrs_eq (by simp), hfill'.of_arrs_eq (by simp) (by simp) (by simp)⟩,
        hri'⟩
      have hd : degOf lists ((T.map Fin.val).getD i 0) = (lists T[i]).length := by
        simp [degOf, List.getD_eq_getElem?_getD, hi]
      show t ≤ 12 + 48 * degOf lists ((T.map Fin.val).getD i 0)
      rw [hd]; exact ht)
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, -, -, hfill₃⟩ := hloop₁ s₂ hOI0
  set s₄ := s₃.setReg rM 0
  have hex₄ : Exec w (.assign rM (.const 0)) s₃ s₄ 2 := .assign (by simp [checkWord])
  let CI : ℕ → State → Prop := fun m st =>
    Keeps attachScanRegs attachArrs s₀ st ∧
    st.regs rM = m ∧
    (st.arrs aAttSt).length = bridges.length ∧
    (st.arrs aAttEn).length = bridges.length ∧
    (st.arrs aAttEnt).length = totalAttachments H T bridges ∧
    (∀ γ < bridges.length, (st.arrs aAttSt)[γ]? = some (attOffset H T bridges γ)) ∧
    (∀ (γ : ℕ) (hγ : γ < K + m) (hγ_B : γ < bridges.length),
      (st.arrs aAttEn)[γ]? =
        some (attOffset H T bridges γ + ((bridges[γ]'hγ_B).attachmentIndices H T).length) ∧
      ∀ (k : ℕ) (hk : k < ((bridges[γ]'hγ_B).attachmentIndices H T).length),
        (st.arrs aAttEnt)[attOffset H T bridges γ + k]? =
          some (((bridges[γ]'hγ_B).attachmentIndices H T)[k]'hk))
  have hCI0 : CI 0 s₄ := by
    refine ⟨hk₃.setReg (by simp [attachScanRegs]) _, by simp [s₄],
      by simp [s₄, hfill₃.len_st, bridges], by simp [s₄, hfill₃.len_en, bridges],
      by simp [s₄, hfill₃.len_ent, bridges],
      fun γ hγ => by simpa [s₄, bridges] using hfill₃.get_st γ hγ,
      fun γ hγ hγ_B => ?_⟩
    have hγ_K : γ < K := by omega
    have hatt_eq : (bridges[γ]'hγ_B).attachmentIndices H T = compAttAt H lists T segs T.length 0 γ := by
      rw [compAttAt_end H lists T segs hγ_K]
      exact bridgesOfSegsAndChords_comp_attachmentIndices H T segs chordPairs hγ_K
    refine ⟨?_, fun k hk => ?_⟩
    · rw [hatt_eq]; simpa [s₄, bridges] using hfill₃.get_en γ hγ_K
    · simp only [hatt_eq] at hk ⊢
      simpa [s₄, bridges] using hfill₃.get_ent γ hγ_K k hk
  have hloop₂ := forUp_pot CI (fun _ => 0) M_ch 26
    (r_i := rM) (hi := .reg rNumChords) (body := attFillChordBody) hw1 hM_w
    (fun m _ st hst => ⟨hst.2.1,
      reg_eval (by rw [hst.1.1 rNumChords (by decide)]; exact hch.numChords) hM_w⟩)
    (fun m hm st ⟨hk, hrm, hlen_st, hlen_en, hlen_ent, hget_st, hdone⟩ => by
      set γ₀ := K + m
      have hγ₀_B : γ₀ < bridges.length := by rw [hB_eq]; omega
      have hγ₀_w : γ₀ < 2 ^ w := by omega
      have hrK : st.regs rNumComp = K := by
        rw [hk.1 rNumComp (by decide)]; exact hcomp.numComp
      obtain ⟨hi_m, hj_m, hij_m, _, _⟩ := (mem_chordsUpTo_iff hpre.adj.2 hT).mp (List.getElem_mem hm)
      have hatt_m : (bridges[γ₀]'hγ₀_B).attachmentIndices H T = [chordPairs[m].1, chordPairs[m].2] :=
        bridgesOfSegsAndChords_chord_attachmentIndices hpre.adj.2 hT segs hm
      have hatt_len_m : ((bridges[γ₀]'hγ₀_B).attachmentIndices H T).length = 2 := by
        rw [hatt_m]; rfl
      set cur := attOffset H T bridges γ₀
      have hcur2_le : cur + 2 ≤ totalAttachments H T bridges := by
        have hle := attOffset_mono H T bridges (γ₁ := γ₀ + 1) (γ₂ := bridges.length) (by omega) le_rfl
        rw [attOffset_succ H T bridges hγ₀_B, hatt_len_m, attOffset_length H T bridges] at hle
        exact hle
      have hcur_w : cur < 2 ^ w := by omega
      have hcur1_w : cur + 1 < 2 ^ w := by omega
      have hcur2_w : cur + 2 < 2 ^ w := by omega
      have hm_w : m < 2 ^ w := by omega
      set st₁ := st.setReg rG γ₀
      have he₁ : Exec w (.assign rG (.op .add (.reg rNumComp) (.reg rM))) st st₁ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrK, hrm,
          hK_w, hm_w, hγ₀_w, γ₀])
      have hread_cur : (Expr.read aAttSt (.reg rG)).eval w st₁ = some cur :=
        read_reg_eval (by simp [st₁]) hγ₀_w (by simpa [st₁, cur] using hget_st γ₀ hγ₀_B) hcur_w
      set st₂ := st₁.setReg rCur cur
      have he₂ : Exec w (.assign rCur (.read aAttSt (.reg rG))) st₁ st₂ 3 := .assign hread_cur
      have hch_I : st₂.arrs aChordI = s₀.arrs aChordI := by
        simp [st₂, st₁]; exact hk.2 aChordI (by decide)
      have hch_J : st₂.arrs aChordJ = s₀.arrs aChordJ := by
        simp [st₂, st₁]; exact hk.2 aChordJ (by decide)
      have hread_I : (Expr.read aChordI (.reg rM)).eval w st₂ = some chordPairs[m].1 :=
        read_reg_eval (by simp [st₂, st₁, hrm]) hm_w
          (by rw [hch_I]; exact hch.get_I m hm) (by omega)
      set st₃ := st₂.setReg rTmp1 chordPairs[m].1
      have he₃ : Exec w (.assign rTmp1 (.read aChordI (.reg rM))) st₂ st₃ 3 := .assign hread_I
      have hread_J : (Expr.read aChordJ (.reg rM)).eval w st₃ = some chordPairs[m].2 :=
        read_reg_eval (by simp [st₃, st₂, st₁, hrm]) hm_w
          (by simp [st₃, hch_J]; exact hch.get_J m hm) (by omega)
      set st₄ := st₃.setReg rTmp2 chordPairs[m].2
      have he₄ : Exec w (.assign rTmp2 (.read aChordJ (.reg rM))) st₃ st₄ 3 := .assign hread_J
      set st₅ := st₄.writeArr aAttEnt cur chordPairs[m].1
      have he₅ : Exec w (.write aAttEnt (.reg rCur) (.reg rTmp1)) st₄ st₅ 3 :=
        .write (reg_eval (by simp [st₄, st₃, st₂]) hcur_w)
          (reg_eval (by simp [st₄, st₃]) (by omega))
          (by simp [st₄, st₃, st₂, st₁, hlen_ent]; omega)
      set st₆ := st₅.writeArr aAttEnt (cur + 1) chordPairs[m].2
      have he₆ : Exec w (.write aAttEnt (.op .add (.reg rCur) (.const 1)) (.reg rTmp2)) st₅ st₆ 5 :=
        .write (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, st₅, st₄, st₃, st₂,
            hcur_w, hw1, hcur1_w])
          (reg_eval (by simp [st₅, st₄]) (by omega))
          (by simp [st₅, st₄, st₃, st₂, st₁, hlen_ent]; omega)
      set st₇ := st₆.writeArr aAttEn γ₀ (cur + 2)
      have he₇ : Exec w (.write aAttEn (.reg rG) (.op .add (.reg rCur) (.const 2))) st₆ st₇ 5 :=
        .write (reg_eval (by simp [st₆, st₅, st₄, st₃, st₂, st₁]) hγ₀_w)
          (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, st₆, st₅, st₄, st₃, st₂,
            hcur_w, hw2, hcur2_w])
          (by simp [st₆, st₅, st₄, st₃, st₂, st₁, hlen_en, hγ₀_B])
      have hex_body : Exec w attFillChordBody st st₇ (4 + (3 + (3 + (3 + (3 + (5 + 5)))))) :=
        .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ he₇)))))
      have hk₇ : Keeps attachScanRegs attachArrs s₀ st₇ :=
        ((((((hk.setReg (by simp [attachScanRegs]) _).setReg
          (by simp [attachScanRegs]) _).setReg (by simp [attachScanRegs]) _).setReg
          (by simp [attachScanRegs]) _).writeArr (by simp [attachArrs]) _ _).writeArr
          (by simp [attachArrs]) _ _).writeArr (by simp [attachArrs]) _ _
      refine ⟨st₇, _, hex_body, by omega,
        ⟨hk₇.setReg (by simp [attachScanRegs]) _, by simp,
         by simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, hlen_st],
         by simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, hlen_en],
         by simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, hlen_ent],
         fun γ hγ => by simpa [st₇, st₆, st₅, st₄, st₃, st₂, st₁] using hget_st γ hγ,
         fun γ hγ hγ_B => ?_⟩,
        by simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, hrm]⟩
      have hγ_lt : γ < γ₀ + 1 := by omega
      rcases Nat.lt_succ_iff_lt_or_eq.mp hγ_lt with hlt_γ | rfl
      · have hne_γ : γ₀ ≠ γ := Nat.ne_of_gt hlt_γ
        obtain ⟨hen_prev, hent_prev⟩ := hdone γ hlt_γ hγ_B
        refine ⟨?_, fun k hk => ?_⟩
        · simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, List.getElem?_set_ne hne_γ, hen_prev]
        · have hne0 : cur ≠ attOffset H T bridges γ + k :=
            attOffset_disjoint H T bridges hγ₀_B hγ_B hne_γ (k₁ := 0) (by omega) hk
          have hne1 : cur + 1 ≠ attOffset H T bridges γ + k :=
            attOffset_disjoint H T bridges hγ₀_B hγ_B hne_γ (k₁ := 1) (by omega) hk
          simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁,
            List.getElem?_set_ne hne1, List.getElem?_set_ne hne0, hent_prev k hk]
      · refine ⟨?_, fun k hk => ?_⟩
        · have hlt_e : γ₀ < (st.arrs aAttEn).length := by rw [hlen_en]; exact hγ₀_B
          simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁, List.getElem?_set_self hlt_e, cur, hatt_len_m]
        · simp only [State.setReg_arrs, st₇,
            State.writeArr_arrs_ne _ _ _ (by decide : aAttEnt ≠ aAttEn),
            st₆, st₅, State.writeArr_arrs_self, st₄, st₃, st₂, st₁]
          rw [hatt_len_m] at hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk0 | rfl
          · have hk_eq : k = 0 := by omega
            subst hk_eq
            have hlt0' : cur < (st.arrs aAttEnt).length := by rw [hlen_ent]; omega
            simp [cur, List.getElem?_set_ne (by omega : attOffset H T bridges γ₀ + 1 ≠
              attOffset H T bridges γ₀), List.getElem?_set_self hlt0', hatt_m]
          · have hlt1 : cur + 1 < ((st.arrs aAttEnt).set cur chordPairs[m].1).length := by
              rw [List.length_set, hlen_ent]; omega
            simp [cur, List.getElem?_set_self hlt1, hatt_m])
    0 (Nat.zero_le _) s₄ hCI0
  obtain ⟨s₅, t₅, hex₅, ht₅, hk₅, -, hlen_st₅, hlen_en₅, hlen_ent₅, hget_st₅, hdone₅⟩ := hloop₂
  refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), ?_, hk₅, hlen_ent₅, ?_⟩
  · have hsum := sum_deg_cycle_le lists hT
    simp only [Expr.cost] at ht₃ ht₅
    have e : ∑ j ∈ Finset.range T.length,
        (1 + 6 + (12 + 48 * degOf lists ((T.map Fin.val).getD j 0))) =
        19 * T.length + 48 * ∑ j ∈ Finset.range T.length,
          degOf lists ((T.map Fin.val).getD j 0) := by
      rw [Finset.mul_sum, show 19 * T.length = ∑ _j ∈ Finset.range T.length, 19 by simp [mul_comm],
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e] at ht₃
    omega
  · refine ⟨hlen_st₅, hlen_en₅, fun ⟨γ, hγ⟩ => ?_⟩
    obtain ⟨hen_γ, hent_γ⟩ := hdone₅ γ (by omega) hγ
    have hst_γ := hget_st₅ γ hγ
    set st := attOffset H T bridges γ
    set l := (bridges[γ]'hγ).attachmentIndices H T
    have hγ_st : γ < (s₅.arrs aAttSt).length := by rw [hlen_st₅]; exact hγ
    have hγ_en : γ < (s₅.arrs aAttEn).length := by rw [hlen_en₅]; exact hγ
    have hen_le_ent : st + l.length ≤ (s₅.arrs aAttEnt).length := by
      rw [hlen_ent₅, ← attOffset_length H T bridges]
      have hle := attOffset_mono H T bridges (γ₁ := γ + 1) (γ₂ := bridges.length) (by omega) le_rfl
      rw [attOffset_succ H T bridges hγ] at hle
      exact hle
    refine ⟨st, st + l.length, hγ_st, hγ_en, hen_le_ent, by dsimp only [st, l]; omega,
      by simpa [List.getElem?_eq_getElem hγ_st] using hst_γ,
      by simpa [List.getElem?_eq_getElem hγ_en] using hen_γ,
      by omega, fun k hk => ?_⟩
    have hget_k := hent_γ k hk
    have hk' : k < l.length := hk
    have hlt_k : st + k < (s₅.arrs aAttEnt).length := by omega
    rwa [List.getElem?_eq_getElem hlt_k, Option.some.injEq] at hget_k

set_option maxHeartbeats 400000 in
/-- **Execution of `attachListsProg`** (the attachment lists of Section 5.1).
Builds the CSR list family `(aAttSt, aAttEn, aAttEnt)` storing `bridges[γ].attachmentIndices H T`
for every `γ < bridges.length`, with `rNumBridges = bridges.length` and
`rTotAtt = totalAttachments H T bridges`, in $O(n + |T| + m)$ steps. -/
theorem attachListsProg_exec {w : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (lists : Fin n → List ℕ) (T : List (Fin n)) (hT : T.Nodup)
    (segs : List (List (Fin n))) (items : List ℕ)
    (s₀ : State) (hpre : ChordPre H lists T s₀) (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (hcomp : CompSegsOK H T segs items s₀)
    (hall : ∀ x : Fin n, x ∉ T → x.1 ∈ items)
    (hch : ChordsArrOK (s₀.arrs aEnt).length (chordsUpTo lists T T.length) s₀)
    (hnw : 4 * (n + (s₀.arrs aEnt).length + 2) < 2 ^ w)
    (hM_le : totalAdjEntries lists ≤ (s₀.arrs aEnt).length) :
    ∃ s' t, Exec w attachListsProg s₀ s' t ∧
      t ≤ 50 + 25 * n + 38 * T.length + 71 * (s₀.arrs aEnt).length + 94 * totalAdjEntries lists ∧
      Keeps attachRegs attachArrs s₀ s' ∧
      s'.regs rNumBridges =
        (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length ∧
      s'.regs rTotAtt =
        totalAttachments H T (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)) ∧
      (s'.arrs aAttEnt).length =
        totalAttachments H T (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)) ∧
      IsListFamily (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length
        aAttSt aAttEn aAttEnt
        (fun γ : Fin (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)).length =>
          ((bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length))[γ.1]'γ.2).attachmentIndices H T)
        s' := by
  set bridges := bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)
  have hw1 : 1 < 2 ^ w := by omega
  have hK_le_n : segs.length ≤ n := hcomp.segs_le_n
  have hM_le_ent : (chordsUpTo lists T T.length).length ≤ (s₀.arrs aEnt).length := hch.pairs_le_M
  have hB_le : bridges.length ≤ n + (s₀.arrs aEnt).length := by
    simp [bridges, bridgesOfSegsAndChords, chordBridgesOfPairs]; omega
  have htot_le : totalAttachments H T bridges ≤ totalAdjEntries lists :=
    totalAttachments_bridgesOfSegsAndChords_le hpre.adj.2 hT hcomp hall
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hrB₁, hlen₁, hget_len₁⟩ :=
    attCountProg_exec H lists T hT segs items s₀ hpre hent hcomp hall hch hnw
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hrtot₂, hlen_st₂, hlen_en₂, hlen_ent₂, hget_st₂, hget_en₂⟩ :=
    attPrefixProg_exec H T bridges s₁ hrB₁ hlen₁ hget_len₁ hw1 (by omega) (by omega)
  have hk₁₂ : Keeps attachRegs attachArrs s₀ s₂ :=
    hk₁.trans hk₂ (fun _ hr => mem_attachRegs_of_mem_prefixRegs hr)
      (fun _ ha => mem_attachArrs_of_mem_prefixArrs ha)
  have hpre₂ : ChordPre H lists T s₂ :=
    ⟨hpre.adj.of_arrs_eq (hk₁₂.2 _ (by decide)) (hk₁₂.2 _ (by decide)) (hk₁₂.2 _ (by decide)),
     by rw [hk₁₂.2 _ (by decide)]; exact hpre.cyc,
     by rw [hk₁₂.2 _ (by decide)]; exact hpre.pos,
     by rw [hk₁₂.1 _ (by decide)]; exact hpre.k,
     by rw [hk₁₂.1 _ (by decide)]; exact hpre.n⟩
  have hcomp₂ : CompSegsOK H T segs items s₂ :=
    hcomp.of_state (by rw [hk₁₂.1 _ (by decide)]) (by rw [hk₁₂.2 _ (by decide)])
      (by rw [hk₁₂.2 _ (by decide)]) (by rw [hk₁₂.2 _ (by decide)])
  have hch₂ : ChordsArrOK (s₂.arrs aEnt).length (chordsUpTo lists T T.length) s₂ := by
    rw [hk₁₂.2 aEnt (by decide)]
    exact hch.of_state (by rw [hk₁₂.1 _ (by decide)]) (by rw [hk₁₂.2 _ (by decide)])
      (by rw [hk₁₂.2 _ (by decide)])
  have hent₂ : (s₂.arrs aEnt).length = (s₀.arrs aEnt).length :=
    congrArg List.length (hk₁₂.2 aEnt (by decide))
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hlen_ent₃, hfam₃⟩ :=
    attFillProg_exec H lists T hT segs items s₂ hpre₂ (by rw [hent₂]; exact hent)
      hcomp₂ hall hch₂ (by rw [hent₂]; exact hnw) (by rw [hent₂]; exact hM_le)
      hlen_st₂ hlen_en₂ hlen_ent₂ hget_st₂ hget_en₂
  have hk_all : Keeps attachRegs attachArrs s₀ s₃ :=
    hk₁₂.trans hk₃ (fun _ hr => mem_attachRegs_of_mem_attachScanRegs hr)
      (fun _ ha => ha)
  have hrB₃ : s₃.regs rNumBridges = bridges.length := by
    rw [hk₃.1 rNumBridges (by decide), hk₂.1 rNumBridges (by decide), hrB₁]
  have hrtot₃ : s₃.regs rTotAtt = totalAttachments H T bridges := by
    rw [hk₃.1 rTotAtt (by decide), hrtot₂]
  rw [hent₂] at ht₃
  refine ⟨s₃, _, .seq hex₁ (.seq hex₂ hex₃), by omega, hk_all, hrB₃, hrtot₃, hlen_ent₃, hfam₃⟩

end GraphMinor.Compute
