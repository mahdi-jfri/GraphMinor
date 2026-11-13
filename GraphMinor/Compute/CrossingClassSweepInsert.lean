module

public import GraphMinor.Compute.CrossingClassSweepClean

/-!
# Minimum endpoints and candidate insertion

This file implements minimum-endpoint search and insertion of the bridge-candidate sweep in Section 5.2 of
`docs/crossing/crossing_extractor.tex`. The execution theorems follow the stored candidates and
bound the
number of Word RAM steps.
-/

@[expose] public section

namespace GraphMinor.Compute

open GraphMinor.Crossing

/-! ### 5. Step 3 helper: `minRightProg` and `minRightCandidate` -/

/-- Left-fold characterization of `minRightCandidate`. -/
def minRightFold (best : Candidate) : List Candidate → Candidate
  | [] => best
  | J :: Js => minRightFold (if J.r < best.r then J else best) Js

@[simp]
theorem minRightFold_nil (best : Candidate) : minRightFold best [] = best := rfl

@[simp]
theorem minRightFold_cons (best J : Candidate) (Js : List Candidate) :
    minRightFold best (J :: Js) = minRightFold (if J.r < best.r then J else best) Js := rfl

theorem minRightFold_append (best : Candidate) (xs ys : List Candidate) :
    minRightFold best (xs ++ ys) = minRightFold (minRightFold best xs) ys := by
  induction xs generalizing best with
  | nil => rfl
  | cons x xs' ih => exact ih _

theorem minRightFold_eq_ite (best J₁ : Candidate) (Js : List Candidate) :
    minRightFold best (J₁ :: Js) =
      if best.r ≤ (minRightFold J₁ Js).r then best else minRightFold J₁ Js := by
  induction Js generalizing best J₁ with
  | nil =>
    rw [minRightFold_cons, minRightFold_nil, minRightFold_nil]
    split_ifs <;> first | rfl | omega
  | cons J₂ Js' ih =>
    rw [minRightFold_cons, ih (if J₁.r < best.r then J₁ else best) J₂, ih J₁ J₂]
    split_ifs <;> first | rfl | omega

theorem minRightCandidate_eq_minRightFold (J₀ : Candidate) (Js : List Candidate) :
    minRightCandidate (J₀ :: Js) = some (minRightFold J₀ Js) := by
  induction Js generalizing J₀ with
  | nil => rfl
  | cons J₁ Js' ih =>
    simp only [minRightCandidate, ih J₁, minRightFold_eq_ite]
    split_ifs <;> rfl

theorem minRightCandidate_eq_minRightFold_self {items : List Candidate} (hne : items ≠ []) :
    minRightCandidate items =
      some (minRightFold (items[0]'(List.length_pos_of_ne_nil hne)) items) := by
  cases items with
  | nil => contradiction
  | cons J₀ Js =>
    simp [minRightCandidate_eq_minRightFold, minRightFold]

/-- Loop body for `minRightProg` at offset `rM` into `[rDiffSt, rDiffEn)`. -/
def minRightBody : Cmd :=
  .seq (.assign rCandTmp1 (.op .add (.reg rDiffSt) (.reg rM)))
  (.seq (.assign rCandTmp2 (.read aItemR (.reg rCandTmp1)))
  (.ite (.op .lt (.reg rCandTmp2) (.reg rMinR))
    (.seq (.assign rMinL (.read aItemL (.reg rCandTmp1)))
    (.seq (.assign rMinR (.reg rCandTmp2))
          (.assign rMinG (.read aItemG (.reg rCandTmp1)))))
    .skip))

/-- Compute `minRightCandidate B.items` into `(rMinL, rMinR, rMinG)`. -/
def minRightProg : Cmd :=
  .seq (.assign rMinL (.read aItemL (.reg rDiffSt)))
  (.seq (.assign rMinR (.read aItemR (.reg rDiffSt)))
  (.seq (.assign rMinG (.read aItemG (.reg rDiffSt)))
  (.seq (.assign rTmp2 (.op .sub (.reg rDiffEn) (.reg rDiffSt)))
  (.seq (.assign rM (.const 0))
        (forUp rM (.reg rTmp2) minRightBody)))))

theorem minRightFold_mem {best : Candidate} {xs : List Candidate} :
    minRightFold best xs = best ∨ minRightFold best xs ∈ xs := by
  induction xs generalizing best with
  | nil => exact Or.inl rfl
  | cons x xs' ih =>
    simp only [minRightFold]
    rcases ih (best := if x.r < best.r then x else best) with heq | hmem
    · rw [heq]
      split_ifs
      · exact Or.inr List.mem_cons_self
      · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem x hmem)

private def minRightInv (st₀ : ℕ) (items : List Candidate) (hne : items ≠ []) (s₀ : State)
    (k : ℕ) (s : State) : Prop :=
  s.regs rDiffSt = st₀ ∧
  s.regs rTmp2 = items.length ∧
  s.regs rM = k ∧
  s.regs rMinL = (minRightFold (items[0]'(List.length_pos_of_ne_nil hne)) (items.take k)).l ∧
  s.regs rMinR = (minRightFold (items[0]'(List.length_pos_of_ne_nil hne)) (items.take k)).r ∧
  s.regs rMinG = (minRightFold (items[0]'(List.length_pos_of_ne_nil hne)) (items.take k)).γ ∧
  (∀ j (hj : j < items.length),
    (s.arrs aItemL)[st₀ + j]? = some (items[j]'hj).l ∧
    (s.arrs aItemR)[st₀ + j]? = some (items[j]'hj).r ∧
    (s.arrs aItemG)[st₀ + j]? = some (items[j]'hj).γ) ∧
  (∀ r, r ≠ rMinL ∧ r ≠ rMinR ∧ r ≠ rMinG ∧ r ≠ rTmp2 ∧ r ≠ rM ∧
        r ≠ rCandTmp1 ∧ r ≠ rCandTmp2 → s.regs r = s₀.regs r) ∧
  (∀ a, s.arrs a = s₀.arrs a)

private theorem minRightBody_triple {w : ℕ} (st₀ : ℕ) (items : List Candidate)
    (hne : items ≠ []) (s₀ : State) (hw : 1 < 2 ^ w) (hst₀ : st₀ + items.length < 2 ^ w)
    (hItemsW : ∀ J ∈ items, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w) :
    ∀ k < items.length,
      ⦃minRightInv st₀ items hne s₀ k⦄[w]
        minRightBody
      ⦃fun s' => minRightInv st₀ items hne s₀ (k + 1) (s'.setReg rM (k + 1)) ∧ s'.regs rM = k⦄ ≤
        fun _ => 25 := by
  intro k hk s hs
  rcases hs with ⟨hrDiffSt, hrTmp2, hrM, hrMinL, hrMinR, hrMinG, hItems, hRegs, hArrs⟩
  set J₀ := items[0]'(List.length_pos_of_ne_nil hne) with hJ₀_def
  set best := minRightFold J₀ (items.take k) with hbest_def
  have hbest_mem : best ∈ items := by
    rcases minRightFold_mem (best := J₀) (xs := items.take k) with heq | hmem
    · rw [hbest_def, heq]; exact List.getElem_mem _
    · exact List.mem_of_mem_take hmem
  obtain ⟨_, hbest_r, _⟩ := hItemsW best hbest_mem
  set Jk := items[k]'hk
  obtain ⟨hJkl, hJkr, hJkγ⟩ := hItemsW Jk (List.getElem_mem hk)
  obtain ⟨hItemLk, hItemRk, hItemGk⟩ := hItems k hk
  have hfold_succ :
      minRightFold J₀ (items.take (k + 1)) = if Jk.r < best.r then Jk else best := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk, minRightFold_append]
    rfl
  let s₁ := s.setReg rCandTmp1 (st₀ + k)
  have he1 : (Expr.op .add (.reg rDiffSt) (.reg rM)).eval w s = some (st₀ + k) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrDiffSt, hrM,
      show st₀ < 2 ^ w by omega, show k < 2 ^ w by omega, show st₀ + k < 2 ^ w by omega]
  let s₂ := s₁.setReg rCandTmp2 Jk.r
  have he2 : (Expr.read aItemR (.reg rCandTmp1)).eval w s₁ = some Jk.r :=
    read_reg_eval (by simp [s₁]) (by omega) hItemRk hJkr
  by_cases hlt : Jk.r < best.r
  · have hcond : (Expr.op .lt (.reg rCandTmp2) (.reg rMinR)).eval w s₂ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hrMinR,
        hJkr, hbest_r, hlt, hw]
    let s₃ := s₂.setReg rMinL Jk.l
    have he3 : (Expr.read aItemL (.reg rCandTmp1)).eval w s₂ = some Jk.l :=
      read_reg_eval (by simp [s₂, s₁]) (by omega) hItemLk hJkl
    let s₄ := s₃.setReg rMinR Jk.r
    have he4 : (Expr.reg rCandTmp2).eval w s₃ = some Jk.r := by
      simp [Expr.eval, s₃, s₂, checkWord, hJkr]
    let s₅ := s₄.setReg rMinG Jk.γ
    have he5 : (Expr.read aItemG (.reg rCandTmp1)).eval w s₄ = some Jk.γ :=
      read_reg_eval (by simp [s₄, s₃, s₂, s₁]) (by omega) hItemGk hJkγ
    have hex : Exec w minRightBody s s₅ _ :=
      .seq (.assign he1) (.seq (.assign he2)
        (.ite_true hcond (by dsimp [Expr.cost]; omega)
          (.seq (.assign he3) (.seq (.assign he4) (.assign he5)))))
    refine ⟨s₅, _, hex, by dsimp [Expr.cost]; omega, ?_, by simp [s₅, s₄, s₃, s₂, s₁, hrM]⟩
    dsimp only [minRightInv]
    rw [← hJ₀_def, hfold_succ]
    refine ⟨by simp [s₅, s₄, s₃, s₂, s₁, hrDiffSt],
      by simp [s₅, s₄, s₃, s₂, s₁, hrTmp2],
      by simp,
      by simp [hlt, s₅, s₄, s₃],
      by simp [hlt, s₅, s₄],
      by simp [hlt, s₅],
      hItems, ?_, hArrs⟩
    intro r ⟨h1, h2, h3, h4, h5, h6, h7⟩
    simp [s₅, s₄, s₃, s₂, s₁, h1, h2, h3, h5, h6, h7,
      hRegs r ⟨h1, h2, h3, h4, h5, h6, h7⟩]
  · have hcond : (Expr.op .lt (.reg rCandTmp2) (.reg rMinR)).eval w s₂ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hrMinR,
        hJkr, hbest_r, hlt, show (0 : ℕ) < 2 ^ w by omega]
    have hex : Exec w minRightBody s s₂ _ :=
      .seq (.assign he1) (.seq (.assign he2) (.ite_false hcond (.skip s₂)))
    refine ⟨s₂, _, hex, by dsimp [Expr.cost]; omega, ?_, by simp [s₂, s₁, hrM]⟩
    dsimp only [minRightInv]
    rw [← hJ₀_def, hfold_succ]
    refine ⟨by simp [s₂, s₁, hrDiffSt],
      by simp [s₂, s₁, hrTmp2],
      by simp,
      by simp [hlt, s₂, s₁, hrMinL],
      by simp [hlt, s₂, s₁, hrMinR],
      by simp [hlt, s₂, s₁, hrMinG],
      hItems, ?_, hArrs⟩
    intro r ⟨h1, h2, h3, h4, h5, h6, h7⟩
    simp [s₂, s₁, h5, h6, h7, hRegs r ⟨h1, h2, h3, h4, h5, h6, h7⟩]

/-- Total-correctness specification of `minRightProg`. -/
theorem minRightProg_exec {w : ℕ} (st₀ : ℕ) (items : List Candidate) (hne : items ≠ [])
    (s : State) (hw : 1 < 2 ^ w) (hst₀ : st₀ + items.length < 2 ^ w)
    (hItemsW : ∀ J ∈ items, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w)
    (hrSt : s.regs rDiffSt = st₀)
    (hrEn : s.regs rDiffEn = st₀ + items.length)
    (hItems : ∀ j (hj : j < items.length),
      (s.arrs aItemL)[st₀ + j]? = some (items[j]'hj).l ∧
      (s.arrs aItemR)[st₀ + j]? = some (items[j]'hj).r ∧
      (s.arrs aItemG)[st₀ + j]? = some (items[j]'hj).γ) :
    ∃ s' t J_min, Exec w minRightProg s s' t ∧
      t ≤ 25 + 32 * items.length ∧
      minRightCandidate items = some J_min ∧
      s'.regs rMinL = J_min.l ∧
      s'.regs rMinR = J_min.r ∧
      s'.regs rMinG = J_min.γ ∧
      (∀ r, r ≠ rMinL ∧ r ≠ rMinR ∧ r ≠ rMinG ∧ r ≠ rTmp2 ∧ r ≠ rM ∧
            r ≠ rCandTmp1 ∧ r ≠ rCandTmp2 → s'.regs r = s.regs r) ∧
      (∀ a, s'.arrs a = s.arrs a) := by
  have hpos : 0 < items.length := List.length_pos_of_ne_nil hne
  set J₀ := items[0]'hpos with hJ₀_def
  obtain ⟨hJ₀l, hJ₀r, hJ₀γ⟩ := hItemsW J₀ (List.getElem_mem hpos)
  obtain ⟨hItemL0, hItemR0, hItemG0⟩ := hItems 0 hpos
  rw [Nat.add_zero] at hItemL0 hItemR0 hItemG0
  let s₁ := s.setReg rMinL J₀.l
  have he1 : (Expr.read aItemL (.reg rDiffSt)).eval w s = some J₀.l :=
    read_reg_eval hrSt (by omega) hItemL0 hJ₀l
  let s₂ := s₁.setReg rMinR J₀.r
  have he2 : (Expr.read aItemR (.reg rDiffSt)).eval w s₁ = some J₀.r :=
    read_reg_eval (by simp [s₁, hrSt]) (by omega) hItemR0 hJ₀r
  let s₃ := s₂.setReg rMinG J₀.γ
  have he3 : (Expr.read aItemG (.reg rDiffSt)).eval w s₂ = some J₀.γ :=
    read_reg_eval (by simp [s₂, s₁, hrSt]) (by omega) hItemG0 hJ₀γ
  let s₄ := s₃.setReg rTmp2 items.length
  have he4 : (Expr.op .sub (.reg rDiffEn) (.reg rDiffSt)).eval w s₃ = some items.length := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hrSt, hrEn,
      show st₀ + items.length < 2 ^ w by omega, show st₀ < 2 ^ w by omega,
      show items.length < 2 ^ w by omega]
  let s₅ := s₄.setReg rM 0
  have he5 : (Expr.const 0).eval w s₄ = some 0 := by
    simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega]
  have hInv0 : minRightInv st₀ items hne s 0 s₅ := by
    dsimp only [minRightInv]
    rw [← hJ₀_def]
    refine ⟨by simp [s₅, s₄, s₃, s₂, s₁, hrSt],
      by simp [s₅, s₄],
      by simp [s₅],
      by simp [s₅, s₄, s₃, s₂, s₁],
      by simp [s₅, s₄, s₃, s₂],
      by simp [s₅, s₄, s₃],
      hItems, ?_, fun _ => rfl⟩
    intro r ⟨h1, h2, h3, h4, h5, _⟩
    simp [s₅, s₄, s₃, s₂, s₁, h1, h2, h3, h4, h5]
  have hLoop := Triple.forUp_const (r_i := rM) (hi := .reg rTmp2)
    (minRightInv st₀ items hne s) items.length 25 hw
    (by omega)
    (fun k _ st_k hIk => by
      rcases hIk with ⟨_, hr2, hrM_k, _⟩
      refine ⟨hrM_k, ?_⟩
      simp [Expr.eval, hr2, checkWord, show items.length < 2 ^ w by omega])
    (minRightBody_triple st₀ items hne s hw hst₀ hItemsW)
  rcases hLoop s₅ hInv0 with ⟨s₆, tLoop, hexLoop, htLoop, hInvN⟩
  dsimp only [Expr.cost] at htLoop
  rcases hInvN with ⟨_, _, _, hrMinL_6, hrMinR_6, hrMinG_6, _, hRegs_6, hArrs_6⟩
  rw [List.take_length, ← hJ₀_def] at hrMinL_6 hrMinR_6 hrMinG_6
  have hex : Exec w minRightProg s s₆ _ :=
    .seq (.assign he1) (.seq (.assign he2) (.seq (.assign he3)
      (.seq (.assign he4) (.seq (.assign he5) hexLoop))))
  exact ⟨s₆, _, minRightFold J₀ items, hex, by dsimp [Expr.cost]; omega,
    minRightCandidate_eq_minRightFold_self hne, hrMinL_6, hrMinR_6, hrMinG_6,
    hRegs_6, hArrs_6⟩

/-! ### 6. Step 4 of the sweep: `insertCandProg` -/

/-- Step 4 of the sweep (`insertCandidate`): append `(rCurL, rCurR, rCurG)` to the top block if its
color is `rCurG`, or push a new block on top of the stack. -/
def insertCandProg : Cmd :=
  .seq (.write aItemL (.reg rItemCnt) (.reg rCurL))
  (.seq (.write aItemR (.reg rItemCnt) (.reg rCurR))
  (.seq (.write aItemG (.reg rItemCnt) (.reg rCurG))
  (.seq (.assign rTmp1 (.op .add (.reg rItemCnt) (.const 1)))
  (.ite (.op .lt (.const 0) (.reg rBlkCnt))
    (.seq (.assign rG (.op .sub (.reg rBlkCnt) (.const 1)))
    (.seq (.assign rTmp2 (.read aBlkG (.reg rG)))
    (.ite (.op .eq (.reg rTmp2) (.reg rCurG))
      (.seq (.write aBlkEn (.reg rG) (.reg rTmp1))
            (.assign rItemCnt (.reg rTmp1)))
      (.seq (.write aBlkG (.reg rBlkCnt) (.reg rCurG))
      (.seq (.write aBlkSt (.reg rBlkCnt) (.reg rItemCnt))
      (.seq (.write aBlkEn (.reg rBlkCnt) (.reg rTmp1))
      (.seq (.assign rBlkCnt (.op .add (.reg rBlkCnt) (.const 1)))
            (.assign rItemCnt (.reg rTmp1)))))))))
    (.seq (.write aBlkG (.const 0) (.reg rCurG))
    (.seq (.write aBlkSt (.const 0) (.reg rItemCnt))
    (.seq (.write aBlkEn (.const 0) (.reg rTmp1))
    (.seq (.assign rBlkCnt (.const 1))
          (.assign rItemCnt (.reg rTmp1))))))))))

/-- Specification of `insertCandProg`. -/
theorem insertCandProg_exec {w : ℕ} (cap : ℕ) (I : Candidate) (st : List Block) (s : State)
    (hw : 1 < 2 ^ w) (hcap : cap < 2 ^ w)
    (hIW : I.l < 2 ^ w ∧ I.r < 2 ^ w ∧ I.γ < 2 ^ w)
    (hBlkW : ∀ B ∈ st, B.γ < 2 ^ w)
    (hst : IsBlockStack cap st s)
    (hble : st.length + 1 ≤ cap)
    (henle : (storedCandidates st).length + 1 ≤ cap)
    (hCurL : s.regs rCurL = I.l) (hCurR : s.regs rCurR = I.r) (hCurG : s.regs rCurG = I.γ) :
    ∃ s' t, Exec w insertCandProg s s' t ∧
      t ≤ 45 ∧
      IsBlockStack cap (insertCandidate I st) s' ∧
      (∀ r, r ≠ rBlkCnt ∧ r ≠ rItemCnt ∧ r ≠ rG ∧ r ≠ rTmp1 ∧ r ≠ rTmp2 → s'.regs r = s.regs r) ∧
      (∀ a, a ≠ aBlkG ∧ a ≠ aBlkSt ∧ a ≠ aBlkEn ∧ a ≠ aItemL ∧ a ≠ aItemR ∧ a ≠ aItemG →
        s'.arrs a = s.arrs a) := by
  rcases hst with ⟨hL1, hL2, hL3, hL4, hL5, hL6, hrBlk, hrItem, _, _, hBlocksOK⟩
  rcases hIW with ⟨hIl, hIr, hIγ⟩
  set m := (storedCandidates st).length with hm_def
  let s₁ := s.writeArr aItemL m I.l
  have hi1 : (Expr.reg rItemCnt).eval w s = some m := by
    simp [Expr.eval, hrItem, checkWord, show m < 2 ^ w by omega]
  have hv1 : (Expr.reg rCurL).eval w s = some I.l := by
    simp [Expr.eval, hCurL, checkWord, hIl]
  have hlen1 : m < (s.arrs aItemL).length := by rw [hL4]; omega
  let s₂ := s₁.writeArr aItemR m I.r
  have hi2 : (Expr.reg rItemCnt).eval w s₁ = some m := by
    simp [Expr.eval, s₁, hrItem, checkWord, show m < 2 ^ w by omega]
  have hv2 : (Expr.reg rCurR).eval w s₁ = some I.r := by
    simp [Expr.eval, s₁, hCurR, checkWord, hIr]
  have hlen2 : m < (s₁.arrs aItemR).length := by simp [s₁, hL5]; omega
  let s₃ := s₂.writeArr aItemG m I.γ
  have hi3 : (Expr.reg rItemCnt).eval w s₂ = some m := by
    simp [Expr.eval, s₂, s₁, hrItem, checkWord, show m < 2 ^ w by omega]
  have hv3 : (Expr.reg rCurG).eval w s₂ = some I.γ := by
    simp [Expr.eval, s₂, s₁, hCurG, checkWord, hIγ]
  have hlen3 : m < (s₂.arrs aItemG).length := by simp [s₂, s₁, hL6]; omega
  let s₄ := s₃.setReg rTmp1 (m + 1)
  have he4 : (Expr.op .add (.reg rItemCnt) (.const 1)).eval w s₃ = some (m + 1) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hrItem, hw,
      show m < 2 ^ w by omega, show m + 1 < 2 ^ w by omega]
  cases st with
  | nil =>
    have hm0 : m = 0 := rfl
    have hcond0 : (Expr.op .lt (.const 0) (.reg rBlkCnt)).eval w s₄ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₄, s₃, s₂, s₁,
        hrBlk, show (0 : ℕ) < 2 ^ w by omega]
    let s₅ := s₄.writeArr aBlkG 0 I.γ
    have hi5 : (Expr.const 0).eval w s₄ = some 0 := by
      simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega]
    have hv5 : (Expr.reg rCurG).eval w s₄ = some I.γ := by
      simp [Expr.eval, s₄, s₃, s₂, s₁, hCurG, checkWord, hIγ]
    have hlen5 : 0 < (s₄.arrs aBlkG).length := by
      simp [s₄, s₃, s₂, s₁, hL1]; omega
    let s₆ := s₅.writeArr aBlkSt 0 0
    have hv6 : (Expr.reg rItemCnt).eval w s₅ = some 0 := by
      simp [Expr.eval, s₅, s₄, s₃, s₂, s₁, hrItem, hm0,
        checkWord, show (0 : ℕ) < 2 ^ w by omega]
    have hlen6 : 0 < (s₅.arrs aBlkSt).length := by
      simp [s₅, s₄, s₃, s₂, s₁, hL2]; omega
    let s₇ := s₆.writeArr aBlkEn 0 1
    have hv7 : (Expr.reg rTmp1).eval w s₆ = some 1 := by
      simp [Expr.eval, s₆, s₅, s₄, hm0, checkWord, hw]
    have hlen7 : 0 < (s₆.arrs aBlkEn).length := by
      simp [s₆, s₅, s₄, s₃, s₂, s₁, hL3]; omega
    let s₈ := s₇.setReg rBlkCnt 1
    have he8 : (Expr.const 1).eval w s₇ = some 1 := by simp [Expr.eval, checkWord, hw]
    let s₉ := s₈.setReg rItemCnt 1
    have he9 : (Expr.reg rTmp1).eval w s₈ = some 1 := by
      simp [Expr.eval, s₈, s₇, s₆, s₅, s₄, hm0, checkWord, hw]
    have hex : Exec w insertCandProg s s₉ _ :=
      .seq (.write hi1 hv1 hlen1) (.seq (.write hi2 hv2 hlen2)
      (.seq (.write hi3 hv3 hlen3) (.seq (.assign he4)
        (.ite_false hcond0
          (.seq (.write hi5 hv5 hlen5) (.seq (.write hi5 hv6 hlen6)
          (.seq (.write hi5 hv7 hlen7) (.seq (.assign he8) (.assign he9)))))))))
    refine ⟨s₉, _, hex, by dsimp [Expr.cost]; omega, ?_, ?_, ?_⟩
    · simp only [insertCandidate]
      refine ⟨by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL1],
        by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL2],
        by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL3],
        by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL4],
        by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL5],
        by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL6],
        by simp [s₉, s₈],
        by simp [s₉, storedCandidates],
        hble, henle, ?_⟩
      dsimp only [StackBlocksOK, storedCandidates, List.length_nil, List.flatMap_nil]
      refine ⟨by simp [s₉, s₈, s₇, s₆, s₅, List.getElem?_set_self hlen5],
        by simp [s₉, s₈, s₇, s₆, List.getElem?_set_self hlen6],
        by simp [s₉, s₈, s₇, List.getElem?_set_self hlen7],
        ?_, trivial⟩
      intro k hk
      simp only [List.length_singleton] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      have hlen1' : 0 < (s.arrs aItemL).length := by simpa [hm0] using hlen1
      have hlen2' : 0 < (s.arrs aItemR).length := by simpa [hm0, s₁] using hlen2
      have hlen3' : 0 < (s.arrs aItemG).length := by simpa [hm0, s₂, s₁] using hlen3
      refine ⟨?_, ?_, ?_⟩
      · simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hm0, List.getElem?_set_self hlen1']
      · simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hm0, List.getElem?_set_self hlen2']
      · simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hm0, List.getElem?_set_self hlen3']
    · intro r ⟨h1, h2, _, h4, _⟩
      simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, h1, h2, h4]
    · intro a ⟨ha1, ha2, ha3, ha4, ha5, ha6⟩
      simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha1, ha2, ha3, ha4, ha5, ha6]
  | cons B rest =>
    rcases hBlocksOK with ⟨hBG, hBSt, hBEn, hBItems, hRestOK⟩
    set b := rest.length with hb_def
    set st₀ := (storedCandidates rest).length with hst₀_def
    have hb_eq : (B :: rest).length = b + 1 := rfl
    have hm_eq : m = st₀ + B.items.length := by
      rw [hm_def, length_storedCandidates_cons]; omega
    rw [hb_eq] at hrBlk hble
    have hBW : B.γ < 2 ^ w := hBlkW B List.mem_cons_self
    have hcond0 : (Expr.op .lt (.const 0) (.reg rBlkCnt)).eval w s₄ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₄, s₃, s₂, s₁,
        hrBlk, hw, show b + 1 < 2 ^ w by omega]
    let s₅ := s₄.setReg rG b
    have he5 : (Expr.op .sub (.reg rBlkCnt) (.const 1)).eval w s₄ = some b := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₄, s₃, s₂, s₁,
        hrBlk, hw, show b + 1 < 2 ^ w by omega, show b < 2 ^ w by omega]
    let s₆ := s₅.setReg rTmp2 B.γ
    have hBG₅ : (s₅.arrs aBlkG)[b]? = some B.γ := by
      simp [s₅, s₄, s₃, s₂, s₁, hBG]
    have he6 : (Expr.read aBlkG (.reg rG)).eval w s₅ = some B.γ :=
      read_reg_eval (by simp [s₅]) (by omega) hBG₅ hBW
    by_cases hγ : B.γ = I.γ
    · have hcond1 : (Expr.op .eq (.reg rTmp2) (.reg rCurG)).eval w s₆ = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₆, s₅, s₄, s₃, s₂, s₁,
          hCurG, hγ, hIγ, hw]
      let s₇ := s₆.writeArr aBlkEn b (m + 1)
      have hi7 : (Expr.reg rG).eval w s₆ = some b := by
        simp [Expr.eval, s₆, s₅, checkWord, show b < 2 ^ w by omega]
      have hv7 : (Expr.reg rTmp1).eval w s₆ = some (m + 1) := by
        simp [Expr.eval, s₆, s₅, s₄, checkWord, show m + 1 < 2 ^ w by omega]
      have hlen7 : b < (s₆.arrs aBlkEn).length := by
        simp [s₆, s₅, s₄, s₃, s₂, s₁, hL3]; omega
      let s₈ := s₇.setReg rItemCnt (m + 1)
      have he8 : (Expr.reg rTmp1).eval w s₇ = some (m + 1) := by
        simp [Expr.eval, s₇, s₆, s₅, s₄, checkWord, show m + 1 < 2 ^ w by omega]
      have hex : Exec w insertCandProg s s₈ _ :=
        .seq (.write hi1 hv1 hlen1) (.seq (.write hi2 hv2 hlen2)
        (.seq (.write hi3 hv3 hlen3) (.seq (.assign he4)
          (.ite_true hcond0 (by dsimp [Expr.cost]; omega)
            (.seq (.assign he5) (.seq (.assign he6)
              (.ite_true hcond1 (by dsimp [Expr.cost]; omega)
                (.seq (.write hi7 hv7 hlen7) (.assign he8)))))))))
      refine ⟨s₈, _, hex, by dsimp [Expr.cost]; omega, ?_, ?_, ?_⟩
      · simp only [insertCandidate, hγ, beq_self_eq_true, ↓reduceIte]
        have hlen_stored :
            (storedCandidates ({ γ := I.γ, items := B.items ++ [I] } :: rest)).length = m + 1 := by
          rw [length_storedCandidates_cons, ← hst₀_def]
          dsimp only
          simp only [List.length_append, List.length_singleton]
          omega
        refine ⟨by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL1],
          by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL2],
          by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL3],
          by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL4],
          by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL5],
          by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL6],
          by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hrBlk, b],
          by simp [s₈, hlen_stored],
          by simp; omega,
          by rw [hlen_stored]; exact henle, ?_⟩
        dsimp only [StackBlocksOK]
        rw [← hb_def, ← hst₀_def]
        refine ⟨by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hBG, hγ],
          by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hBSt],
          ?_, ?_, ?_⟩
        · simp [s₈, s₇, List.getElem?_set_self hlen7, hm_eq]
          omega
        · intro k hk
          simp only [List.length_append, List.length_singleton] at hk
          by_cases hkb : k < B.items.length
          · have hne : m ≠ st₀ + k := by omega
            have h1 : (s₈.arrs aItemL)[st₀ + k]? = (s.arrs aItemL)[st₀ + k]? := by
              simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
            have h2 : (s₈.arrs aItemR)[st₀ + k]? = (s.arrs aItemR)[st₀ + k]? := by
              simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
            have h3 : (s₈.arrs aItemG)[st₀ + k]? = (s.arrs aItemG)[st₀ + k]? := by
              simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
            simp only [List.getElem_append_left hkb, h1, h2, h3]
            exact hBItems k hkb
          · have hkeq : k = B.items.length := by omega
            subst hkeq
            have hmk : st₀ + B.items.length = m := hm_eq.symm
            simp only [hmk, List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
            refine ⟨?_, ?_, ?_⟩
            · simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_self hlen1]
            · simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_self
                (show m < (s.arrs aItemR).length by rw [hL5]; omega)]
            · simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_self
                (show m < (s.arrs aItemG).length by rw [hL6]; omega)]
        · refine hRestOK.of_agree_below (fun _ _ => rfl) (fun _ _ => rfl)
            (fun b' hb' => ?_) (fun idx hidx => ?_) (fun idx hidx => ?_) (fun idx hidx => ?_)
          · have hne : b ≠ b' := by omega
            simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
          · have hne : m ≠ idx := by omega
            simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
          · have hne : m ≠ idx := by omega
            simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
          · have hne : m ≠ idx := by omega
            simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
      · intro r ⟨h1, h2, h3, h4, h5⟩
        simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, h2, h3, h4, h5]
      · intro a ⟨ha1, ha2, ha3, ha4, ha5, ha6⟩
        simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha3, ha4, ha5, ha6]
    · have hcond1 : (Expr.op .eq (.reg rTmp2) (.reg rCurG)).eval w s₆ = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₆, s₅, s₄, s₃, s₂, s₁,
          hCurG, hγ, hBW, hIγ, show (0 : ℕ) < 2 ^ w by omega]
      let s₇ := s₆.writeArr aBlkG (b + 1) I.γ
      have hi7 : (Expr.reg rBlkCnt).eval w s₆ = some (b + 1) := by
        simp [Expr.eval, s₆, s₅, s₄, s₃, s₂, s₁, hrBlk,
          checkWord, show b + 1 < 2 ^ w by omega]
      have hv7 : (Expr.reg rCurG).eval w s₆ = some I.γ := by
        simp [Expr.eval, s₆, s₅, s₄, s₃, s₂, s₁, hCurG, checkWord, hIγ]
      have hlen7 : b + 1 < (s₆.arrs aBlkG).length := by
        simp [s₆, s₅, s₄, s₃, s₂, s₁, hL1]; omega
      let s₈ := s₇.writeArr aBlkSt (b + 1) m
      have hi8 : (Expr.reg rBlkCnt).eval w s₇ = some (b + 1) := by
        simp [Expr.eval, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hrBlk,
          checkWord, show b + 1 < 2 ^ w by omega]
      have hv8 : (Expr.reg rItemCnt).eval w s₇ = some m := by
        simp [Expr.eval, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hrItem,
          checkWord, show m < 2 ^ w by omega]
      have hlen8 : b + 1 < (s₇.arrs aBlkSt).length := by
        simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL2]; omega
      let s₉ := s₈.writeArr aBlkEn (b + 1) (m + 1)
      have hi9 : (Expr.reg rBlkCnt).eval w s₈ = some (b + 1) := by
        simp [Expr.eval, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hrBlk,
          checkWord, show b + 1 < 2 ^ w by omega]
      have hv9 : (Expr.reg rTmp1).eval w s₈ = some (m + 1) := by
        simp [Expr.eval, s₈, s₇, s₆, s₅, s₄, checkWord, show m + 1 < 2 ^ w by omega]
      have hlen9 : b + 1 < (s₈.arrs aBlkEn).length := by
        simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL3]; omega
      let s₁₀ := s₉.setReg rBlkCnt (b + 2)
      have he10 : (Expr.op .add (.reg rBlkCnt) (.const 1)).eval w s₉ = some (b + 2) := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
          hrBlk, hw, show b + 1 < 2 ^ w by omega, show b + 1 + 1 < 2 ^ w by omega]
      let s₁₁ := s₁₀.setReg rItemCnt (m + 1)
      have he11 : (Expr.reg rTmp1).eval w s₁₀ = some (m + 1) := by
        simp [Expr.eval, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, checkWord, show m + 1 < 2 ^ w by omega]
      have hex : Exec w insertCandProg s s₁₁ _ :=
        .seq (.write hi1 hv1 hlen1) (.seq (.write hi2 hv2 hlen2)
        (.seq (.write hi3 hv3 hlen3) (.seq (.assign he4)
          (.ite_true hcond0 (by dsimp [Expr.cost]; omega)
            (.seq (.assign he5) (.seq (.assign he6)
              (.ite_false hcond1
                (.seq (.write hi7 hv7 hlen7) (.seq (.write hi8 hv8 hlen8)
                (.seq (.write hi9 hv9 hlen9) (.seq (.assign he10) (.assign he11))))))))))))
      refine ⟨s₁₁, _, hex, by dsimp [Expr.cost]; omega, ?_, ?_, ?_⟩
      · simp only [insertCandidate, beq_iff_eq, hγ, ↓reduceIte]
        have hlen_stored :
            (storedCandidates ({ γ := I.γ, items := [I] } :: B :: rest)).length = m + 1 := by
          rw [length_storedCandidates_cons, ← hm_def]
          dsimp only [List.length_singleton]
          omega
        refine ⟨by simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL1],
          by simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL2],
          by simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL3],
          by simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL4],
          by simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL5],
          by simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL6],
          by simp [s₁₁, s₁₀, b],
          by simp [s₁₁, hlen_stored],
          by simp; omega,
          by rw [hlen_stored]; exact henle, ?_⟩
        dsimp only [StackBlocksOK]
        rw [hb_eq, ← hm_def]
        refine ⟨by simp [s₁₁, s₁₀, s₉, s₈, s₇, List.getElem?_set_self hlen7],
          by simp [s₁₁, s₁₀, s₉, s₈, List.getElem?_set_self hlen8],
          by simp [s₁₁, s₁₀, s₉, List.getElem?_set_self hlen9],
          ?_, ?_⟩
        · intro k hk
          simp only [List.length_singleton] at hk
          have hk0 : k = 0 := by omega
          subst hk0
          simp only [Nat.add_zero, List.getElem_singleton]
          refine ⟨?_, ?_, ?_⟩
          · simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_self hlen1]
          · simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_self
              (show m < (s.arrs aItemR).length by rw [hL5]; omega)]
          · simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_self
              (show m < (s.arrs aItemG).length by rw [hL6]; omega)]
        · have hB_OK : StackBlocksOK (B :: rest) s := ⟨hBG, hBSt, hBEn, hBItems, hRestOK⟩
          refine hB_OK.of_agree_below (fun b' hb' => ?_) (fun b' hb' => ?_)
            (fun b' hb' => ?_) (fun idx hidx => ?_) (fun idx hidx => ?_) (fun idx hidx => ?_)
          · rw [hb_eq] at hb'
            have hne : b + 1 ≠ b' := by omega
            simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
          · rw [hb_eq] at hb'
            have hne : b + 1 ≠ b' := by omega
            simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
          · rw [hb_eq] at hb'
            have hne : b + 1 ≠ b' := by omega
            simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
          · have hne : m ≠ idx := by omega
            simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
          · have hne : m ≠ idx := by omega
            simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
          · have hne : m ≠ idx := by omega
            simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
      · intro r ⟨h1, h2, h3, h4, h5⟩
        simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, h1, h2, h3, h4, h5]
      · intro a ⟨ha1, ha2, ha3, ha4, ha5, ha6⟩
        simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha1, ha2, ha3, ha4, ha5, ha6]



end GraphMinor.Compute
