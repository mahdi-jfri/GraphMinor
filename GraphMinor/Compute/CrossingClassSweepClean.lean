module

public import GraphMinor.Compute.CrossingClassCandSort

/-!
# Cleanup and block lookup

This file implements cleanup and lookup of the bridge-candidate sweep in Section 5.2 of
`docs/crossing/crossing_extractor.tex`. The execution theorems follow the stored candidates and
bound the
number of Word RAM steps.
-/

@[expose] public section

namespace GraphMinor.Compute

open GraphMinor.Crossing

/-! ### 1. Registers and arrays for the block-stack sweep -/

/-- Number of blocks currently on the stack (`st.length`). -/
abbrev rBlkCnt : Reg := 120
/-- Number of candidate items currently stored across all blocks (`(storedCandidates st).length`). -/
abbrev rItemCnt : Reg := 121
/-- Loop index over the sorted candidate array `0 .. rNumCand - 1`. -/
abbrev rSweepIdx : Reg := 122
/-- Flag set to `1` when a crossing pair `(I₁, I₂)` of different colors is found, `0` otherwise. -/
abbrev rSweepFound : Reg := 123
/-- Output candidate `I₁ = (l₁, r₁, γ₁)` when `rSweepFound = 1`. -/
abbrev rOutI1L : Reg := 124
abbrev rOutI1R : Reg := 125
abbrev rOutI1G : Reg := 126
/-- Output candidate `I₂ = (l₂, r₂, γ₂)` when `rSweepFound = 1`. -/
abbrev rOutI2L : Reg := 127
abbrev rOutI2R : Reg := 128
abbrev rOutI2G : Reg := 129
/-- Current candidate `I = (l, r, γ)` being processed. -/
abbrev rCurL : Reg := 130
abbrev rCurR : Reg := 131
abbrev rCurG : Reg := 132
/-- Result of `firstDiffProg`: flag `rDiffFound` and slice `[rDiffSt, rDiffEn)` in `aItem*`. -/
abbrev rDiffFound : Reg := 133
abbrev rDiffSt : Reg := 134
abbrev rDiffEn : Reg := 135
/-- Result of `minRightProg`: candidate `J` attaining the minimum right endpoint in `B`. -/
abbrev rMinL : Reg := 136
abbrev rMinR : Reg := 137
abbrev rMinG : Reg := 138
/-- Scratch registers for sweep item reads. -/
abbrev rCandTmp1 : Reg := 139
abbrev rCandTmp2 : Reg := 140

/-- Block color array `aBlkG[b]`. -/
abbrev aBlkG : Arr := 120
/-- Block start offset array `aBlkSt[b]` into `aItem*`. -/
abbrev aBlkSt : Arr := 121
/-- Block end offset array `aBlkEn[b]` into `aItem*`. -/
abbrev aBlkEn : Arr := 122
/-- Flat item arrays `aItemL[idx]`, `aItemR[idx]`, `aItemG[idx]`. -/
abbrev aItemL : Arr := 123
abbrev aItemR : Arr := 124
abbrev aItemG : Arr := 125

/-! ### 2. Array representation of `st : List Block` -/

/-- Recursive predicate stating that the blocks of `st : List Block` (ordered from top of stack to
bottom of stack) are stored in `aBlkG`, `aBlkSt`, `aBlkEn` at indices `0 .. st.length - 1` (from
bottom to top) and their items are stored contiguously in `aItemL`, `aItemR`, `aItemG` at indices
`0 .. (storedCandidates st).length - 1`. -/
def StackBlocksOK : List Block → State → Prop
  | [], _ => True
  | B :: rest, s =>
    (s.arrs aBlkG)[rest.length]? = some B.γ ∧
    (s.arrs aBlkSt)[rest.length]? = some (storedCandidates rest).length ∧
    (s.arrs aBlkEn)[rest.length]? = some ((storedCandidates rest).length + B.items.length) ∧
    (∀ k (hk : k < B.items.length),
      (s.arrs aItemL)[(storedCandidates rest).length + k]? = some (B.items[k]'hk).l ∧
      (s.arrs aItemR)[(storedCandidates rest).length + k]? = some (B.items[k]'hk).r ∧
      (s.arrs aItemG)[(storedCandidates rest).length + k]? = some (B.items[k]'hk).γ) ∧
    StackBlocksOK rest s

@[simp]
theorem length_storedCandidates_cons (B : Block) (rest : List Block) :
    (storedCandidates (B :: rest)).length = B.items.length + (storedCandidates rest).length := by
  simp [storedCandidates]

theorem StackBlocksOK.of_agree_below {st : List Block} {s s' : State}
    (h : StackBlocksOK st s)
    (hBlkG : ∀ b < st.length, (s'.arrs aBlkG)[b]? = (s.arrs aBlkG)[b]?)
    (hBlkSt : ∀ b < st.length, (s'.arrs aBlkSt)[b]? = (s.arrs aBlkSt)[b]?)
    (hBlkEn : ∀ b < st.length, (s'.arrs aBlkEn)[b]? = (s.arrs aBlkEn)[b]?)
    (hItemL : ∀ idx < (storedCandidates st).length, (s'.arrs aItemL)[idx]? = (s.arrs aItemL)[idx]?)
    (hItemR : ∀ idx < (storedCandidates st).length, (s'.arrs aItemR)[idx]? = (s.arrs aItemR)[idx]?)
    (hItemG : ∀ idx < (storedCandidates st).length, (s'.arrs aItemG)[idx]? = (s.arrs aItemG)[idx]?) :
    StackBlocksOK st s' := by
  induction st with
  | nil => trivial
  | cons B rest ih =>
    rcases h with ⟨hG, hSt, hEn, hItems, hRest⟩
    have hb_lt : rest.length < (B :: rest).length := by simp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hBlkG rest.length hb_lt, hG]
    · rw [hBlkSt rest.length hb_lt, hSt]
    · rw [hBlkEn rest.length hb_lt, hEn]
    · intro k hk
      have hidx_lt : (storedCandidates rest).length + k < (storedCandidates (B :: rest)).length := by
        rw [length_storedCandidates_cons]; omega
      rw [hItemL _ hidx_lt, hItemR _ hidx_lt, hItemG _ hidx_lt]
      exact hItems k hk
    · apply ih hRest
      · intro b hb; exact hBlkG b (by simp; omega)
      · intro b hb; exact hBlkSt b (by simp; omega)
      · intro b hb; exact hBlkEn b (by simp; omega)
      · intro idx hidx; exact hItemL idx (by rw [length_storedCandidates_cons]; omega)
      · intro idx hidx; exact hItemR idx (by rw [length_storedCandidates_cons]; omega)
      · intro idx hidx; exact hItemG idx (by rw [length_storedCandidates_cons]; omega)

theorem StackBlocksOK.setReg {st : List Block} {s : State} (r : Reg) (v : ℕ)
    (h : StackBlocksOK st s) : StackBlocksOK st (s.setReg r v) :=
  h.of_agree_below (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

theorem StackBlocksOK.writeArr_other {st : List Block} {s : State} {a : Arr} (idx val : ℕ)
    (ha : a ≠ aBlkG ∧ a ≠ aBlkSt ∧ a ≠ aBlkEn ∧ a ≠ aItemL ∧ a ≠ aItemR ∧ a ≠ aItemG)
    (h : StackBlocksOK st s) : StackBlocksOK st (s.writeArr a idx val) := by
  rcases ha with ⟨h1, h2, h3, h4, h5, h6⟩
  refine h.of_agree_below (fun _ _ => ?_) (fun _ _ => ?_) (fun _ _ => ?_)
    (fun _ _ => ?_) (fun _ _ => ?_) (fun _ _ => ?_) <;>
    simp [State.writeArr, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6]

/-- Full state predicate for the block stack `st : List Block` with capacity `cap`. -/
def IsBlockStack (cap : ℕ) (st : List Block) (s : State) : Prop :=
  (s.arrs aBlkG).length = cap ∧
  (s.arrs aBlkSt).length = cap ∧
  (s.arrs aBlkEn).length = cap ∧
  (s.arrs aItemL).length = cap ∧
  (s.arrs aItemR).length = cap ∧
  (s.arrs aItemG).length = cap ∧
  s.regs rBlkCnt = st.length ∧
  s.regs rItemCnt = (storedCandidates st).length ∧
  st.length ≤ cap ∧
  (storedCandidates st).length ≤ cap ∧
  StackBlocksOK st s

theorem IsBlockStack.setReg_other {cap : ℕ} {st : List Block} {s : State} (r : Reg) (v : ℕ)
    (hr : r ≠ rBlkCnt ∧ r ≠ rItemCnt) (h : IsBlockStack cap st s) :
    IsBlockStack cap st (s.setReg r v) := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_, h9, h10, h11.setReg r v⟩
  · simp [State.setReg, Ne.symm hr.1, h7]
  · simp [State.setReg, Ne.symm hr.2, h8]

/-! ### 3. Step 1 of the sweep: `cleanStackProg` -/

/-- Filter one item at offset `rM` in the top block during `cleanStackProg`. -/
def cleanItemBody : Cmd :=
  .seq (.assign rCandTmp1 (.op .add (.reg rTmp1) (.reg rM)))
  (.seq (.assign rCandTmp2 (.read aItemR (.reg rCandTmp1)))
  (.ite (.op .lt (.reg rCurL) (.reg rCandTmp2))
    (.seq (.write aItemL (.reg rTmp3) (.read aItemL (.reg rCandTmp1)))
    (.seq (.write aItemR (.reg rTmp3) (.reg rCandTmp2))
    (.seq (.write aItemG (.reg rTmp3) (.read aItemG (.reg rCandTmp1)))
          (.assign rTmp3 (.op .add (.reg rTmp3) (.const 1))))))
    .skip))

/-- Filter the top block of the stack: if all its items expire, pop the block; otherwise update its
end offset `aBlkEn[rG]` and set `rTmp4 := rBlkCnt` to terminate the cleanup loop. -/
def cleanTopBlockBody : Cmd :=
  .seq (.assign rG (.op .sub (.reg rBlkCnt) (.const 1)))
  (.seq (.assign rTmp1 (.read aBlkSt (.reg rG)))
  (.seq (.assign rTmp2 (.op .sub (.read aBlkEn (.reg rG)) (.reg rTmp1)))
  (.seq (.assign rTmp3 (.reg rTmp1))
  (.seq (.assign rM (.const 0))
  (.seq (forUp rM (.reg rTmp2) cleanItemBody)
  (.ite (.op .eq (.reg rTmp3) (.reg rTmp1))
    (.seq (.assign rBlkCnt (.reg rG))
          (.assign rItemCnt (.reg rTmp1)))
    (.seq (.write aBlkEn (.reg rG) (.reg rTmp3))
    (.seq (.assign rItemCnt (.reg rTmp3))
          (.assign rTmp4 (.reg rBlkCnt))))))))))

/-- While loop of `cleanStackProg`. -/
def cleanStackWhile : Cmd :=
  .while (.op .lt (.reg rTmp4) (.reg rBlkCnt)) cleanTopBlockBody

/-- Step 1 of the sweep (`cleanStack`). -/
def cleanStackProg : Cmd :=
  .seq (.assign rTmp4 (.const 0)) cleanStackWhile

/-- Loop invariant for filtering the top block `B` of `B :: rest` at step `k ≤ B.items.length`. -/
private def cleanFilterInv (cap l : ℕ) (B : Block) (rest : List Block) (s₀ : State)
    (k : ℕ) (s : State) : Prop :=
  (s.arrs aBlkG).length = cap ∧
  (s.arrs aBlkSt).length = cap ∧
  (s.arrs aBlkEn).length = cap ∧
  (s.arrs aItemL).length = cap ∧
  (s.arrs aItemR).length = cap ∧
  (s.arrs aItemG).length = cap ∧
  s.regs rBlkCnt = rest.length + 1 ∧
  s.regs rItemCnt = (storedCandidates rest).length + B.items.length ∧
  s.regs rCurL = l ∧
  s.regs rG = rest.length ∧
  s.regs rTmp1 = (storedCandidates rest).length ∧
  s.regs rTmp2 = B.items.length ∧
  s.regs rTmp3 = (storedCandidates rest).length +
    ((B.items.take k).filter (fun J => decide (l < J.r))).length ∧
  s.regs rTmp4 = 0 ∧
  s.regs rM = k ∧
  rest.length + 1 ≤ cap ∧
  (storedCandidates rest).length + B.items.length ≤ cap ∧
  (s.arrs aBlkG)[rest.length]? = some B.γ ∧
  (s.arrs aBlkSt)[rest.length]? = some (storedCandidates rest).length ∧
  (s.arrs aBlkEn)[rest.length]? = some ((storedCandidates rest).length + B.items.length) ∧
  (∀ j (hj : j < ((B.items.take k).filter (fun J => decide (l < J.r))).length),
    (s.arrs aItemL)[(storedCandidates rest).length + j]? =
      some (((B.items.take k).filter (fun J => decide (l < J.r)))[j]'hj).l ∧
    (s.arrs aItemR)[(storedCandidates rest).length + j]? =
      some (((B.items.take k).filter (fun J => decide (l < J.r)))[j]'hj).r ∧
    (s.arrs aItemG)[(storedCandidates rest).length + j]? =
      some (((B.items.take k).filter (fun J => decide (l < J.r)))[j]'hj).γ) ∧
  (∀ j (hj : j < B.items.length), k ≤ j →
    (s.arrs aItemL)[(storedCandidates rest).length + j]? = some (B.items[j]'hj).l ∧
    (s.arrs aItemR)[(storedCandidates rest).length + j]? = some (B.items[j]'hj).r ∧
    (s.arrs aItemG)[(storedCandidates rest).length + j]? = some (B.items[j]'hj).γ) ∧
  StackBlocksOK rest s ∧
  (∀ r, r ≠ rG ∧ r ≠ rM ∧ r ≠ rTmp1 ∧ r ≠ rTmp2 ∧ r ≠ rTmp3 ∧
        r ≠ rCandTmp1 ∧ r ≠ rCandTmp2 → s.regs r = s₀.regs r) ∧
  (∀ a, a ≠ aItemL ∧ a ≠ aItemR ∧ a ≠ aItemG → s.arrs a = s₀.arrs a)

private theorem cleanItemBody_triple {w : ℕ} (cap l : ℕ) (B : Block) (rest : List Block)
    (s₀ : State) (hw : 1 < 2 ^ w) (hcap : cap < 2 ^ w) (hl : l < 2 ^ w)
    (hItemsW : ∀ J ∈ B.items, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w) :
    ∀ k < B.items.length,
      ⦃cleanFilterInv cap l B rest s₀ k⦄[w]
        cleanItemBody
      ⦃fun s' => cleanFilterInv cap l B rest s₀ (k + 1) (s'.setReg rM (k + 1)) ∧ s'.regs rM = k⦄ ≤
        fun _ => 30 := by
  intro k hk s hs
  rcases hs with ⟨hL1, hL2, hL3, hL4, hL5, hL6, hrBlk, hrItem, hrCurL, hrG, hrTmp1, hrTmp2,
    hrTmp3, hrTmp4, hrM, hble, henle, hBG, hBSt, hBEn, hKept, hRem, hRest, hRegs, hArrs⟩
  set b := rest.length
  set st₀ := (storedCandidates rest).length
  set kept := (B.items.take k).filter (fun J => decide (l < J.r))
  have hkept_len : kept.length ≤ k := by
    have h1 : kept.length ≤ (B.items.take k).length := List.length_filter_le _ _
    have h2 : (B.items.take k).length = k := List.length_take_of_le (by omega)
    omega
  set Jk := B.items[k]'hk
  have hJk_mem : Jk ∈ B.items := List.getElem_mem hk
  obtain ⟨hJkl, hJkr, hJkγ⟩ := hItemsW Jk hJk_mem
  obtain ⟨hItemLk, hItemRk, hItemGk⟩ := hRem k hk le_rfl
  have htake_succ : B.items.take (k + 1) = B.items.take k ++ [Jk] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]
    rfl
  let s₁ := s.setReg rCandTmp1 (st₀ + k)
  have he1 : (Expr.op .add (.reg rTmp1) (.reg rM)).eval w s = some (st₀ + k) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrTmp1, hrM,
      show st₀ < 2 ^ w by omega, show k < 2 ^ w by omega, show st₀ + k < 2 ^ w by omega]
  let s₂ := s₁.setReg rCandTmp2 Jk.r
  have he2 : (Expr.read aItemR (.reg rCandTmp1)).eval w s₁ = some Jk.r :=
    read_reg_eval (by simp [s₁]) (by omega) hItemRk hJkr
  by_cases hlt : l < Jk.r
  · have hcond : (Expr.op .lt (.reg rCurL) (.reg rCandTmp2)).eval w s₂ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hrCurL,
        hl, hJkr, hlt, hw]
    let s₃ := s₂.writeArr aItemL (st₀ + kept.length) Jk.l
    have hi3 : (Expr.reg rTmp3).eval w s₂ = some (st₀ + kept.length) := by
      simp [Expr.eval, s₂, s₁, hrTmp3, checkWord, show st₀ + kept.length < 2 ^ w by omega]
    have hv3 : (Expr.read aItemL (.reg rCandTmp1)).eval w s₂ = some Jk.l :=
      read_reg_eval (by simp [s₂, s₁]) (by omega) hItemLk hJkl
    have hlen3 : st₀ + kept.length < (s₂.arrs aItemL).length := by
      simp [s₂, s₁, hL4]; omega
    let s₄ := s₃.writeArr aItemR (st₀ + kept.length) Jk.r
    have hi4 : (Expr.reg rTmp3).eval w s₃ = some (st₀ + kept.length) := by
      simp [Expr.eval, s₃, s₂, s₁, hrTmp3, checkWord, show st₀ + kept.length < 2 ^ w by omega]
    have hv4 : (Expr.reg rCandTmp2).eval w s₃ = some Jk.r := by
      simp [Expr.eval, s₃, s₂, checkWord, hJkr]
    have hlen4 : st₀ + kept.length < (s₃.arrs aItemR).length := by
      simp [s₃, s₂, s₁, hL5]; omega
    let s₅ := s₄.writeArr aItemG (st₀ + kept.length) Jk.γ
    have hi5 : (Expr.reg rTmp3).eval w s₄ = some (st₀ + kept.length) := by
      simp [Expr.eval, s₄, s₃, s₂, s₁, hrTmp3, checkWord, show st₀ + kept.length < 2 ^ w by omega]
    have hItemGk₄ : (s₄.arrs aItemG)[st₀ + k]? = some Jk.γ := by
      simp [s₄, s₃, s₂, s₁, hItemGk, Jk]
    have hv5 : (Expr.read aItemG (.reg rCandTmp1)).eval w s₄ = some Jk.γ :=
      read_reg_eval (by simp [s₄, s₃, s₂, s₁]) (by omega) hItemGk₄ hJkγ
    have hlen5 : st₀ + kept.length < (s₄.arrs aItemG).length := by
      simp [s₄, s₃, s₂, s₁, hL6]; omega
    let s₆ := s₅.setReg rTmp3 (st₀ + kept.length + 1)
    have he6 : (Expr.op .add (.reg rTmp3) (.const 1)).eval w s₅ = some (st₀ + kept.length + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, s₄, s₃, s₂, s₁,
        hrTmp3, hw, show st₀ + kept.length < 2 ^ w by omega, show st₀ + kept.length + 1 < 2 ^ w by omega]
    have hex : Exec w cleanItemBody s s₆ _ :=
      .seq (.assign he1) (.seq (.assign he2)
        (.ite_true hcond (by dsimp [Expr.cost]; omega)
          (.seq (.write hi3 hv3 hlen3)
          (.seq (.write hi4 hv4 hlen4)
          (.seq (.write hi5 hv5 hlen5)
                (.assign he6))))))
    refine ⟨s₆, _, hex, by dsimp [Expr.cost]; omega, ?_, by simp [s₆, s₅, s₄, s₃, s₂, s₁, hrM]⟩
    have hkept_succ : (B.items.take (k + 1)).filter (fun J => decide (l < J.r)) = kept ++ [Jk] := by
      rw [htake_succ, List.filter_append]
      simp [kept, hlt]
    dsimp only [cleanFilterInv]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hble, henle,
      hBG, hBSt, hBEn, ?_, ?_, ?_, ?_, ?_⟩
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, hL1]
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, hL2]
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, hL3]
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, hL4]
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, hL5]
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, hL6]
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, hrBlk, b]
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, hrItem, st₀]
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, hrCurL]
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, hrG, b]
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, hrTmp1, st₀]
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, hrTmp2]
    · rw [hkept_succ]
      simp [s₆, s₅, s₄, s₃, s₂, s₁, st₀]
      omega
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, hrTmp4]
    · simp
    · intro j hj
      simp only [hkept_succ, List.length_append, List.length_singleton] at hj
      by_cases hjk : j < kept.length
      · have hne : st₀ + kept.length ≠ st₀ + j := by omega
        have h1 : ((s₆.setReg rM (k + 1)).arrs aItemL)[st₀ + j]? = (s.arrs aItemL)[st₀ + j]? := by
          simp [s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
        have h2 : ((s₆.setReg rM (k + 1)).arrs aItemR)[st₀ + j]? = (s.arrs aItemR)[st₀ + j]? := by
          simp [s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
        have h3 : ((s₆.setReg rM (k + 1)).arrs aItemG)[st₀ + j]? = (s.arrs aItemG)[st₀ + j]? := by
          simp [s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
        simp only [hkept_succ, List.getElem_append_left hjk]
        rw [h1, h2, h3]
        exact hKept j hjk
      · have hjeq : j = kept.length := by omega
        subst hjeq
        simp only [hkept_succ, List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
        refine ⟨?_, ?_, ?_⟩
        · simp [s₆, s₅, s₄, s₃, s₂, s₁, st₀, List.getElem?_set_self
            (show (storedCandidates rest).length + kept.length < (s.arrs aItemL).length by rw [hL4]; omega)]
        · simp [s₆, s₅, s₄, s₃, s₂, s₁, st₀, List.getElem?_set_self
            (show (storedCandidates rest).length + kept.length < (s.arrs aItemR).length by rw [hL5]; omega)]
        · simp [s₆, s₅, s₄, s₃, s₂, s₁, st₀, List.getElem?_set_self
            (show (storedCandidates rest).length + kept.length < (s.arrs aItemG).length by rw [hL6]; omega)]
    · intro j hj hkj
      have hne : st₀ + kept.length ≠ st₀ + j := by omega
      have h1 : ((s₆.setReg rM (k + 1)).arrs aItemL)[st₀ + j]? = (s.arrs aItemL)[st₀ + j]? := by
        simp [s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
      have h2 : ((s₆.setReg rM (k + 1)).arrs aItemR)[st₀ + j]? = (s.arrs aItemR)[st₀ + j]? := by
        simp [s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
      have h3 : ((s₆.setReg rM (k + 1)).arrs aItemG)[st₀ + j]? = (s.arrs aItemG)[st₀ + j]? := by
        simp [s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
      rw [h1, h2, h3]
      exact hRem j hj (by omega)
    · refine hRest.of_agree_below (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun idx hidx => ?_) (fun idx hidx => ?_) (fun idx hidx => ?_) <;>
      · have hne : st₀ + kept.length ≠ idx := by omega
        simp [s₆, s₅, s₄, s₃, s₂, s₁, List.getElem?_set_ne hne]
    · intro r ⟨h1, h2, h3, h4, h5, h6, h7⟩
      simp [s₆, s₅, s₄, s₃, s₂, s₁, h2, h5, h6, h7,
        hRegs r ⟨h1, h2, h3, h4, h5, h6, h7⟩]
    · intro a ⟨ha1, ha2, ha3⟩
      simp [s₆, s₅, s₄, s₃, s₂, s₁, ha1, ha2, ha3, hArrs a ⟨ha1, ha2, ha3⟩]
  · have hcond : (Expr.op .lt (.reg rCurL) (.reg rCandTmp2)).eval w s₂ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hrCurL,
        hl, hJkr, hlt, show (0 : ℕ) < 2 ^ w by omega]
    have hex : Exec w cleanItemBody s s₂ _ :=
      .seq (.assign he1) (.seq (.assign he2) (.ite_false hcond (.skip s₂)))
    refine ⟨s₂, _, hex, by dsimp [Expr.cost]; omega, ?_, by simp [s₂, s₁, hrM]⟩
    have hkept_succ : (B.items.take (k + 1)).filter (fun J => decide (l < J.r)) = kept := by
      rw [htake_succ, List.filter_append]
      simp [kept, hlt]
    dsimp only [cleanFilterInv]
    refine ⟨hL1, hL2, hL3, hL4, hL5, hL6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hble, henle,
      hBG, hBSt, hBEn, ?_, ?_, hRest.setReg _ _ |>.setReg _ _ |>.setReg _ _, ?_, ?_⟩
    · simp [s₂, s₁, hrBlk, b]
    · simp [s₂, s₁, hrItem, st₀]
    · simp [s₂, s₁, hrCurL]
    · simp [s₂, s₁, hrG, b]
    · simp [s₂, s₁, hrTmp1, st₀]
    · simp [s₂, s₁, hrTmp2]
    · rw [hkept_succ]
      simp [s₂, s₁, hrTmp3, st₀]
    · simp [s₂, s₁, hrTmp4]
    · simp
    · intro j hj
      simp only [hkept_succ] at hj ⊢
      exact hKept j hj
    · intro j hj hkj
      exact hRem j hj (by omega)
    · intro r ⟨h1, h2, h3, h4, h5, h6, h7⟩
      simp [s₂, s₁, h2, h6, h7, hRegs r ⟨h1, h2, h3, h4, h5, h6, h7⟩]
    · intro a ⟨ha1, ha2, ha3⟩
      exact hArrs a ⟨ha1, ha2, ha3⟩

set_option maxHeartbeats 1000000 in
private theorem cleanTopBlockBody_exec {w : ℕ} (cap l : ℕ) (B : Block) (rest : List Block)
    (s : State) (hw : 1 < 2 ^ w) (hcap : cap < 2 ^ w) (hl : l < 2 ^ w)
    (hItemsW : ∀ J ∈ B.items, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w)
    (hst : IsBlockStack cap (B :: rest) s)
    (hCurL : s.regs rCurL = l) (hTmp4 : s.regs rTmp4 = 0) :
    ∃ s' t, Exec w cleanTopBlockBody s s' t ∧
      t ≤ 45 + 37 * B.items.length ∧
      s'.regs rCurL = l ∧
      (∀ r, r ≠ rG ∧ r ≠ rM ∧ r ≠ rTmp1 ∧ r ≠ rTmp2 ∧ r ≠ rTmp3 ∧ r ≠ rTmp4 ∧
            r ≠ rCandTmp1 ∧ r ≠ rCandTmp2 ∧ r ≠ rBlkCnt ∧ r ≠ rItemCnt →
            s'.regs r = s.regs r) ∧
      (∀ a, a ≠ aBlkEn ∧ a ≠ aItemL ∧ a ≠ aItemR ∧ a ≠ aItemG → s'.arrs a = s.arrs a) ∧
      if (B.items.filter (fun J => decide (l < J.r))).isEmpty then
        IsBlockStack cap rest s' ∧ s'.regs rTmp4 = 0
      else
        IsBlockStack cap ({ γ := B.γ, items := B.items.filter (fun J => decide (l < J.r)) } :: rest) s' ∧
        s'.regs rTmp4 = rest.length + 1 := by
  set items' := B.items.filter (fun J => decide (l < J.r))
  rcases hst with ⟨hL1, hL2, hL3, hL4, hL5, hL6, hrBlk, hrItem, hble, henle,
    hBG, hBSt, hBEn, hBItems, hRest⟩
  set b := rest.length with hb_def
  set st₀ := (storedCandidates rest).length with hst₀_def
  have hb_eq : (B :: rest).length = b + 1 := rfl
  have hen_eq : (storedCandidates (B :: rest)).length = st₀ + B.items.length := by
    rw [length_storedCandidates_cons]; omega
  rw [hb_eq] at hrBlk hble
  rw [hen_eq] at hrItem henle
  let s₁ := s.setReg rG b
  have he1 : (Expr.op .sub (.reg rBlkCnt) (.const 1)).eval w s = some b := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrBlk, hw,
      show b + 1 < 2 ^ w by omega, show b < 2 ^ w by omega]
  let s₂ := s₁.setReg rTmp1 st₀
  have he2 : (Expr.read aBlkSt (.reg rG)).eval w s₁ = some st₀ :=
    read_reg_eval (by simp [s₁]) (by omega) hBSt (by omega)
  let s₃ := s₂.setReg rTmp2 B.items.length
  have he3_read : (Expr.read aBlkEn (.reg rG)).eval w s₂ = some (st₀ + B.items.length) :=
    read_reg_eval (by simp [s₂, s₁]) (by omega) hBEn (by omega)
  have he3_1 : (Expr.reg rTmp1).eval w s₂ = some st₀ := by
    simp [Expr.eval, s₂, checkWord, show st₀ < 2 ^ w by omega]
  have he3 : (Expr.op .sub (.read aBlkEn (.reg rG)) (.reg rTmp1)).eval w s₂ = some B.items.length := by
    rw [Expr.eval, he3_read, he3_1]
    simp [BinOp.eval, BinOp.raw, checkWord, show B.items.length < 2 ^ w by omega]
  let s₄ := s₃.setReg rTmp3 st₀
  have he4 : (Expr.reg rTmp1).eval w s₃ = some st₀ := by
    simp [Expr.eval, s₃, s₂, checkWord, show st₀ < 2 ^ w by omega]
  let s₅ := s₄.setReg rM 0
  have he5 : (Expr.const 0).eval w s₄ = some 0 := by
    simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega]
  have hInv0 : cleanFilterInv cap l B rest s 0 s₅ := by
    dsimp only [cleanFilterInv]
    refine ⟨hL1, hL2, hL3, hL4, hL5, hL6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hble, henle, hBG, hBSt, hBEn, ?_, ?_,
      hRest.setReg _ _ |>.setReg _ _ |>.setReg _ _ |>.setReg _ _ |>.setReg _ _, ?_, ?_⟩
    · simp [s₅, s₄, s₃, s₂, s₁, hrBlk, b]
    · simp [s₅, s₄, s₃, s₂, s₁, hrItem, st₀]
    · simp [s₅, s₄, s₃, s₂, s₁, hCurL]
    · simp [s₅, s₄, s₃, s₂, s₁, b]
    · simp [s₅, s₄, s₃, s₂, s₁, st₀]
    · simp [s₅, s₄, s₃, s₂, s₁]
    · simp [s₅, s₄, s₃, s₂, s₁, st₀]
    · simp [s₅, s₄, s₃, s₂, s₁, hTmp4]
    · simp [s₅, s₄, s₃, s₂, s₁]
    · intro j hj; simp at hj
    · intro j hj _; exact hBItems j hj
    · intro r ⟨h1, h2, h3, h4, h5, _⟩
      simp [s₅, s₄, s₃, s₂, s₁, h1, h2, h3, h4, h5]
    · intro a _; rfl
  have hLoop := Triple.forUp_const (r_i := rM) (hi := .reg rTmp2)
    (cleanFilterInv cap l B rest s) B.items.length 30 hw
    (by omega)
    (fun k _ st_k hIk => by
      rcases hIk with ⟨_, _, _, _, _, _, _, _, _, _, _, hr2, _, _, hrM_k, _⟩
      refine ⟨hrM_k, ?_⟩
      simp [Expr.eval, hr2, checkWord, show B.items.length < 2 ^ w by omega])
    (cleanItemBody_triple cap l B rest s hw hcap hl hItemsW)
  rcases hLoop s₅ hInv0 with ⟨s₆, tLoop, hexLoop, htLoop, hInvN⟩
  dsimp only [Expr.cost] at htLoop
  rcases hInvN with ⟨hL1_6, hL2_6, hL3_6, hL4_6, hL5_6, hL6_6, hrBlk_6, hrItem_6, hrCurL_6,
    hrG_6, hrTmp1_6, hrTmp2_6, hrTmp3_6, hrTmp4_6, hrM_6, _, _, hBG_6, hBSt_6, hBEn_6,
    hKept_6, _, hRest_6, hRegs_6, hArrs_6⟩
  have htake_all : (B.items.take B.items.length).filter (fun J => decide (l < J.r)) = items' := by
    rw [List.take_length]
  rw [htake_all, ← hst₀_def] at hrTmp3_6 hKept_6
  rw [← hb_def] at hrBlk_6 hrG_6 hBG_6 hBSt_6 hBEn_6
  rw [← hst₀_def] at hrItem_6 hrTmp1_6 hBSt_6 hBEn_6
  have hitems'_le : items'.length ≤ B.items.length := List.length_filter_le _ _
  by_cases hemp : items'.isEmpty
  · have hlen0 : items'.length = 0 := by
      rw [List.isEmpty_iff.mp hemp, List.length_nil]
    have hcond : (Expr.op .eq (.reg rTmp3) (.reg rTmp1)).eval w s₆ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrTmp3_6, hrTmp1_6, hlen0, hw,
        show st₀ < 2 ^ w by omega]
    let s₇ := s₆.setReg rBlkCnt b
    have he7 : (Expr.reg rG).eval w s₆ = some b := by
      simp [Expr.eval, hrG_6, checkWord, show b < 2 ^ w by omega]
    let s₈ := s₇.setReg rItemCnt st₀
    have he8 : (Expr.reg rTmp1).eval w s₇ = some st₀ := by
      simp [Expr.eval, s₇, hrTmp1_6, checkWord, show st₀ < 2 ^ w by omega]
    have hex : Exec w cleanTopBlockBody s s₈ _ :=
      .seq (.assign he1) (.seq (.assign he2) (.seq (.assign he3) (.seq (.assign he4)
      (.seq (.assign he5) (.seq hexLoop
        (.ite_true hcond (by dsimp [Expr.cost]; omega) (.seq (.assign he7) (.assign he8))))))))
    refine ⟨s₈, _, hex, by dsimp [Expr.cost]; omega,
      by simp [s₈, s₇, hrCurL_6], ?_, ?_, ?_⟩
    · intro r ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      simp [s₈, s₇, h9, h10, hRegs_6 r ⟨h1, h2, h3, h4, h5, h7, h8⟩]
    · intro a ⟨_, ha2, ha3, ha4⟩
      exact hArrs_6 a ⟨ha2, ha3, ha4⟩
    · simp only [hemp, ↓reduceIte]
      refine ⟨⟨hL1_6, hL2_6, hL3_6, hL4_6, hL5_6, hL6_6,
        by simp [s₈, s₇, b], by simp [s₈, s₇, st₀],
        Nat.le_of_succ_le hble, Nat.le_trans (Nat.le_add_right _ _) henle,
        hRest_6.setReg _ _ |>.setReg _ _⟩,
        by simp [s₈, s₇, hrTmp4_6]⟩
  · have hne : items' ≠ [] := List.isEmpty_eq_false_iff.mp (Bool.eq_false_iff.mpr hemp)
    have hcond : (Expr.op .eq (.reg rTmp3) (.reg rTmp1)).eval w s₆ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrTmp3_6, hrTmp1_6, hne,
        show st₀ + items'.length < 2 ^ w by omega, show st₀ < 2 ^ w by omega,
        show (0 : ℕ) < 2 ^ w by omega]
    let s₇ := s₆.writeArr aBlkEn b (st₀ + items'.length)
    have hi7 : (Expr.reg rG).eval w s₆ = some b := by
      simp [Expr.eval, hrG_6, checkWord, show b < 2 ^ w by omega]
    have hv7 : (Expr.reg rTmp3).eval w s₆ = some (st₀ + items'.length) := by
      simp [Expr.eval, hrTmp3_6, checkWord, show st₀ + items'.length < 2 ^ w by omega]
    have hlen7 : b < (s₆.arrs aBlkEn).length := by rw [hL3_6]; omega
    let s₈ := s₇.setReg rItemCnt (st₀ + items'.length)
    have he8 : (Expr.reg rTmp3).eval w s₇ = some (st₀ + items'.length) := by
      simp [Expr.eval, s₇, hrTmp3_6, checkWord, show st₀ + items'.length < 2 ^ w by omega]
    let s₉ := s₈.setReg rTmp4 (b + 1)
    have he9 : (Expr.reg rBlkCnt).eval w s₈ = some (b + 1) := by
      simp [Expr.eval, s₈, s₇, hrBlk_6, checkWord, show b + 1 < 2 ^ w by omega]
    have hex : Exec w cleanTopBlockBody s s₉ _ :=
      .seq (.assign he1) (.seq (.assign he2) (.seq (.assign he3) (.seq (.assign he4)
      (.seq (.assign he5) (.seq hexLoop
        (.ite_false hcond (.seq (.write hi7 hv7 hlen7) (.seq (.assign he8) (.assign he9)))))))))
    refine ⟨s₉, _, hex, by dsimp [Expr.cost]; omega,
      by simp [s₉, s₈, s₇, hrCurL_6], ?_, ?_, ?_⟩
    · intro r ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      simp [s₉, s₈, s₇, h6, h10, hRegs_6 r ⟨h1, h2, h3, h4, h5, h7, h8⟩]
    · intro a ⟨ha1, ha2, ha3, ha4⟩
      simp [s₉, s₈, s₇, ha1, hArrs_6 a ⟨ha2, ha3, ha4⟩]
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
      have hlen_stored :
          (storedCandidates ({ γ := B.γ, items := items' } :: rest)).length = st₀ + items'.length := by
        rw [length_storedCandidates_cons, ← hst₀_def]
        dsimp only
        omega
      refine ⟨⟨hL1_6, hL2_6, by simp [s₉, s₈, s₇, hL3_6],
        hL4_6, hL5_6, hL6_6,
        by simp [s₉, s₈, s₇, hrBlk_6, b],
        by simp [s₉, s₈, s₇, hlen_stored],
        hble, by rw [hlen_stored]; omega, ?_⟩,
        by simp [s₉, s₈, s₇, b]⟩
      refine ⟨hBG_6, hBSt_6, ?_, hKept_6, ?_⟩
      · rw [← hb_def, ← hst₀_def]
        simp [s₉, s₈, s₇, List.getElem?_set_self hlen7]
      · refine hRest_6.of_agree_below (fun _ _ => rfl) (fun _ _ => rfl)
          (fun b' hb' => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        have hne : b ≠ b' := by omega
        simp [s₉, s₈, s₇, List.getElem?_set_ne hne]

/-- Execution of `cleanStackWhile` by structural induction on `st : List Block`. -/
private theorem cleanStackWhile_exec {w : ℕ} (cap l : ℕ) (st : List Block) (s : State)
    (hw : 1 < 2 ^ w) (hcap : cap < 2 ^ w) (hl : l < 2 ^ w)
    (hInv : StackInv st)
    (hItemsW : ∀ J ∈ storedCandidates st, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w)
    (hSix : ∀ B' ∈ cleanStack l st, B'.items.length ≤ 6)
    (hst : IsBlockStack cap st s)
    (hCurL : s.regs rCurL = l) (hTmp4 : s.regs rTmp4 = 0) :
    ∃ s' t, Exec w cleanStackWhile s s' t ∧
      t ≤ 280 + 85 * ((storedCandidates st).length - (storedCandidates (cleanStack l st)).length) ∧
      IsBlockStack cap (cleanStack l st) s' ∧
      s'.regs rCurL = l ∧
      (∀ r, r ≠ rG ∧ r ≠ rM ∧ r ≠ rTmp1 ∧ r ≠ rTmp2 ∧ r ≠ rTmp3 ∧ r ≠ rTmp4 ∧
            r ≠ rCandTmp1 ∧ r ≠ rCandTmp2 ∧ r ≠ rBlkCnt ∧ r ≠ rItemCnt →
            s'.regs r = s.regs r) ∧
      (∀ a, a ≠ aBlkEn ∧ a ≠ aItemL ∧ a ≠ aItemR ∧ a ≠ aItemG → s'.arrs a = s.arrs a) := by
  induction st generalizing s with
  | nil =>
    have hrBlk : s.regs rBlkCnt = 0 := hst.2.2.2.2.2.2.1
    have hcond : (Expr.op .lt (.reg rTmp4) (.reg rBlkCnt)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hTmp4, hrBlk,
        show (0 : ℕ) < 2 ^ w by omega]
    exact ⟨s, 3, .while_false hcond, by omega, hst, hCurL, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons B rest ih =>
    have hrBlk : s.regs rBlkCnt = rest.length + 1 := hst.2.2.2.2.2.2.1
    have hble : rest.length + 1 ≤ cap := hst.2.2.2.2.2.2.2.2.1
    have hcond : (Expr.op .lt (.reg rTmp4) (.reg rBlkCnt)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hTmp4, hrBlk, hw,
        show rest.length + 1 < 2 ^ w by omega]
    have hB_W : ∀ J ∈ B.items, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w := by
      intro J hJ
      apply hItemsW J
      simp [storedCandidates, List.mem_append, hJ]
    have hRest_W : ∀ J ∈ storedCandidates rest, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w := by
      intro J hJ
      apply hItemsW J
      simp only [storedCandidates, List.flatMap_cons, List.mem_append]
      exact Or.inr hJ
    rcases cleanTopBlockBody_exec cap l B rest s hw hcap hl hB_W hst hCurL hTmp4 with
      ⟨s₁, t₁, hex₁, ht₁, hCurL₁, hRegs₁, hArrs₁, hBranch⟩
    set items' := B.items.filter (fun J => decide (l < J.r))
    by_cases hemp : items'.isEmpty
    · simp only [hemp, ↓reduceIte] at hBranch
      rcases hBranch with ⟨hst₁, hTmp4₁⟩
      have hclean_eq : cleanStack l (B :: rest) = cleanStack l rest := by
        simp [cleanStack, items', hemp]
      have hSix_rest : ∀ B' ∈ cleanStack l rest, B'.items.length ≤ 6 := by
        rwa [← hclean_eq]
      rcases ih s₁ hInv.tail hRest_W hSix_rest hst₁ hCurL₁ hTmp4₁ with
        ⟨s₂, t₂, hex₂, ht₂, hst₂, hCurL₂, hRegs₂, hArrs₂⟩
      have hB_pos : 0 < B.items.length :=
        List.length_pos_of_ne_nil (hInv.wf B List.mem_cons_self).1
      have hsub_len : (storedCandidates (cleanStack l rest)).length ≤ (storedCandidates rest).length :=
        (storedCandidates_cleanStack_sublist l rest).length_le
      refine ⟨s₂, 3 + t₁ + t₂, .while_true hcond (by omega) hex₁ hex₂, ?_,
        by rwa [hclean_eq], hCurL₂,
        fun r hr => (hRegs₂ r hr).trans (hRegs₁ r hr),
        fun a ha => (hArrs₂ a ha).trans (hArrs₁ a ha)⟩
      rw [hclean_eq, length_storedCandidates_cons]
      omega
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at hBranch
      rcases hBranch with ⟨hst₁, hTmp4₁⟩
      have hclean_eq : cleanStack l (B :: rest) = { γ := B.γ, items := items' } :: rest := by
        simp [cleanStack, items', hemp]
      have hrBlk₁ : s₁.regs rBlkCnt = rest.length + 1 := hst₁.2.2.2.2.2.2.1
      have hcond₂ : (Expr.op .lt (.reg rTmp4) (.reg rBlkCnt)).eval w s₁ = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hTmp4₁, hrBlk₁,
          show rest.length + 1 < 2 ^ w by omega, show (0 : ℕ) < 2 ^ w by omega]
      have hitems'_six : items'.length ≤ 6 := by
        apply hSix { γ := B.γ, items := items' }
        rw [hclean_eq]
        exact List.mem_cons_self
      have hitems'_le : items'.length ≤ B.items.length := List.length_filter_le _ _
      refine ⟨s₁, 3 + t₁ + 3, .while_true hcond (by omega) hex₁ (.while_false hcond₂), ?_,
        by rwa [hclean_eq], hCurL₁, hRegs₁, hArrs₁⟩
      rw [hclean_eq, length_storedCandidates_cons, length_storedCandidates_cons]
      dsimp only
      omega

/-- Total-correctness specification of `cleanStackProg`. -/
theorem cleanStackProg_exec {w : ℕ} (cap l : ℕ) (st : List Block) (s : State)
    (hw : 1 < 2 ^ w) (hcap : cap < 2 ^ w) (hl : l < 2 ^ w)
    (hInv : StackInv st)
    (hItemsW : ∀ J ∈ storedCandidates st, J.l < 2 ^ w ∧ J.r < 2 ^ w ∧ J.γ < 2 ^ w)
    (hSix : ∀ B' ∈ cleanStack l st, B'.items.length ≤ 6)
    (hst : IsBlockStack cap st s)
    (hCurL : s.regs rCurL = l) :
    ∃ s' t, Exec w cleanStackProg s s' t ∧
      t ≤ 285 + 85 * ((storedCandidates st).length - (storedCandidates (cleanStack l st)).length) ∧
      IsBlockStack cap (cleanStack l st) s' ∧
      s'.regs rCurL = l ∧
      (∀ r, r ≠ rG ∧ r ≠ rM ∧ r ≠ rTmp1 ∧ r ≠ rTmp2 ∧ r ≠ rTmp3 ∧ r ≠ rTmp4 ∧
            r ≠ rCandTmp1 ∧ r ≠ rCandTmp2 ∧ r ≠ rBlkCnt ∧ r ≠ rItemCnt →
            s'.regs r = s.regs r) ∧
      (∀ a, a ≠ aBlkEn ∧ a ≠ aItemL ∧ a ≠ aItemR ∧ a ≠ aItemG → s'.arrs a = s.arrs a) := by
  let s₀ := s.setReg rTmp4 0
  have he0 : (Expr.const 0).eval w s = some 0 := by
    simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega]
  have hst₀ : IsBlockStack cap st s₀ :=
    hst.setReg_other rTmp4 0 ⟨by decide, by decide⟩
  have hCurL₀ : s₀.regs rCurL = l := by simp [s₀, hCurL]
  have hTmp4₀ : s₀.regs rTmp4 = 0 := by simp [s₀]
  rcases cleanStackWhile_exec cap l st s₀ hw hcap hl hInv hItemsW hSix hst₀ hCurL₀ hTmp4₀ with
    ⟨s', t, hex, ht, hst', hCurL', hRegs, hArrs⟩
  refine ⟨s', _, .seq (.assign he0) hex, by dsimp [Expr.cost]; omega, hst', hCurL', ?_, hArrs⟩
  intro r hr
  rw [hRegs r hr]
  simp [s₀, hr.2.2.2.2.2.1]

/-! ### 4. Step 2 of the sweep: `firstDiffProg` -/

/-- Step 2 of the sweep (`firstDiffBlock`): inspect the top block and (if its color equals
`rCurG`) the second block from the top, setting `rDiffFound`, `rDiffSt`, and `rDiffEn`. -/
def firstDiffProg : Cmd :=
  .seq (.assign rDiffFound (.const 0))
  (.seq (.assign rDiffSt (.const 0))
  (.seq (.assign rDiffEn (.const 0))
  (.ite (.op .lt (.const 0) (.reg rBlkCnt))
    (.seq (.assign rG (.op .sub (.reg rBlkCnt) (.const 1)))
    (.seq (.assign rTmp1 (.read aBlkG (.reg rG)))
    (.ite (.op .eq (.reg rTmp1) (.reg rCurG))
      (.ite (.op .lt (.const 1) (.reg rBlkCnt))
        (.seq (.assign rM (.op .sub (.reg rBlkCnt) (.const 2)))
        (.seq (.assign rTmp2 (.read aBlkG (.reg rM)))
        (.ite (.op .eq (.reg rTmp2) (.reg rCurG))
          .skip
          (.seq (.assign rDiffFound (.const 1))
          (.seq (.assign rDiffSt (.read aBlkSt (.reg rM)))
                (.assign rDiffEn (.read aBlkEn (.reg rM))))))))
        .skip)
      (.seq (.assign rDiffFound (.const 1))
      (.seq (.assign rDiffSt (.read aBlkSt (.reg rG)))
            (.assign rDiffEn (.read aBlkEn (.reg rG))))))))
    .skip)))

/-- Specification of `firstDiffProg`. -/
theorem firstDiffProg_exec {w : ℕ} (cap γ : ℕ) (st : List Block) (s : State)
    (hw : 1 < 2 ^ w) (hcap : cap < 2 ^ w) (hγ : γ < 2 ^ w)
    (hBlkW : ∀ B ∈ st, B.γ < 2 ^ w)
    (hst : IsBlockStack cap st s)
    (hCurG : s.regs rCurG = γ) :
    ∃ s' t, Exec w firstDiffProg s s' t ∧
      t ≤ 40 ∧
      IsBlockStack cap st s' ∧
      (∀ r, r ≠ rDiffFound ∧ r ≠ rDiffSt ∧ r ≠ rDiffEn ∧ r ≠ rG ∧ r ≠ rM ∧ r ≠ rTmp1 ∧ r ≠ rTmp2 →
        s'.regs r = s.regs r) ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      match firstDiffBlock γ st with
      | none => s'.regs rDiffFound = 0
      | some B =>
        s'.regs rDiffFound = 1 ∧
        ∃ st₀, s'.regs rDiffSt = st₀ ∧
          s'.regs rDiffEn = st₀ + B.items.length ∧
          st₀ + B.items.length ≤ cap ∧
          ∀ k (hk : k < B.items.length),
            let J := B.items[k]'hk
            (s'.arrs aItemL)[st₀ + k]? = some J.l ∧
            (s'.arrs aItemR)[st₀ + k]? = some J.r ∧
            (s'.arrs aItemG)[st₀ + k]? = some J.γ := by
  have hrBlk : s.regs rBlkCnt = st.length := hst.2.2.2.2.2.2.1
  have hble : st.length ≤ cap := hst.2.2.2.2.2.2.2.2.1
  have henle : (storedCandidates st).length ≤ cap := hst.2.2.2.2.2.2.2.2.2.1
  let s₁ := s.setReg rDiffFound 0
  have he1 : (Expr.const 0).eval w s = some 0 := by
    simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega]
  let s₂ := s₁.setReg rDiffSt 0
  have he2 : (Expr.const 0).eval w s₁ = some 0 := he1
  let s₃ := s₂.setReg rDiffEn 0
  have he3 : (Expr.const 0).eval w s₂ = some 0 := he1
  have hst₃ : IsBlockStack cap st s₃ :=
    hst.setReg_other _ _ ⟨by decide, by decide⟩
      |>.setReg_other _ _ ⟨by decide, by decide⟩
      |>.setReg_other _ _ ⟨by decide, by decide⟩
  cases st with
  | nil =>
    have hcond0 : (Expr.op .lt (.const 0) (.reg rBlkCnt)).eval w s₃ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hrBlk,
        show (0 : ℕ) < 2 ^ w by omega]
    have hex : Exec w firstDiffProg s s₃ _ :=
      .seq (.assign he1) (.seq (.assign he2) (.seq (.assign he3)
        (.ite_false hcond0 (.skip s₃))))
    refine ⟨s₃, _, hex, by dsimp [Expr.cost]; omega, hst₃, ?_, fun _ => rfl,
      by simp [firstDiffBlock, s₃, s₂, s₁]⟩
    intro r ⟨h1, h2, h3, _⟩
    simp [s₃, s₂, s₁, h1, h2, h3]
  | cons B₁ rest =>
    have hb₁_len : (B₁ :: rest).length = rest.length + 1 := rfl
    have hB₁_W : B₁.γ < 2 ^ w := hBlkW B₁ List.mem_cons_self
    rcases hst.2.2.2.2.2.2.2.2.2.2 with ⟨hB₁G, hB₁St, hB₁En, hB₁Items, hRestOK⟩
    have hcond0 : (Expr.op .lt (.const 0) (.reg rBlkCnt)).eval w s₃ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hrBlk, hb₁_len,
        hw, show rest.length + 1 < 2 ^ w by omega]
    let s₄ := s₃.setReg rG rest.length
    have he4 : (Expr.op .sub (.reg rBlkCnt) (.const 1)).eval w s₃ = some rest.length := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hrBlk, hb₁_len,
        hw, show rest.length + 1 < 2 ^ w by omega, show rest.length < 2 ^ w by omega]
    let s₅ := s₄.setReg rTmp1 B₁.γ
    have he5 : (Expr.read aBlkG (.reg rG)).eval w s₄ = some B₁.γ :=
      read_reg_eval (by simp [s₄]) (by omega) hB₁G hB₁_W
    have hst₅ : IsBlockStack cap (B₁ :: rest) s₅ :=
      hst₃.setReg_other _ _ ⟨by decide, by decide⟩
        |>.setReg_other _ _ ⟨by decide, by decide⟩
    by_cases hγ1 : B₁.γ = γ
    · have hcond1 : (Expr.op .eq (.reg rTmp1) (.reg rCurG)).eval w s₅ = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, s₄, s₃, s₂, s₁,
          hCurG, hγ1, hγ, hw]
      cases rest with
      | nil =>
        have hcond2 : (Expr.op .lt (.const 1) (.reg rBlkCnt)).eval w s₅ = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, s₄, s₃, s₂, s₁,
            hrBlk, hb₁_len, hw, show (0 : ℕ) < 2 ^ w by omega]
        have hex : Exec w firstDiffProg s s₅ _ :=
          .seq (.assign he1) (.seq (.assign he2) (.seq (.assign he3)
            (.ite_true hcond0 (by dsimp [Expr.cost]; omega)
              (.seq (.assign he4) (.seq (.assign he5)
                (.ite_true hcond1 (by dsimp [Expr.cost]; omega) (.ite_false hcond2 (.skip s₅))))))))
        refine ⟨s₅, _, hex, by dsimp [Expr.cost]; omega, hst₅, ?_, fun _ => rfl, ?_⟩
        · intro r ⟨h1, h2, h3, h4, _, h6, _⟩
          simp [s₅, s₄, s₃, s₂, s₁, h1, h2, h3, h4, h6]
        · simp [firstDiffBlock, hγ1, s₅, s₄, s₃, s₂, s₁]
      | cons B₂ rest' =>
        have hb₂_len : (B₁ :: B₂ :: rest').length = rest'.length + 2 := rfl
        have hB₂_W : B₂.γ < 2 ^ w := hBlkW B₂ (List.mem_cons_of_mem B₁ List.mem_cons_self)
        rcases hRestOK with ⟨hB₂G, hB₂St, hB₂En, hB₂Items, _⟩
        have hcond2 : (Expr.op .lt (.const 1) (.reg rBlkCnt)).eval w s₅ = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, s₄, s₃, s₂, s₁,
            hrBlk, hb₂_len, hw, show rest'.length + 2 < 2 ^ w by omega]
        let s₆ := s₅.setReg rM rest'.length
        have he6 : (Expr.op .sub (.reg rBlkCnt) (.const 2)).eval w s₅ = some rest'.length := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, s₄, s₃, s₂, s₁,
            hrBlk, hb₂_len, show (2 : ℕ) < 2 ^ w by omega,
            show rest'.length + 2 < 2 ^ w by omega, show rest'.length < 2 ^ w by omega]
        let s₇ := s₆.setReg rTmp2 B₂.γ
        have he7 : (Expr.read aBlkG (.reg rM)).eval w s₆ = some B₂.γ :=
          read_reg_eval (by simp [s₆]) (by omega) hB₂G hB₂_W
        have hst₇ : IsBlockStack cap (B₁ :: B₂ :: rest') s₇ :=
          hst₅.setReg_other _ _ ⟨by decide, by decide⟩
            |>.setReg_other _ _ ⟨by decide, by decide⟩
        by_cases hγ2 : B₂.γ = γ
        · have hcond3 : (Expr.op .eq (.reg rTmp2) (.reg rCurG)).eval w s₇ = some 1 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
              hCurG, hγ2, hγ, hw]
          have hex : Exec w firstDiffProg s s₇ _ :=
            .seq (.assign he1) (.seq (.assign he2) (.seq (.assign he3)
              (.ite_true hcond0 (by dsimp [Expr.cost]; omega)
                (.seq (.assign he4) (.seq (.assign he5)
                  (.ite_true hcond1 (by dsimp [Expr.cost]; omega)
                    (.ite_true hcond2 (by dsimp [Expr.cost]; omega)
                      (.seq (.assign he6) (.seq (.assign he7)
                        (.ite_true hcond3 (by dsimp [Expr.cost]; omega) (.skip s₇)))))))))))
          refine ⟨s₇, _, hex, by dsimp [Expr.cost]; omega, hst₇, ?_, fun _ => rfl, ?_⟩
          · intro r ⟨h1, h2, h3, h4, h5, h6, h7⟩
            simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, h1, h2, h3, h4, h5, h6, h7]
          · simp [firstDiffBlock, hγ1, hγ2, s₇, s₆, s₅, s₄, s₃, s₂, s₁]
        · have hcond3 : (Expr.op .eq (.reg rTmp2) (.reg rCurG)).eval w s₇ = some 0 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
              hCurG, hγ2, hB₂_W, hγ, show (0 : ℕ) < 2 ^ w by omega]
          set st₀ := (storedCandidates rest').length
          have hen₀_le : st₀ + B₂.items.length ≤ cap := by
            simp only [length_storedCandidates_cons] at henle; omega
          let s₈ := s₇.setReg rDiffFound 1
          have he8 : (Expr.const 1).eval w s₇ = some 1 := by simp [Expr.eval, checkWord, hw]
          let s₉ := s₈.setReg rDiffSt st₀
          have he9 : (Expr.read aBlkSt (.reg rM)).eval w s₈ = some st₀ :=
            read_reg_eval (by simp [s₈, s₇, s₆]) (by omega) hB₂St (by omega)
          let s₁₀ := s₉.setReg rDiffEn (st₀ + B₂.items.length)
          have he10 : (Expr.read aBlkEn (.reg rM)).eval w s₉ = some (st₀ + B₂.items.length) :=
            read_reg_eval (by simp [s₉, s₈, s₇, s₆]) (by omega) hB₂En (by omega)
          have hst₁₀ : IsBlockStack cap (B₁ :: B₂ :: rest') s₁₀ :=
            hst₇.setReg_other _ _ ⟨by decide, by decide⟩
              |>.setReg_other _ _ ⟨by decide, by decide⟩
              |>.setReg_other _ _ ⟨by decide, by decide⟩
          have hex : Exec w firstDiffProg s s₁₀ _ :=
            .seq (.assign he1) (.seq (.assign he2) (.seq (.assign he3)
              (.ite_true hcond0 (by dsimp [Expr.cost]; omega)
                (.seq (.assign he4) (.seq (.assign he5)
                  (.ite_true hcond1 (by dsimp [Expr.cost]; omega)
                    (.ite_true hcond2 (by dsimp [Expr.cost]; omega)
                      (.seq (.assign he6) (.seq (.assign he7)
                        (.ite_false hcond3
                          (.seq (.assign he8) (.seq (.assign he9) (.assign he10)))))))))))))
          refine ⟨s₁₀, _, hex, by dsimp [Expr.cost]; omega, hst₁₀, ?_, fun _ => rfl, ?_⟩
          · intro r ⟨h1, h2, h3, h4, h5, h6, h7⟩
            simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, h1, h2, h3, h4, h5, h6, h7]
          · simp only [firstDiffBlock, hγ1, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              bne_iff_ne, ne_eq, hγ2, not_false_eq_true]
            refine ⟨by simp [s₁₀, s₉, s₈], st₀,
              by simp [s₁₀, s₉], by simp [s₁₀], hen₀_le, hB₂Items⟩
    · have hcond1 : (Expr.op .eq (.reg rTmp1) (.reg rCurG)).eval w s₅ = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, s₄, s₃, s₂, s₁,
          hCurG, hγ1, hB₁_W, hγ, show (0 : ℕ) < 2 ^ w by omega]
      set st₀ := (storedCandidates rest).length
      have hen₀_le : st₀ + B₁.items.length ≤ cap := by
        simp only [length_storedCandidates_cons] at henle; omega
      let s₆ := s₅.setReg rDiffFound 1
      have he6 : (Expr.const 1).eval w s₅ = some 1 := by simp [Expr.eval, checkWord, hw]
      let s₇ := s₆.setReg rDiffSt st₀
      have he7 : (Expr.read aBlkSt (.reg rG)).eval w s₆ = some st₀ :=
        read_reg_eval (by simp [s₆, s₅, s₄]) (by omega) hB₁St (by omega)
      let s₈ := s₇.setReg rDiffEn (st₀ + B₁.items.length)
      have he8 : (Expr.read aBlkEn (.reg rG)).eval w s₇ = some (st₀ + B₁.items.length) :=
        read_reg_eval (by simp [s₇, s₆, s₅, s₄]) (by omega) hB₁En (by omega)
      have hst₈ : IsBlockStack cap (B₁ :: rest) s₈ :=
        hst₅.setReg_other _ _ ⟨by decide, by decide⟩
          |>.setReg_other _ _ ⟨by decide, by decide⟩
          |>.setReg_other _ _ ⟨by decide, by decide⟩
      have hex : Exec w firstDiffProg s s₈ _ :=
        .seq (.assign he1) (.seq (.assign he2) (.seq (.assign he3)
          (.ite_true hcond0 (by dsimp [Expr.cost]; omega)
            (.seq (.assign he4) (.seq (.assign he5)
              (.ite_false hcond1
                (.seq (.assign he6) (.seq (.assign he7) (.assign he8)))))))))
      refine ⟨s₈, _, hex, by dsimp [Expr.cost]; omega, hst₈, ?_, fun _ => rfl, ?_⟩
      · intro r ⟨h1, h2, h3, h4, _, h6, _⟩
        simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, h1, h2, h3, h4, h6]
      · simp only [firstDiffBlock, bne_iff_ne, ne_eq, hγ1, not_false_eq_true, ↓reduceIte]
        refine ⟨by simp [s₈, s₇, s₆], st₀,
          by simp [s₈, s₇], by simp [s₈], hen₀_le, hB₁Items⟩


end GraphMinor.Compute
