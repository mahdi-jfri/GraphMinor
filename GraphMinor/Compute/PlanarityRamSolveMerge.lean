module

public import GraphMinor.Compute.PlanarityRamSolveOld

/-!
# The anchor step and the final push of `MERGE`

Between its two loops, `MERGE(S,T)` of Part I, Section 4 of the planarity note
moves the anchor of `T`:

    if b=a: append T.A to S.A
    else:   append T.A to R

and after the second loop it ends with

    if L or R is nonempty: push (L,R) onto S.P

This file gives the RAM programs of these two steps, `anchorProg` and
`pushProg`, and their specifications `anchorProg_spec` and `pushProg_spec`.
The summary pointers of `S` and `T` are in registers 57 and 61, `b` is in
register 62, and the next free block address is in register 54.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The anchor step: load the anchor headers of `S` and `T` and the least
depth of `S`, append the anchor of `T` to that of `S` or to `R`, and store the
anchor header of `S` back. -/
def anchorProg : Cmd :=
  .seq (.seq (.assign 65 (.read Field.summaryFirst.array (.reg 57)))
      (.seq (.assign 66 (.read Field.summaryLast.array (.reg 57)))
        (.seq (.assign 68 (.read Field.summaryFirst.array (.reg 61)))
          (.seq (.assign 69 (.read Field.summaryLast.array (.reg 61)))
            (.assign 72 (.read Field.summaryLeast.array (.reg 57)))))))
    (.seq (.ite (.op .eq (.reg 72) (.reg 62)) (appendProg 65 66 68 69)
        (appendProg 63 64 68 69))
      (.seq (.write Field.summaryFirst.array (.reg 57) (.reg 65))
        (.write Field.summaryLast.array (.reg 57) (.reg 66))))

/-- The cells that the anchor step may write. -/
def AnchorCells (pS : ℕ) (P : List ℕ) (a q : ℕ) : Prop :=
  a = Field.nodeNext.array ∧ q ∈ P ∨
    (a = Field.summaryFirst.array ∨ a = Field.summaryLast.array) ∧ q = pS

/-- Part I, Section 4: "if b=a: append T.A to S.A else: append T.A to R". -/
theorem anchorProg_spec {w D cap : ℕ} {s : State} {pS pT fS lS fT lT a b : ℕ}
    {AS AT RA : List ℕ} {x y right : List ReturnNode}
    (h57 : s.regs 57 = pS) (h61 : s.regs 61 = pT) (h62 : s.regs 62 = b)
    (hSf : (s.arrs Field.summaryFirst.array)[pS]? = some fS)
    (hSl : (s.arrs Field.summaryLast.array)[pS]? = some lS)
    (hSm : (s.arrs Field.summaryLeast.array)[pS]? = some a)
    (hTf : (s.arrs Field.summaryFirst.array)[pT]? = some fT)
    (hTl : (s.arrs Field.summaryLast.array)[pT]? = some lT)
    (hAS : ListAt s cap fS lS AS x) (hAT : ListAt s cap fT lT AT y)
    (hR : ListAt s cap (s.regs 63) (s.regs 64) RA right)
    (hd1 : ∀ q ∈ AS, q ∉ AT) (hd2 : ∀ q ∈ RA, q ∉ AT) (hd3 : ∀ q ∈ AS, q ∉ RA)
    (hpS : pS ≤ D) (hpT : pT ≤ D) (hb : b ≤ D) (hW : Words D s)
    (hcap : 0 < cap) (hcapD : cap ≤ D + 1) (hD : D + 2 < 2 ^ w) :
    ∃ s' t, Exec w anchorProg s s' t ∧ t ≤ 40 ∧
      ListAt s' cap (s'.regs 65) (s'.regs 66) (if b = a then AS ++ AT else AS)
        (if b = a then x ++ y else x) ∧
      ListAt s' cap (s'.regs 63) (s'.regs 64) (if b = a then RA else RA ++ AT)
        (if b = a then right else right ++ y) ∧
      (s'.arrs Field.summaryFirst.array)[pS]? = some (s'.regs 65) ∧
      (s'.arrs Field.summaryLast.array)[pS]? = some (s'.regs 66) ∧
      Frame s s' (AnchorCells pS (AS ++ RA)) ∧ Words D s' ∧
      (∀ r, r ∉ anchorProg.writtenRegs → s'.regs r = s.regs r) := by
  have hpSw : s.regs 57 < 2 ^ w := by omega
  have hpTw : s.regs 61 < 2 ^ w := by omega
  have hfSD := hW.get (by simp [Field.array]) (by simp [Field.array]) hSf
  have hlSD := hW.get (by simp [Field.array]) (by simp [Field.array]) hSl
  have hfTD := hW.get (by simp [Field.array]) (by simp [Field.array]) hTf
  have hlTD := hW.get (by simp [Field.array]) (by simp [Field.array]) hTl
  have haD := hW.get (by simp [Field.array]) (by simp [Field.array]) hSm
  rw [← h57] at hSf hSl hSm
  rw [← h61] at hTf hTl
  let s₅ := ((((s.setReg 65 fS).setReg 66 lS).setReg 68 fT).setReg 69 lT).setReg 72 a
  have hx₅ : Exec w (.seq (.assign 65 (.read Field.summaryFirst.array (.reg 57)))
      (.seq (.assign 66 (.read Field.summaryLast.array (.reg 57)))
        (.seq (.assign 68 (.read Field.summaryFirst.array (.reg 61)))
          (.seq (.assign 69 (.read Field.summaryLast.array (.reg 61)))
            (.assign 72 (.read Field.summaryLeast.array (.reg 57))))))) s s₅ 15 :=
    Exec.seq (exec_ld hpSw hSf (by omega)) (Exec.seq (exec_ld (by simpa using hpSw)
      (by simpa using hSl) (by omega)) (Exec.seq (exec_ld (by simpa using hpTw)
        (by simpa using hTf) (by omega)) (Exec.seq (exec_ld (by simpa using hpTw)
          (by simpa using hTl) (by omega)) (exec_ld (by simpa using hpSw) (by simpa using hSm)
            (by omega)))))
  have harr₅ : s₅.arrs = s.arrs := rfl
  have hW₅ : Words D s₅ := hW
  have hS₅ : ListAt s₅ cap (s₅.regs 65) (s₅.regs 66) AS x := by
    simpa [s₅] using hAS.of_arrs_eq harr₅
  have hT₅ : ListAt s₅ cap (s₅.regs 68) (s₅.regs 69) AT y := by
    simpa [s₅] using hAT.of_arrs_eq harr₅
  have hR₅ : ListAt s₅ cap (s₅.regs 63) (s₅.regs 64) RA right := by
    simpa [s₅] using hR.of_arrs_eq harr₅
  have heq : (Expr.op .eq (.reg 72) (.reg 62)).eval w s₅ = some (if a = b then 1 else 0) := by
    rw [eval_op (eval_reg (by simp [s₅]; omega)) (eval_reg (by simp [s₅]; omega)),
      binop_eq (by omega)]
    simp [s₅, h62]
  -- The conditional append.
  obtain ⟨s₆, t₆, hx₆, ht₆, hA₆, hR₆, hF₆, hW₆, hregs₆⟩ : ∃ s₆ t₆,
      Exec w (.ite (.op .eq (.reg 72) (.reg 62)) (appendProg 65 66 68 69)
        (appendProg 63 64 68 69)) s₅ s₆ t₆ ∧ t₆ ≤ 10 ∧
      ListAt s₆ cap (s₆.regs 65) (s₆.regs 66) (if b = a then AS ++ AT else AS)
        (if b = a then x ++ y else x) ∧
      ListAt s₆ cap (s₆.regs 63) (s₆.regs 64) (if b = a then RA else RA ++ AT)
        (if b = a then right else right ++ y) ∧
      Frame s₅ s₆ (fun a q => a = Field.nodeNext.array ∧ q ∈ AS ++ RA) ∧ Words D s₆ ∧
      (∀ r, r ≠ 63 → r ≠ 64 → r ≠ 65 → r ≠ 66 → s₆.regs r = s₅.regs r) := by
    by_cases hab : b = a
    · obtain ⟨s₆, t₆, hx, ht, hA, hF, hregs, hW'⟩ := appendProg_spec (w := w) (D := D)
        (fA := 65) (lA := 66) (fB := 68) (lB := 69) (by decide) (by decide) hS₅ hT₅ hd1 hcap
        hcapD (by omega) hW₅
      refine ⟨s₆, _, exec_ite_eval heq (fun _ => hx) (fun h => by simp [hab] at h), by simp; omega,
        by simpa [hab] using hA, ?_, hF.mono (fun _ _ h => ⟨h.1, List.mem_append_left _ h.2⟩), hW',
        fun r _ _ h1 h2 => hregs r h1 h2⟩
      simp only [hab, ↓reduceIte]
      rw [hregs 63 (by decide) (by decide), hregs 64 (by decide) (by decide)]
      exact hR₅.frame_next hF (fun q hq hs => hd3 q hs hq)
    · obtain ⟨s₆, t₆, hx, ht, hA, hF, hregs, hW'⟩ := appendProg_spec (w := w) (D := D)
        (fA := 63) (lA := 64) (fB := 68) (lB := 69) (by decide) (by decide) hR₅ hT₅ hd2 hcap
        hcapD (by omega) hW₅
      refine ⟨s₆, _, exec_ite_eval heq (fun h => by simp [Ne.symm hab] at h) (fun _ => hx),
        by simp; omega, ?_, by simpa [hab] using hA,
        hF.mono (fun _ _ h => ⟨h.1, List.mem_append_right _ h.2⟩), hW',
        fun r h1 h2 _ _ => hregs r h1 h2⟩
      simp only [hab, ↓reduceIte]
      rw [hregs 65 (by decide) (by decide), hregs 66 (by decide) (by decide)]
      exact hS₅.frame_next hF hd3
  -- Store the anchor header of `S`.
  have h57₆ : s₆.regs 57 = pS := by
    rw [hregs₆ 57 (by decide) (by decide) (by decide) (by decide)]
    simp [s₅, h57]
  have hlen₆ : pS < (s₆.arrs Field.summaryFirst.array).length := by
    rw [(hF₆ _).1, harr₅]
    exact (List.getElem?_eq_some_iff.mp (h57 ▸ hSf)).1
  have hlen₆' : pS < (s₆.arrs Field.summaryLast.array).length := by
    rw [(hF₆ _).1, harr₅]
    exact (List.getElem?_eq_some_iff.mp (h57 ▸ hSl)).1
  have hp65 := hA₆.pointers_lt hcap
  let s₇ := s₆.writeArr Field.summaryFirst.array pS (s₆.regs 65)
  let s₈ := s₇.writeArr Field.summaryLast.array pS (s₆.regs 66)
  have hx₈ : Exec w (.seq (.write Field.summaryFirst.array (.reg 57) (.reg 65))
      (.write Field.summaryLast.array (.reg 57) (.reg 66))) s₆ s₈ 6 := by
    have h1 := exec_st (w := w) (s := s₆) (a := Field.summaryFirst.array) (idx := 57) (val := 65)
      (by rw [h57₆]; exact hlen₆) (by rw [h57₆]; omega) (by omega)
    have h2 := exec_st (w := w) (s := s₇) (a := Field.summaryLast.array) (idx := 57) (val := 66)
      (by simp only [s₇, State.writeArr_regs, h57₆]
          rw [State.writeArr_arrs_ne _ _ _ (by simp [Field.array])]
          exact hlen₆') (by simp [s₇, h57₆]; omega) (by simp [s₇]; omega)
    rw [h57₆] at h1
    simpa [s₇, h57₆] using Exec.seq h1 h2
  have hFw : Frame s₆ s₈ (fun a q => (a = Field.summaryFirst.array ∨
      a = Field.summaryLast.array) ∧ q = pS) :=
    ((Frame.writeArr s₆ _ _ _).trans (Frame.writeArr s₇ _ _ _)).mono
      (fun a q h => by rcases h with h | h <;> simp [h.1, h.2])
  have hnodes : ∀ q, ¬ NodeCell (fun a q => (a = Field.summaryFirst.array ∨
      a = Field.summaryLast.array) ∧ q = pS) q := by
    intro q
    simp [NodeCell, Field.array]
  refine ⟨s₈, _, Exec.seq hx₅ (Exec.seq hx₆ hx₈), by omega,
    by simpa [s₈, s₇] using hA₆.frame hFw (fun q _ => hnodes q),
    by simpa [s₈, s₇] using hR₆.frame hFw (fun q _ => hnodes q), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [s₈, s₇, State.writeArr_regs]
    rw [State.writeArr_arrs_ne _ _ _ (by simp [Field.array]), State.writeArr_arrs_self,
      List.getElem?_set_self hlen₆]
  · simp only [s₈, s₇, State.writeArr_regs]
    rw [State.writeArr_arrs_self, State.writeArr_arrs_ne _ _ _ (by simp [Field.array]),
      List.getElem?_set_self hlen₆']
  · refine ((Frame.of_arrs_eq harr₅ (fun _ _ => False)).trans (hF₆.trans hFw)).mono ?_
    intro a q h
    rcases h with h | h | h
    · exact h.elim
    · exact Or.inl h
    · exact Or.inr h
  · exact (hW₆.writeArr _ _ (by omega)).writeArr _ _ (by have := hp65.2; omega)
  · intro r hr
    have := (Exec.seq hx₅ (Exec.seq hx₆ hx₈)).regs_eq_of_not_mem_writtenRegs (r := r)
    exact this (by simpa [anchorProg] using hr)

/-! ### The final push -/

/-- The top pointer of a stack is below the capacity. -/
theorem BlockChain.top_lt {s : State} {cap p : ℕ} {bs ns : List ℕ} {stack : List Block}
    (h : BlockChain s cap p bs ns stack) (hcap : 0 < cap) : p < cap := by
  cases h with
  | nil => exact hcap
  | cons _ hb _ _ _ _ _ _ _ _ => exact hb

theorem writeArr_get_self {s : State} {a i v : ℕ} (h : i < (s.arrs a).length) :
    ((s.writeArr a i v).arrs a)[i]? = some v := by
  rw [State.writeArr_arrs_self, List.getElem?_set_self h]

theorem writeArr_get_ne {s : State} {a a' i v : ℕ} (h : a' ≠ a) (q : ℕ) :
    ((s.writeArr a i v).arrs a')[q]? = (s.arrs a')[q]? := by
  rw [State.writeArr_arrs_ne _ _ _ h]

/-- Write a new block record at the address in register 54, with the lists
`L` (registers 65, 66) and `R` (registers 63, 64) and the stack below at
register 67. Register 67 then points to the new block, and register 54 moves
to the next free address. -/
def pushProg : Cmd :=
  .seq (.seq (.write Field.blockLeftFirst.array (.reg 54) (.reg 65))
      (.seq (.write Field.blockLeftLast.array (.reg 54) (.reg 66))
        (.seq (.write Field.blockRightFirst.array (.reg 54) (.reg 63))
          (.seq (.write Field.blockRightLast.array (.reg 54) (.reg 64))
            (.write Field.blockBelow.array (.reg 54) (.reg 67))))))
    (.seq (.assign 67 (.reg 54)) (.assign 54 (.op .add (.reg 54) (.const 1))))

/-- Part I, Section 4: "push (L,R) onto S.P", at a fresh block address. -/
theorem pushProg_spec {w D cap : ℕ} {s : State} {bs ns LA RA : List ℕ} {stack : List Block}
    {x y : List ReturnNode}
    (hB : BlockChain s cap (s.regs 67) bs ns stack)
    (hL : ListAt s cap (s.regs 65) (s.regs 66) LA x)
    (hR : ListAt s cap (s.regs 63) (s.regs 64) RA y)
    (hpos : 0 < s.regs 54) (hp : s.regs 54 < cap) (hfresh : s.regs 54 ∉ bs)
    (hlen : ∀ a, IsBlockArr a → s.regs 54 < (s.arrs a).length)
    (hW : Words D s) (hcapD : cap ≤ D + 1) (hD : D + 1 < 2 ^ w) :
    ∃ s', Exec w pushProg s s' 21 ∧ s'.regs 67 = s.regs 54 ∧ s'.regs 54 = s.regs 54 + 1 ∧
      BlockChain s' cap (s'.regs 67) (s.regs 54 :: bs) (LA ++ RA ++ ns) (⟨x, y⟩ :: stack) ∧
      Frame s s' (fun a q => q = s.regs 54 ∧ IsBlockArr a) ∧ Words D s' ∧
      (∀ r, r ≠ 54 → r ≠ 67 → s'.regs r = s.regs r) := by
  have hcap : 0 < cap := by omega
  set p := s.regs 54 with hpdef
  have h67 := hB.top_lt hcap
  have hpL := hL.pointers_lt hcap
  have hpR := hR.pointers_lt hcap
  let s₁ := s.writeArr Field.blockLeftFirst.array p (s.regs 65)
  let s₂ := s₁.writeArr Field.blockLeftLast.array p (s.regs 66)
  let s₃ := s₂.writeArr Field.blockRightFirst.array p (s.regs 63)
  let s₄ := s₃.writeArr Field.blockRightLast.array p (s.regs 64)
  let s₅ := s₄.writeArr Field.blockBelow.array p (s.regs 67)
  have hF₅ : Frame s s₅ (fun a q => q = p ∧ IsBlockArr a) :=
    ((((Frame.writeArr s _ _ _).trans (Frame.writeArr s₁ _ _ _)).trans
      (Frame.writeArr s₂ _ _ _)).trans (Frame.writeArr s₃ _ _ _)).trans
      (Frame.writeArr s₄ _ _ _) |>.mono (by
        intro a q h
        simp only [IsBlockArr]
        rcases h with (((h | h) | h) | h) | h <;> simp [h.1, h.2])
  have hl : ∀ a, IsBlockArr a → p < (s.arrs a).length := hlen
  have hl₁ : p < (s₁.arrs Field.blockLeftLast.array).length := by
    rw [(Frame.writeArr s _ _ _ _).1]; exact hl _ (by simp [IsBlockArr])
  have hl₂ : p < (s₂.arrs Field.blockRightFirst.array).length := by
    rw [(Frame.writeArr s₁ _ _ _ _).1, (Frame.writeArr s _ _ _ _).1]
    exact hl _ (by simp [IsBlockArr])
  have hl₃ : p < (s₃.arrs Field.blockRightLast.array).length := by
    rw [(Frame.writeArr s₂ _ _ _ _).1, (Frame.writeArr s₁ _ _ _ _).1,
      (Frame.writeArr s _ _ _ _).1]
    exact hl _ (by simp [IsBlockArr])
  have hl₄ : p < (s₄.arrs Field.blockBelow.array).length := by
    rw [(Frame.writeArr s₃ _ _ _ _).1, (Frame.writeArr s₂ _ _ _ _).1,
      (Frame.writeArr s₁ _ _ _ _).1, (Frame.writeArr s _ _ _ _).1]
    exact hl _ (by simp [IsBlockArr])
  have hpw : p < 2 ^ w := by omega
  have hx₅ : Exec w (.seq (.write Field.blockLeftFirst.array (.reg 54) (.reg 65))
      (.seq (.write Field.blockLeftLast.array (.reg 54) (.reg 66))
        (.seq (.write Field.blockRightFirst.array (.reg 54) (.reg 63))
          (.seq (.write Field.blockRightLast.array (.reg 54) (.reg 64))
            (.write Field.blockBelow.array (.reg 54) (.reg 67)))))) s s₅ 15 :=
    Exec.seq (exec_st (hl _ (by simp [IsBlockArr])) hpw (by omega))
      (Exec.seq (exec_st (s := s₁) hl₁ hpw (by simp [s₁, State.writeArr_regs]; omega))
        (Exec.seq (exec_st (s := s₂) hl₂ hpw (by simp [s₂, s₁, State.writeArr_regs]; omega))
          (Exec.seq (exec_st (s := s₃) hl₃ hpw
              (by simp [s₃, s₂, s₁, State.writeArr_regs]; omega))
            (exec_st (s := s₄) hl₄ hpw (by simp [s₄, s₃, s₂, s₁, State.writeArr_regs]; omega)))))
  let s₆ := s₅.setReg 67 p
  let s₇ := s₆.setReg 54 (p + 1)
  have hx₇ : Exec w (.seq (.assign 67 (.reg 54)) (.assign 54 (.op .add (.reg 54) (.const 1))))
      s₅ s₇ 6 := by
    have h1 : Exec w (.assign 67 (.reg 54)) s₅ s₆ 2 := exec_mov (s := s₅) hpw
    have h2 : Exec w (.assign 54 (.op .add (.reg 54) (.const 1))) s₆ s₇ 4 := by
      have h54 : s₆.regs 54 = p := by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.writeArr_regs, hpdef]
      have := Exec.assign (r := 54) (s := s₆) ((eval_op (eval_reg (s := s₆) (r := 54)
        (by rw [h54]; omega)) (eval_const (n := 1) (by omega))).trans
        (binop_add (by rw [h54]; omega)))
      rw [h54] at this
      exact this
    exact Exec.seq h1 h2
  have harr₇ : s₇.arrs = s₅.arrs := rfl
  have hF₇ : Frame s s₇ (fun a q => q = p ∧ IsBlockArr a) := hF₅
  have hne : ∀ a a' : Field, a ≠ a' → a.array ≠ a'.array := fun a a' h e =>
    h (Field.array_injective e)
  refine ⟨s₇, Exec.seq hx₅ hx₇, by simp [s₇, s₆], by simp [s₇], ?_, hF₇, ?_, ?_⟩
  · have h67₇ : s₇.regs 67 = p := by simp [s₇, s₆]
    rw [h67₇]
    refine hB.push hL hR hpos hp hfresh hF₇ ?_ ?_ ?_ ?_ ?_
    · rw [harr₇]
      simp only [s₅, s₄, s₃, s₂]
      rw [writeArr_get_ne (hne _ _ (by decide)), writeArr_get_ne (hne _ _ (by decide)),
        writeArr_get_ne (hne _ _ (by decide)), writeArr_get_ne (hne _ _ (by decide)),
        writeArr_get_self (hl _ (by simp [IsBlockArr]))]
    · rw [harr₇]
      simp only [s₅, s₄, s₃]
      rw [writeArr_get_ne (hne _ _ (by decide)), writeArr_get_ne (hne _ _ (by decide)),
        writeArr_get_ne (hne _ _ (by decide)), writeArr_get_self hl₁]
    · rw [harr₇]
      simp only [s₅, s₄]
      rw [writeArr_get_ne (hne _ _ (by decide)), writeArr_get_ne (hne _ _ (by decide)),
        writeArr_get_self hl₂]
    · rw [harr₇]
      simp only [s₅]
      rw [writeArr_get_ne (hne _ _ (by decide)), writeArr_get_self hl₃]
    · rw [harr₇]
      exact writeArr_get_self hl₄
  · exact ((((hW.writeArr _ _ (by omega)).writeArr _ _ (by omega)).writeArr _ _
      (by omega)).writeArr _ _ (by omega)).writeArr _ _ (by omega)
  · intro r h1 h2
    simp [s₇, s₆, h1, h2, s₅, s₄, s₃, s₂, s₁, State.writeArr_regs]

/-- The empty list has header `(0, 0)`. -/
theorem ListAt.empty (s : State) (cap : ℕ) : ListAt s cap 0 0 [] [] :=
  ⟨.nil, rfl, List.nodup_nil⟩

/-- Push `(L, R)` if one of them is nonempty, then store the stack top in the
record of `S` at register 57. -/
def pushPartProg : Cmd :=
  .seq (.ite (.reg 65) pushProg (.ite (.reg 63) pushProg .skip))
    (.write Field.summaryTop.array (.reg 57) (.reg 67))

/-- Part I, Section 4: "if L or R is nonempty: push (L,R) onto S.P". -/
theorem pushPartProg_spec {w D cap : ℕ} {s : State} {pS : ℕ} {bs ns LA RA : List ℕ}
    {stack : List Block} {x y : List ReturnNode}
    (hB : BlockChain s cap (s.regs 67) bs ns stack)
    (hL : ListAt s cap (s.regs 65) (s.regs 66) LA x)
    (hR : ListAt s cap (s.regs 63) (s.regs 64) RA y)
    (h57 : s.regs 57 = pS) (hpS : pS < (s.arrs Field.summaryTop.array).length) (hpSD : pS ≤ D)
    (hpos : 0 < s.regs 54) (hp : s.regs 54 < cap) (hfresh : s.regs 54 ∉ bs)
    (hlen : ∀ a, IsBlockArr a → s.regs 54 < (s.arrs a).length)
    (hW : Words D s) (hcapD : cap ≤ D + 1) (hD : D + 1 < 2 ^ w) :
    ∃ s' t, Exec w pushPartProg s s' t ∧ t ≤ 26 ∧
      (s'.arrs Field.summaryTop.array)[pS]? = some (s'.regs 67) ∧
      BlockChain s' cap (s'.regs 67) (if x.isEmpty && y.isEmpty then bs else s.regs 54 :: bs)
        (LA ++ RA ++ ns) (if x.isEmpty && y.isEmpty then stack else ⟨x, y⟩ :: stack) ∧
      s'.regs 54 = (if x.isEmpty && y.isEmpty then s.regs 54 else s.regs 54 + 1) ∧
      Frame s s' (fun a q => q = s.regs 54 ∧ IsBlockArr a ∨
        a = Field.summaryTop.array ∧ q = pS) ∧ Words D s' ∧
      (∀ r, r ≠ 54 → r ≠ 67 → s'.regs r = s.regs r) := by
  have hcap : 0 < cap := by omega
  have hpL := hL.pointers_lt hcap
  have hpR := hR.pointers_lt hcap
  -- First the conditional push.
  obtain ⟨s₁, t₁, hx₁, ht₁, hB₁, h54₁, hF₁, hW₁, hregs₁⟩ : ∃ s₁ t₁,
      Exec w (.ite (.reg 65) pushProg (.ite (.reg 63) pushProg .skip)) s s₁ t₁ ∧ t₁ ≤ 23 ∧
      BlockChain s₁ cap (s₁.regs 67) (if x.isEmpty && y.isEmpty then bs else s.regs 54 :: bs)
        (LA ++ RA ++ ns) (if x.isEmpty && y.isEmpty then stack else ⟨x, y⟩ :: stack) ∧
      s₁.regs 54 = (if x.isEmpty && y.isEmpty then s.regs 54 else s.regs 54 + 1) ∧
      Frame s s₁ (fun a q => q = s.regs 54 ∧ IsBlockArr a) ∧ Words D s₁ ∧
      (∀ r, r ≠ 54 → r ≠ 67 → s₁.regs r = s.regs r) := by
    by_cases h65 : s.regs 65 = 0
    · have hLe : LA = [] := hL.first_eq_zero_iff.mp h65
      have hxe : x = [] := by
        have := hL.1.length_eq
        rw [hLe] at this
        exact List.length_eq_zero_iff.mp this.symm
      subst hLe hxe
      by_cases h63 : s.regs 63 = 0
      · have hRe : RA = [] := hR.first_eq_zero_iff.mp h63
        have hye : y = [] := by
          have := hR.1.length_eq
          rw [hRe] at this
          exact List.length_eq_zero_iff.mp this.symm
        subst hRe hye
        refine ⟨s, _, exec_ite_zero h65 (exec_ite_zero h63 (Exec.skip s)), by omega,
          by simpa using hB, by simp, Frame.refl s _, hW, fun _ _ _ => rfl⟩
      · obtain ⟨s₁, hx, h67, h54, hB', hF, hW', hregs⟩ :=
          pushProg_spec hB hL hR hpos hp hfresh hlen hW hcapD hD
        have hy : y.isEmpty = false := by
          rcases y with _ | ⟨b, y⟩
          · exact absurd (hR.first_eq_zero_iff.mpr (by
              have := hR.1.length_eq
              exact List.length_eq_zero_iff.mp (by simpa using this))) h63
          · rfl
        refine ⟨s₁, _, exec_ite_zero h65 (exec_ite_pos h63 (by omega) hx), by omega, ?_, ?_, hF,
          hW', hregs⟩
        · simpa [hy] using hB'
        · simp [hy, h54]
    · obtain ⟨s₁, hx, h67, h54, hB', hF, hW', hregs⟩ :=
        pushProg_spec hB hL hR hpos hp hfresh hlen hW hcapD hD
      have hx' : x.isEmpty = false := by
        rcases x with _ | ⟨b, x⟩
        · exact absurd (hL.first_eq_zero_iff.mpr (by
            have := hL.1.length_eq
            exact List.length_eq_zero_iff.mp (by simpa using this))) h65
        · rfl
      refine ⟨s₁, _, exec_ite_pos h65 (by omega) hx, by omega, ?_, ?_, hF, hW', hregs⟩
      · simpa [hx'] using hB'
      · simp [hx', h54]
  -- Then the store of the top pointer.
  have h57₁ : s₁.regs 57 = pS := by rw [hregs₁ 57 (by decide) (by decide), h57]
  have hpS₁ : pS < (s₁.arrs Field.summaryTop.array).length := by rw [(hF₁ _).1]; exact hpS
  have h67₁ : s₁.regs 67 < cap := hB₁.top_lt hcap
  have hx₂ := exec_st (w := w) (s := s₁) (a := Field.summaryTop.array) (idx := 57) (val := 67)
    (by rw [h57₁]; exact hpS₁) (by rw [h57₁]; omega) (by omega)
  rw [h57₁] at hx₂
  have hFw := Frame.writeArr s₁ Field.summaryTop.array pS (s₁.regs 67)
  refine ⟨_, _, Exec.seq hx₁ hx₂, by omega, ?_, ?_, ?_, ?_, hW₁.writeArr _ _ (by omega), ?_⟩
  · simp only [State.writeArr_regs]
    exact writeArr_get_self hpS₁
  · simp only [State.writeArr_regs]
    exact hB₁.frame hFw (fun q _ => by simp [BlockCell, Field.array])
      (fun q _ => by simp [NodeCell, Field.array])
  · simpa [State.writeArr_regs] using h54₁
  · exact (hF₁.trans hFw).mono (fun a q h => by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h)
  · intro r h1 h2
    simp only [State.writeArr_regs]
    exact hregs₁ r h1 h2

/-- The second half of `MERGE(S,T)`, after the child loop: the anchor step,
the loop over the old stack of `S`, and the final push. -/
def mergeRestProg : Cmd :=
  .seq anchorProg (.seq (.assign 65 (.const 0)) (.seq (.assign 66 (.const 0))
    (.seq (.assign 67 (.read Field.summaryTop.array (.reg 57)))
      (.seq oldLoopProg (.ite (.reg 35) pushPartProg .skip)))))

/-- The cells that `MERGE` may write: next pointers of the given nodes, the
record of the fresh block `p`, and the anchor and top of the record `pS`. -/
def MergeCells (pS p : ℕ) (P : List ℕ) (a q : ℕ) : Prop :=
  a = Field.nodeNext.array ∧ q ∈ P ∨ q = p ∧ IsBlockArr a ∨
    (a = Field.summaryFirst.array ∨ a = Field.summaryLast.array ∨
      a = Field.summaryTop.array) ∧ q = pS

theorem oldLoopProg_regs : ∀ r : ℕ, r ∈ oldLoopProg.writtenRegs → r = 35 ∨ (63 ≤ r ∧ r ≤ 74) := by
  decide

theorem anchorProg_regs : ∀ r : ℕ, r ∈ anchorProg.writtenRegs → 63 ≤ r ∧ r ≤ 72 := by
  decide

theorem childLoopProg_regs : ∀ r : ℕ, r ∈ childLoopProg.writtenRegs → r = 35 ∨ (63 ≤ r ∧ r ≤ 71) := by
  decide

theorem pushPartProg_regs : ∀ r : ℕ, r ∈ pushPartProg.writtenRegs → r = 54 ∨ r = 67 := by
  decide

/-- The new block list of `MERGE`: push `(L, R)` unless both are empty. -/
abbrev pushed (r : List Block × List ReturnNode × List ReturnNode) : List Block :=
  if r.2.1.isEmpty && r.2.2.isEmpty then r.1 else ⟨r.2.1, r.2.2⟩ :: r.1

/-- The second half of `MERGE(S,T)` refines the Lean `merge` after
`mergeChild`. The record of `S` is at register 57, the anchor header of `T` in
the record at register 61, `b = T.least` in register 62, and the list `R` built
by the child loop in registers 63, 64. -/
theorem mergeRestProg_spec {w D M : ℕ} {s : State} {S : Summary} {pS pT fT lT b : ℕ}
    {bsS nsS AT RA : List ℕ} {Tanchor right : List ReturnNode}
    (hS : SummaryAt s M pS S bsS nsS)
    (h57 : s.regs 57 = pS) (h61 : s.regs 61 = pT) (h62 : s.regs 62 = b)
    (hTf : (s.arrs Field.summaryFirst.array)[pT]? = some fT)
    (hTl : (s.arrs Field.summaryLast.array)[pT]? = some lT)
    (hAT : ListAt s (M + 1) fT lT AT Tanchor)
    (hR : ListAt s (M + 1) (s.regs 63) (s.regs 64) RA right)
    (hnd : (nsS ++ AT ++ RA).Nodup)
    (hfresh : ∀ q ∈ bsS, q < s.regs 54) (h54 : 0 < s.regs 54) (h54M : s.regs 54 < M + 1)
    (hlen : ∀ a, IsBlockArr a → s.regs 54 < (s.arrs a).length)
    (h35 : s.regs 35 = 1) (hW : Words D s) (hpT : pT ≤ D) (hb : b ≤ D) (hM : M ≤ D)
    (hD : D + 2 < 2 ^ w) :
    ∃ s' t, Exec w mergeRestProg s s' t ∧ Words D s' ∧
      (∀ r, r ∉ mergeRestProg.writtenRegs → s'.regs r = s.regs r) ∧
      Frame s s' (MergeCells pS (s.regs 54) (nsS ++ AT ++ RA)) ∧
      s.regs 54 ≤ s'.regs 54 ∧ s'.regs 54 ≤ s.regs 54 + 1 ∧
      match mergeOld b S.blocks [] (if b = S.least then right else right ++ Tanchor) with
      | none => s'.regs 35 = 0 ∧ t ≤ 120 * S.blocks.length + 240
      | some r => s'.regs 35 = 1 ∧ ∃ bs' ns',
          SummaryAt s' M pS ⟨S.least, if b = S.least then S.anchor ++ Tanchor else S.anchor,
            pushed r⟩ bs' ns' ∧
          ns'.Perm (nsS ++ AT ++ RA) ∧ (∀ q ∈ bs', q ∈ bsS ∨ (s.regs 54 ≤ q ∧ q < s'.regs 54)) ∧
          t + 120 * (pushed r).length ≤ 120 * S.blocks.length + 240 := by
  obtain ⟨hpos, hcapS, hleast, fS, lS, topS, AS, stS, hSf, hSl, hStop, hAS, hBS, hns, hndS,
    hbndS⟩ := hS
  subst hns
  have hcap : 0 < M + 1 := by omega
  -- Disjointness facts.
  have hn1 := List.disjoint_of_nodup_append hnd
  have hn2 := List.disjoint_of_nodup_append (List.nodup_append.mp hnd).1
  have hn3 := List.disjoint_of_nodup_append hndS
  have hASAT : ∀ q ∈ AS, q ∉ AT := fun q h h' =>
    hn2 (List.mem_append_left _ h) h'
  have hRAT : ∀ q ∈ RA, q ∉ AT := fun q h h' => hn1 (List.mem_append_right _ h') h
  have hASRA : ∀ q ∈ AS, q ∉ RA := fun q h h' =>
    hn1 (List.mem_append_left _ (List.mem_append_left _ h)) h'
  -- The anchor step.
  have hpSD : pS ≤ D := by omega
  obtain ⟨s₁, t₁, hx₁, ht₁, hA₁, hR₁, hSf₁, hSl₁, hF₁, hW₁, hregs₁⟩ :=
    anchorProg_spec (w := w) (D := D) h57 h61 h62 hSf hSl hleast hTf hTl hAS hAT hR hASAT
      hRAT hASRA hpSD hpT hb hW hcap (by omega) (by omega)
  have hr₁ : ∀ r, r ≠ 63 → r ≠ 64 → r ≠ 65 → r ≠ 66 → r ≠ 68 → r ≠ 69 → r ≠ 72 →
      s₁.regs r = s.regs r := by
    intro r h1 h2 h3 h4 h5 h6 h7
    exact hregs₁ r (by simp [anchorProg, appendProg, Cmd.writtenRegs, h1, h2, h3, h4, h5, h6,
      h7])
  set AS' := if b = S.least then AS ++ AT else AS with hAS'
  set RA' := if b = S.least then RA else RA ++ AT with hRA'
  -- Clear `L` and load the stack of `S`.
  have hStop₁ : (s₁.arrs Field.summaryTop.array)[pS]? = some topS := by
    rw [hF₁.get (by simp [AnchorCells, Field.array])]; exact hStop
  have htopD : topS ≤ D := hW.get (by simp [Field.array]) (by simp [Field.array]) hStop
  have h57₁ : s₁.regs 57 = pS := by rw [hr₁ 57 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide), h57]
  let s₄ := ((s₁.setReg 65 0).setReg 66 0).setReg 67 topS
  have hx₂ : Exec w (.assign 65 (.const 0)) s₁ (s₁.setReg 65 0) 2 := exec_setc (by omega)
  have hx₃ : Exec w (.assign 66 (.const 0)) (s₁.setReg 65 0) ((s₁.setReg 65 0).setReg 66 0) 2 :=
    exec_setc (by omega)
  have hx₄ : Exec w (.assign 67 (.read Field.summaryTop.array (.reg 57)))
      ((s₁.setReg 65 0).setReg 66 0) s₄ 3 :=
    exec_ld (by simp; omega) (by simpa [h57₁] using hStop₁) (by omega)
  have harr₄ : s₄.arrs = s₁.arrs := rfl
  have hF₁' : Frame s s₄ (AnchorCells pS (AS ++ RA)) := hF₁
  have hBS₄ : BlockChain s₄ (M + 1) (s₄.regs 67) bsS stS S.blocks := by
    have := hBS.frame hF₁' (fun q _ => by simp [BlockCell, AnchorCells, Field.array])
      (fun q hq => by
        simp only [NodeCell, AnchorCells, Field.array, not_or]
        refine ⟨⟨fun h => by omega, fun h => by omega⟩, ⟨fun h => by omega, fun h => by omega⟩,
          fun h => ?_, fun h => by omega⟩
        rcases List.mem_append.mp h.2 with h' | h'
        · exact hn3 h' hq
        · exact hn1 (List.mem_append_left _ (List.mem_append_right _ hq)) h')
    simpa [s₄] using this
  have hL₄ : ListAt s₄ (M + 1) (s₄.regs 65) (s₄.regs 66) [] [] := by
    simpa [s₄] using ListAt.empty s₄ (M + 1)
  have hR₄ : ListAt s₄ (M + 1) (s₄.regs 63) (s₄.regs 64) RA'
      (if b = S.least then right else right ++ Tanchor) := by
    simpa [s₄] using hR₁.of_arrs_eq harr₄
  have hRAs : ∀ q ∈ RA', q ∈ RA ∨ q ∈ AT := by
    intro q hq
    by_cases hbs : b = S.least
    · simp only [hRA', hbs, ↓reduceIte] at hq; exact Or.inl hq
    · simp only [hRA', hbs, ↓reduceIte, List.mem_append] at hq; exact hq
  have hASs : ∀ q ∈ AS', q ∈ AS ∨ q ∈ AT := by
    intro q hq
    by_cases hbs : b = S.least
    · simp only [hAS', hbs, ↓reduceIte, List.mem_append] at hq; exact hq
    · simp only [hAS', hbs, ↓reduceIte] at hq; exact Or.inl hq
  have hndRA' : RA'.Nodup := hR₁.2.2
  have hndAS' : AS'.Nodup := hA₁.2.2
  have hnd₄ : ([] ++ RA' ++ stS).Nodup := by
    rw [List.nil_append, List.nodup_append]
    refine ⟨hndRA', (List.nodup_append.mp hndS).2.1, fun q hq q' hq' he => ?_⟩
    subst he
    rcases hRAs q hq with h | h
    · exact hn1 (List.mem_append_left _ (List.mem_append_right _ hq')) h
    · exact hn2 (List.mem_append_right _ hq') h
  have h35₄ : s₄.regs 35 = 1 := by
    simp [s₄]; rw [hr₁ 35 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h35]
  have h62₄ : s₄.regs 62 = b := by
    simp [s₄]; rw [hr₁ 62 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), h62]
  have hW₄ : Words D s₄ := hW₁
  -- The old loop.
  obtain ⟨s₅, t₅, hx₅, hF₅, hW₅, hregs₅, hOld⟩ := oldLoopProg_spec (w := w) (D := D) hBS₄ hL₄
    hR₄ hnd₄ h35₄ hW₄ (by omega) hcap (by omega) hD
  rw [h62₄] at hOld
  have hreg₅ : ∀ r : ℕ, r ≠ 35 → r < 63 ∨ 74 < r → s₅.regs r = s.regs r := by
    intro r h1 h2
    rw [hregs₅ r (fun h => by have := oldLoopProg_regs r h; omega)]
    simp only [s₄, State.setReg_regs, (show r ≠ 67 by omega), (show r ≠ 66 by omega),
      (show r ≠ 65 by omega), ↓reduceIte]
    exact hregs₁ r (fun h => by have := anchorProg_regs r h; omega)
  have h54₅ : s₅.regs 54 = s.regs 54 := hreg₅ 54 (by decide) (by omega)
  have h57₅ : s₅.regs 57 = pS := (hreg₅ 57 (by decide) (by omega)).trans h57
  have hF₅' : Frame s s₅ (MergeCells pS (s.regs 54) (AS ++ stS ++ AT ++ RA)) := by
    refine (hF₁'.trans hF₅).mono ?_
    intro a q h
    rcases h with (⟨ha, hq⟩ | ⟨ha, hq⟩) | ⟨ha, hq⟩
    · refine Or.inl ⟨ha, ?_⟩
      rcases List.mem_append.mp hq with h | h <;> simp [h]
    · exact Or.inr (Or.inr ⟨by rcases ha with h | h <;> simp [h], hq⟩)
    · refine Or.inl ⟨ha, ?_⟩
      rw [List.nil_append] at hq
      rcases List.mem_append.mp hq with h | h
      · rcases hRAs q h with h' | h' <;> simp [h']
      · simp [h]
  have hAR : ∀ q ∈ AS', q ∉ RA' := by
    intro q hq hq'
    by_cases hbs : b = S.least
    · simp only [hAS', hRA', hbs, ↓reduceIte, List.mem_append] at hq hq'
      rcases hq with h | h
      · exact hASRA q h hq'
      · exact hRAT q hq' h
    · simp only [hAS', hRA', hbs, ↓reduceIte, List.mem_append] at hq hq'
      rcases hq' with h | h
      · exact hASRA q hq h
      · exact hASAT q hq h
  have hAst : ∀ q ∈ AS', q ∉ stS := by
    intro q hq hq'
    rcases hASs q hq with h | h
    · exact hn3 h hq'
    · exact hn2 (List.mem_append_right _ hq') h
  have hA₅ : ListAt s₅ (M + 1) (s₁.regs 65) (s₁.regs 66) AS'
      (if b = S.least then S.anchor ++ Tanchor else S.anchor) :=
    (hA₁.of_arrs_eq harr₄).frame_next hF₅ (fun q hq h => by
      rw [List.nil_append] at h
      rcases List.mem_append.mp h with h | h
      · exact hAR q hq h
      · exact hAst q hq h)
  have hSf₅ : (s₅.arrs Field.summaryFirst.array)[pS]? = some (s₁.regs 65) := by
    rw [hF₅.get (by simp [Field.array]), harr₄]; exact hSf₁
  have hSl₅ : (s₅.arrs Field.summaryLast.array)[pS]? = some (s₁.regs 66) := by
    rw [hF₅.get (by simp [Field.array]), harr₄]; exact hSl₁
  have hleast₅ : (s₅.arrs Field.summaryLeast.array)[pS]? = some S.least := by
    rw [hF₅'.get (by simp [MergeCells, IsBlockArr, Field.array])]; exact hleast
  have hAR' : (AS' ++ RA').Perm (AS ++ AT ++ RA) := by
    by_cases hbs : b = S.least
    · simp only [hAS', hRA', hbs, ↓reduceIte]
      exact List.Perm.refl _
    · simp only [hAS', hRA', hbs, ↓reduceIte]
      rw [← List.append_assoc]
      exact List.Perm.refl _ |>.trans (List.perm_iff_count.mpr fun a => by
        simp only [List.count_append]; omega)
  have hndfin : (AS' ++ RA' ++ stS).Nodup := by
    refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨hndAS', hndRA', fun a ha b hb e => ?_⟩,
      (List.nodup_append.mp hndS).2.1, fun a ha b hb e => ?_⟩
    · subst e; exact hAR a ha hb
    · subst e
      rcases List.mem_append.mp ha with h | h
      · exact hAst a h hb
      · rcases hRAs a h with h' | h'
        · exact hn1 (List.mem_append_left _ (List.mem_append_right _ hb)) h'
        · exact hn2 (List.mem_append_right _ hb) h'
  have hlen₅ : ∀ a, (s₅.arrs a).length = (s.arrs a).length := fun a => (hF₅' a).1
  rcases hm : mergeOld b S.blocks [] (if b = S.least then right else right ++ Tanchor) with
    _ | ⟨blocks', left', right'⟩
  · rw [hm] at hOld
    obtain ⟨h35₅, ht₅⟩ := hOld
    have hx := Exec.seq hx₁ (Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄ (Exec.seq hx₅
      (exec_ite_zero (c₁ := pushPartProg) h35₅ (Exec.skip s₅))))))
    refine ⟨s₅, _, hx, hW₅, fun r hr => hx.regs_eq_of_not_mem_writtenRegs hr, hF₅',
      by omega, by omega, h35₅, by omega⟩
  · rw [hm] at hOld
    obtain ⟨h35₅, LA', RA'', bs', ns', hB₅, hsuf, hL₅, hR₅, hperm, ht₅⟩ := hOld
    have hfr : s₅.regs 54 ∉ bs' := fun h => by
      have := hfresh _ (hsuf.subset h); omega
    obtain ⟨s₆, t₆, hx₆, ht₆, hTop₆, hB₆, h54₆, hF₆, hW₆, hregs₆⟩ :=
      pushPartProg_spec (w := w) (D := D) (pS := pS) hB₅ hL₅ hR₅ h57₅
        (by rw [hlen₅]; exact (List.getElem?_eq_some_iff.mp hStop).1) hpSD (by omega)
        (by omega) hfr (fun a ha => by rw [hlen₅]; rw [h54₅]; exact hlen a ha) hW₅ (by omega)
        (by omega)
    have hx := Exec.seq hx₁ (Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄ (Exec.seq hx₅
      (exec_ite_pos (c₂ := .skip) (by omega : s₅.regs 35 ≠ 0) (by omega) hx₆)))))
    have hF₆' : Frame s s₆ (MergeCells pS (s.regs 54) (AS ++ stS ++ AT ++ RA)) :=
      (hF₅'.trans hF₆).mono fun a q h => by
        rcases h with h | (⟨hq, ha⟩ | ⟨ha, hq⟩)
        · exact h
        · exact Or.inr (Or.inl ⟨by rw [hq, h54₅], ha⟩)
        · exact Or.inr (Or.inr ⟨Or.inr (Or.inr ha), hq⟩)
    have hnode₆ : ∀ q, ¬ NodeCell (fun a q => q = s₅.regs 54 ∧ IsBlockArr a ∨
        a = Field.summaryTop.array ∧ q = pS) q := by
      intro q
      simp [NodeCell, IsBlockArr, Field.array]
    have hpl : (pushed (blocks', left', right')).length ≤ blocks'.length + 1 := by
      simp only [pushed]; split <;> simp
    refine ⟨s₆, _, hx, hW₆, fun r hr => hx.regs_eq_of_not_mem_writtenRegs hr, hF₆', ?_, ?_,
      ?_⟩
    · rw [h54₆, h54₅]; split <;> omega
    · rw [h54₆, h54₅]; split <;> omega
    refine ⟨by rw [hregs₆ 35 (by decide) (by decide)]; exact h35₅, _, _,
      ⟨hpos, hcapS, ?_, s₁.regs 65, s₁.regs 66, s₆.regs 67, AS', LA' ++ RA'' ++ ns', ?_, ?_,
        hTop₆, hA₅.frame hF₆ (fun q _ => hnode₆ q), hB₆, rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hF₆.get (by simp [IsBlockArr, Field.array])]; exact hleast₅
    · rw [hF₆.get (by simp [IsBlockArr, Field.array])]; exact hSf₅
    · rw [hF₆.get (by simp [IsBlockArr, Field.array])]; exact hSl₅
    · refine (List.Perm.nodup_iff ?_).mpr hndfin
      refine (List.Perm.append_left AS' hperm).trans ?_
      simp
    · have hbn : bs'.Nodup := hbndS.sublist hsuf.sublist
      split
      · exact hbn
      · exact List.nodup_cons.mpr ⟨hfr, hbn⟩
    · refine ((List.Perm.append_left AS' hperm).trans ?_)
      rw [List.nil_append, ← List.append_assoc]
      refine (List.Perm.append_right stS hAR').trans ?_
      exact List.perm_iff_count.mpr fun a => by simp only [List.count_append]; omega
    · intro q hq
      split at hq
      · exact Or.inl (hsuf.subset hq)
      · rename_i hne
        rcases List.mem_cons.mp hq with h | h
        · right
          rw [h54₆, h54₅, ite_eq_right_of_eq_false _ _ (eq_false hne), h, h54₅]
          omega
        · exact Or.inl (hsuf.subset h)
    · omega

/-! ### The whole of `MERGE` -/

/-- `MERGE` with two nonempty summaries, at registers 57 (`S`) and 61 (`T`). -/
def mergeBothProg : Cmd :=
  .seq (.assign 62 (.read Field.summaryLeast.array (.reg 61)))
    (.seq (.assign 63 (.const 0)) (.seq (.assign 64 (.const 0))
      (.seq (.assign 67 (.read Field.summaryTop.array (.reg 61)))
        (.seq childLoopProg (.ite (.reg 35) mergeRestProg .skip)))))

/-- Part I, Section 4, `MERGE(S,T)`. Register 57 holds the record of `S` and
register 61 that of `T`, with zero for an empty summary. The result is in
register 57, and register 35 is set to zero on a rejection. -/
def mergeProg : Cmd :=
  .ite (.reg 61) (.ite (.reg 57) mergeBothProg (.assign 57 (.reg 61))) .skip

/-- An optional summary at a record pointer. The empty summary has pointer
zero and owns no blocks and no nodes. -/
def OptSummaryAt (s : State) (M p : ℕ) : Option Summary → List ℕ → List ℕ → Prop
  | none, bs, ns => p = 0 ∧ bs = [] ∧ ns = []
  | some S, bs, ns => SummaryAt s M p S bs ns

/-- The number of blocks of an optional summary. -/
def blockCount : Option Summary → ℕ
  | none => 0
  | some S => S.blocks.length

theorem SummaryAt.nodup {s : State} {M p : ℕ} {S : Summary} {bs ns : List ℕ}
    (h : SummaryAt s M p S bs ns) : ns.Nodup := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hnd, _⟩ := h
  exact hnd

theorem SummaryAt.blocks_nodup {s : State} {M p : ℕ} {S : Summary} {bs ns : List ℕ}
    (h : SummaryAt s M p S bs ns) : bs.Nodup := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbnd⟩ := h
  exact hbnd

theorem SummaryAt.ptr_pos {s : State} {M p : ℕ} {S : Summary} {bs ns : List ℕ}
    (h : SummaryAt s M p S bs ns) : 0 < p ∧ p < M + 1 := ⟨h.1, h.2.1⟩

/-- `merge` with two summaries, written with `Option.bind`. -/
theorem merge_some_some (S T : Summary) : merge (some S) (some T) =
    (mergeChild T.blocks []).bind fun right =>
      (mergeOld T.least S.blocks [] (if T.least = S.least then right else right ++ T.anchor)).bind
        fun r => some (some ⟨S.least, if T.least = S.least then S.anchor ++ T.anchor else S.anchor,
          pushed r⟩) := by
  simp only [merge]
  cases hc : mergeChild T.blocks [] with
  | none => rfl
  | some right =>
    cases ho : mergeOld T.least S.blocks [] (if T.least = S.least then right else right ++ T.anchor)
      with
    | none => simp [ho]
    | some r => simp [ho, pushed]

set_option maxRecDepth 20000 in
theorem mergeRestProg_regs : ∀ r : ℕ, r ∈ mergeRestProg.writtenRegs →
    r = 35 ∨ r = 54 ∨ (63 ≤ r ∧ r ≤ 74) := by
  decide

set_option maxRecDepth 20000 in
theorem mergeBothProg_regs : ∀ r : ℕ, r ∈ mergeBothProg.writtenRegs →
    r = 35 ∨ r = 54 ∨ (62 ≤ r ∧ r ≤ 74) := by
  decide

set_option maxRecDepth 20000 in
theorem mergeProg_regs : ∀ r : ℕ, r ∈ mergeProg.writtenRegs →
    r = 35 ∨ r = 54 ∨ r = 57 ∨ (62 ≤ r ∧ r ≤ 74) := by
  decide

/-- `MERGE` refines `merge`. Only next pointers of the nodes of `S` and `T`,
the record of the fresh block at register 54, and the anchor and top of the
record of `S` are written. The block allocator in register 54 moves by at most
one. With 120 steps of potential per block, a merge costs at most 300 steps. -/
theorem mergeProg_spec {w D M : ℕ} {s : State} {old new : Option Summary}
    {bsS nsS bsT nsT : List ℕ}
    (hS : OptSummaryAt s M (s.regs 57) old bsS nsS)
    (hT : OptSummaryAt s M (s.regs 61) new bsT nsT)
    (hdis : ∀ q ∈ nsS, q ∉ nsT)
    (hfresh : ∀ q ∈ bsS, q < s.regs 54) (h54 : 0 < s.regs 54) (h54M : s.regs 54 < M + 1)
    (hlen : ∀ a, IsBlockArr a → s.regs 54 < (s.arrs a).length)
    (h35 : s.regs 35 = 1) (hW : Words D s) (hM : M ≤ D) (hD : D + 2 < 2 ^ w) :
    ∃ s' t, Exec w mergeProg s s' t ∧ Words D s' ∧
      (∀ r, r ∉ mergeProg.writtenRegs → s'.regs r = s.regs r) ∧
      Frame s s' (MergeCells (s.regs 57) (s.regs 54) (nsS ++ nsT)) ∧
      s.regs 54 ≤ s'.regs 54 ∧ s'.regs 54 ≤ s.regs 54 + 1 ∧
      match merge old new with
      | none => s'.regs 35 = 0 ∧ t ≤ 300 + 120 * (blockCount old + blockCount new)
      | some o => s'.regs 35 = 1 ∧ (s'.regs 57 = s.regs 57 ∨ s'.regs 57 = s.regs 61) ∧
          ∃ bs' ns', OptSummaryAt s' M (s'.regs 57) o bs' ns' ∧ ns'.Perm (nsS ++ nsT) ∧
          (∀ q ∈ bs', q ∈ bsS ∨ q ∈ bsT ∨ (s.regs 54 ≤ q ∧ q < s'.regs 54)) ∧
          t + 120 * blockCount o ≤ 300 + 120 * (blockCount old + blockCount new) := by
  have hcap : 0 < M + 1 := by omega
  cases new with
  | none =>
    obtain ⟨h61, rfl, rfl⟩ := hT
    have hx := exec_ite_zero (w := w) (c₁ := .ite (.reg 57) mergeBothProg (.assign 57 (.reg 61)))
      h61 (Exec.skip s)
    have hmerge : merge old none = some old := by cases old <;> rfl
    rw [hmerge]
    exact ⟨s, _, hx, hW, fun _ _ => rfl, Frame.refl s _, le_refl _, by omega, h35, Or.inl rfl,
      bsS, nsS, hS, by simp, fun q hq => Or.inl hq, by simp [blockCount]⟩
  | some T =>
  have hpT : 0 < s.regs 61 ∧ s.regs 61 < M + 1 := SummaryAt.ptr_pos hT
  have h61w : s.regs 61 < 2 ^ w := by omega
  cases old with
  | none =>
    obtain ⟨h57, rfl, rfl⟩ := hS
    have hx := exec_ite_pos (c₂ := .skip) (by omega : s.regs 61 ≠ 0) h61w
      (exec_ite_zero (c₁ := mergeBothProg) h57 (exec_mov (dst := 57) h61w))
    refine ⟨_, _, hx, hW, fun r hr => hx.regs_eq_of_not_mem_writtenRegs hr,
      Frame.of_arrs_eq rfl _, le_refl _, by simp, ?_⟩
    show _ ∧ _
    refine ⟨by simp [h35], Or.inr (by simp), bsT, nsT, ?_, by simp, fun q hq => Or.inr (Or.inl hq),
      by simp [blockCount]⟩
    simpa [OptSummaryAt] using hT.of_arrs_eq (s' := s.setReg 57 (s.regs 61)) rfl
  | some S =>
  simp only [OptSummaryAt] at hS hT
  have hpS := hS.ptr_pos
  have h57w : s.regs 57 < 2 ^ w := by omega
  set pS := s.regs 57 with hpSdef
  set pT := s.regs 61 with hpTdef
  obtain ⟨_, hcapT, hleastT, fT, lT, topT, AT, stT, hTf, hTl, hTtop, hAT, hBT, hnsT, hndT,
    hbndT⟩ := hT
  subst hnsT
  have hbD : T.least ≤ D := hW.get (by simp [Field.array]) (by simp [Field.array]) hleastT
  have htopD : topT ≤ D := hW.get (by simp [Field.array]) (by simp [Field.array]) hTtop
  -- Load `b`, clear `R`, and load the stack of `T`.
  let s₁ := s.setReg 62 T.least
  let s₂ := s₁.setReg 63 0
  let s₃ := s₂.setReg 64 0
  let s₄ := s₃.setReg 67 topT
  have hx₁ : Exec w (.assign 62 (.read Field.summaryLeast.array (.reg 61))) s s₁ 3 :=
    exec_ld h61w hleastT (by omega)
  have hx₂ : Exec w (.assign 63 (.const 0)) s₁ s₂ 2 := exec_setc (by omega)
  have hx₃ : Exec w (.assign 64 (.const 0)) s₂ s₃ 2 := exec_setc (by omega)
  have hx₄ : Exec w (.assign 67 (.read Field.summaryTop.array (.reg 61))) s₃ s₄ 3 :=
    exec_ld (by simp [s₃, s₂, s₁]; omega) (by simpa [s₃, s₂, s₁] using hTtop) (by omega)
  have harr₄ : s₄.arrs = s.arrs := rfl
  have hBT₄ : BlockChain s₄ (M + 1) (s₄.regs 67) bsT stT T.blocks := by
    simpa [s₄] using hBT.of_arrs_eq harr₄
  have hR₄ : ListAt s₄ (M + 1) (s₄.regs 63) (s₄.regs 64) [] [] := by
    simpa [s₄, s₃, s₂] using ListAt.empty s₄ (M + 1)
  have hndst : ([] ++ stT).Nodup := by simpa using (List.nodup_append.mp hndT).2.1
  obtain ⟨s₅, t₅, hx₅, ht₅, hF₅, hW₅, hregs₅, hCh⟩ := childLoopProg_spec (w := w) (D := D)
    hBT₄ hR₄ hndst (by simp [s₄, s₃, s₂, s₁, h35]) hW hcap (by omega) (by omega)
  have hreg₅ : ∀ r : ℕ, r ≠ 35 → r < 62 ∨ 74 < r → s₅.regs r = s.regs r := by
    intro r h1 h2
    rw [hregs₅ r (fun h => by have := childLoopProg_regs r h; omega)]
    simp only [s₄, s₃, s₂, s₁, State.setReg_regs, (show r ≠ 67 by omega),
      (show r ≠ 64 by omega), (show r ≠ 63 by omega), (show r ≠ 62 by omega), ↓reduceIte]
  have h62₅ : s₅.regs 62 = T.least := by
    rw [hregs₅ 62 (fun h => by have := childLoopProg_regs 62 h; omega)]; simp [s₄, s₃, s₂, s₁]
  have hF₅' : Frame s s₅ (fun a q => a = Field.nodeNext.array ∧ q ∈ stT) :=
    hF₅.mono fun a q h => ⟨h.1, by simpa using h.2⟩
  have hlen₅ : ∀ a, (s₅.arrs a).length = (s.arrs a).length := fun a => (hF₅' a).1
  have hx35 : ∀ {s' : State} {c₁ : Cmd}, s'.regs 35 = 0 →
      Exec w (.ite (.reg 35) c₁ .skip) s' s' 2 :=
    fun h => exec_ite_zero h (Exec.skip _)
  rw [merge_some_some]
  rcases hc : mergeChild T.blocks [] with _ | right
  · -- The child loop rejects.
    rw [hc] at hCh
    have hx := exec_ite_pos (c₂ := .skip) (by omega : s.regs 61 ≠ 0) h61w
      (exec_ite_pos (c₂ := .assign 57 (.reg 61)) (by omega : s.regs 57 ≠ 0) h57w
        (Exec.seq hx₁ (Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄ (Exec.seq hx₅
          (hx35 (c₁ := mergeRestProg) hCh)))))))
    refine ⟨s₅, _, hx, hW₅, fun r hr => hx.regs_eq_of_not_mem_writtenRegs hr,
      hF₅'.mono fun a q h => Or.inl ⟨h.1, by simp [h.2]⟩, by rw [hreg₅ 54 (by decide) (by omega)],
      by rw [hreg₅ 54 (by decide) (by omega)]; omega, ?_⟩
    simp only [Option.bind_none]
    exact ⟨hCh, by simp only [blockCount]; omega⟩
  · rw [hc] at hCh
    obtain ⟨h35₅, hR₅⟩ := hCh
    rw [List.nil_append] at hR₅
    have hS₅ : SummaryAt s₅ M pS S bsS nsS := hS.frame hF₅'
      (by simp [SummaryCell, Field.array]) (fun q _ => by simp [BlockCell, Field.array])
      (fun q hq => by
        simp only [NodeCell, Field.array, not_or]
        exact ⟨by omega, by omega, fun h => hdis q hq (List.mem_append_right _ h.2)⟩)
    have hAT₅ : ListAt s₅ (M + 1) fT lT AT T.anchor := hAT.frame_next hF₅' fun q hq h =>
      List.disjoint_of_nodup_append hndT hq h
    have hnd : (nsS ++ AT ++ stT).Nodup := by
      rw [List.append_assoc]
      exact List.nodup_append.mpr ⟨hS.nodup, hndT, fun a ha b hb e => by
        subst e; exact hdis a ha hb⟩
    have h57₅ : s₅.regs 57 = pS := hreg₅ 57 (by decide) (by omega)
    have h61₅ : s₅.regs 61 = pT := hreg₅ 61 (by decide) (by omega)
    have h54₅ : s₅.regs 54 = s.regs 54 := hreg₅ 54 (by decide) (by omega)
    have hTf₅ : (s₅.arrs Field.summaryFirst.array)[pT]? = some fT := by
      rw [hF₅'.get (by simp [Field.array])]; exact hTf
    have hTl₅ : (s₅.arrs Field.summaryLast.array)[pT]? = some lT := by
      rw [hF₅'.get (by simp [Field.array])]; exact hTl
    obtain ⟨s₆, t₆, hx₆, hW₆, hregs₆, hF₆, h54a, h54b, hRest⟩ :=
      mergeRestProg_spec (w := w) (D := D) (M := M) hS₅ h57₅ h61₅ h62₅ hTf₅ hTl₅ hAT₅ hR₅ hnd
        (by rw [h54₅]; exact hfresh) (by omega) (by omega)
        (fun a ha => by rw [hlen₅, h54₅]; exact hlen a ha) h35₅ hW₅ (by omega) hbD hM hD
    have hx := exec_ite_pos (c₂ := .skip) (by omega : s.regs 61 ≠ 0) h61w
      (exec_ite_pos (c₂ := .assign 57 (.reg 61)) (by omega : s.regs 57 ≠ 0) h57w
        (Exec.seq hx₁ (Exec.seq hx₂ (Exec.seq hx₃ (Exec.seq hx₄ (Exec.seq hx₅
          (exec_ite_pos (c₂ := .skip) (by omega : s₅.regs 35 ≠ 0) (by omega) hx₆)))))))
    have hF : Frame s s₆ (MergeCells pS (s.regs 54) (nsS ++ (AT ++ stT))) :=
      (hF₅'.trans hF₆).mono fun a q h => by
        rcases h with ⟨ha, hq⟩ | (⟨ha, hq⟩ | ⟨hq, ha⟩ | ⟨ha, hq⟩)
        · exact Or.inl ⟨ha, by simp [hq]⟩
        · exact Or.inl ⟨ha, by simpa [List.append_assoc] using hq⟩
        · exact Or.inr (Or.inl ⟨by rw [hq, h54₅], ha⟩)
        · exact Or.inr (Or.inr ⟨ha, hq⟩)
    refine ⟨s₆, _, hx, hW₆, fun r hr => hx.regs_eq_of_not_mem_writtenRegs hr, hF,
      by omega, by omega, ?_⟩
    simp only [Option.bind_some]
    have h57₆ : s₆.regs 57 = pS := by
      rw [hregs₆ 57 (fun h => by have := mergeRestProg_regs 57 h; omega)]; exact h57₅
    rcases ho : mergeOld T.least S.blocks []
        (if T.least = S.least then right else right ++ T.anchor) with _ | r
    · rw [ho] at hRest
      obtain ⟨h35₆, ht₆⟩ := hRest
      simp only [Option.bind_none]
      exact ⟨h35₆, by simp only [blockCount]; omega⟩
    · rw [ho] at hRest
      obtain ⟨h35₆, bs', ns', hS₆, hperm, hbs, ht₆⟩ := hRest
      simp only [Option.bind_some]
      refine ⟨h35₆, Or.inl h57₆, bs', ns', ?_, ?_, ?_, ?_⟩
      · simp only [OptSummaryAt]; rw [h57₆]; exact hS₆
      · simpa [List.append_assoc] using hperm
      · intro q hq
        rcases hbs q hq with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨by omega, h.2⟩)
      · simp only [blockCount]; omega

end GraphMinor.Compute.PlanarityRam
