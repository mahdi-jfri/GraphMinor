module

public import GraphMinor.Compute.Algorithm77Prog76Step

/-!
# Word RAM Implementation of Graph Minors XIII, Step (7.6): Canonical Wall Paths and Ray Extension

This file implements the Word RAM subroutines for generating canonical elementary-wall paths and
extending star rays to a subwall (`pathToSubwall`, `extendStarRay`) in Step (7.6) of (7.7):

1. **Section 1: `IsCoordBufPrefix`, `appendRowPathCmd`, and `buildElemWallUpPathCmd`:**
   Generates `rowPath` and `elemWallUpPath` in `(coordXArr, coordYArr)`.
2. **Section 2: `buildElemWallCanonicalPathCmd`, `buildElemWallEdgeCanonicalPathCmd`, and
   `elemPathForVertCmd`:**
   Generates `elemWallCanonicalPath`, `elemWallEdgeCanonicalPath`, and `W.elemPathForVert v q`
   in `(coordXArr, coordYArr)`.
3. **Section 3: `liftElemPathCmd`, `pathToSubwallCmd`, and `extendOneRayCmd`:**
   Lifts `W.elemPathForVert v q` into `liftArr`, computes `W.pathToSubwall W'.vertexFinset v q`
   into `tmpPathArr2`, and extends each star ray in `starRayArr l a i`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

set_option linter.deprecated false

attribute [local irreducible] elemWallCoords elemWallNumVerts elemWallEdges elemWallVertCoord

/-! ### Section 1: `IsCoordBufPrefix`, `appendRowPathCmd`, and `buildElemWallUpPathCmd` -/

theorem rowPathUp_succ_eq_append (x : ℕ) :
    ∀ (d y : ℕ), rowPathUp x (d + 1) y = rowPathUp x d y ++ [(x + d + 1, y)]
  | 0, y => by simp [rowPathUp]
  | d + 1, y => by
    calc rowPathUp x (d + 1 + 1) y
        = (x, y) :: rowPathUp (x + 1) (d + 1) y := rfl
      _ = (x, y) :: (rowPathUp (x + 1) d y ++ [(x + 1 + d + 1, y)]) := by
          rw [rowPathUp_succ_eq_append (x + 1) d y]
      _ = rowPathUp x (d + 1) y ++ [(x + (d + 1) + 1, y)] := by
          have hadd : x + 1 + d + 1 = x + (d + 1) + 1 := by omega
          rw [rowPathUp, List.cons_append, hadd]

theorem reverse_rowPathUp_succ (x₂ d y : ℕ) :
    (rowPathUp x₂ (d + 1) y).reverse = (x₂ + d + 1, y) :: (rowPathUp x₂ d y).reverse := by
  rw [rowPathUp_succ_eq_append, List.reverse_append, List.reverse_singleton, List.singleton_append]

theorem length_rowPathUp : ∀ (x d y : ℕ), (rowPathUp x d y).length = d + 1
  | x, 0, y => by simp [rowPathUp]
  | x, d + 1, y => by simp [rowPathUp, length_rowPathUp (x + 1) d y]

theorem length_rowPath (x₁ x₂ y : ℕ) :
    (rowPath x₁ x₂ y).length = (if x₁ ≤ x₂ then x₂ - x₁ else x₁ - x₂) + 1 := by
  unfold rowPath
  split_ifs <;> simp [length_rowPathUp]

theorem length_rowPath_le {w_row x₁ x₂ : ℕ} (y : ℕ) (hx₁ : x₁ < w_row) (hx₂ : x₂ < w_row) :
    (rowPath x₁ x₂ y).length ≤ w_row := by
  rw [length_rowPath]
  split_ifs <;> omega

theorem vertCol_lt {h : ℕ} (hh : 1 ≤ h) (y : ℕ) : vertCol y < 2 * h + 2 := by
  unfold vertCol
  split_ifs <;> omega

theorem length_elemWallUpPath_le {h x₂ : ℕ} (hh : 1 ≤ h) (hx₂ : x₂ < 2 * h + 2) :
    ∀ (d x₁ y₁ : ℕ), x₁ < 2 * h + 2 →
      (elemWallUpPath x₂ d x₁ y₁).length ≤ (d + 1) * (2 * h + 2)
  | 0, x₁, y₁, hx₁ => by
    simpa [elemWallUpPath] using length_rowPath_le y₁ hx₁ hx₂
  | d + 1, x₁, y₁, hx₁ => by
    rw [elemWallUpPath, List.length_append]
    have h1 := length_rowPath_le y₁ hx₁ (vertCol_lt hh y₁)
    have h2 := length_elemWallUpPath_le hh hx₂ d (vertCol y₁) (y₁ + 1) (vertCol_lt hh y₁)
    calc (rowPath x₁ (vertCol y₁) y₁).length +
          (elemWallUpPath x₂ d (vertCol y₁) (y₁ + 1)).length
        ≤ (2 * h + 2) + (d + 1) * (2 * h + 2) := Nat.add_le_add h1 h2
      _ = (d + 1 + 1) * (2 * h + 2) := by ring

theorem IsArrBufPrefix.write_end {arr pfx : List ℕ} {r7 : ℕ}
    (h : IsArrBufPrefix arr pfx r7) (hlt : pfx.length < arr.length) (val : ℕ) :
    IsArrBufPrefix (arr.set r7 val) (pfx ++ [val]) (r7 + 1) := by
  rcases h with ⟨rfl, _, hget⟩
  refine ⟨by simp, by simp [List.length_set]; omega, fun i hi => ?_⟩
  rw [List.getElem?_set]
  by_cases heq : pfx.length = i
  · subst heq
    simp [hlt]
  · have hi_lt : i < pfx.length := by simp at hi; omega
    simp [heq, List.getElem_append_left hi_lt, hget i hi_lt]

/-- Two-array buffer prefix invariant for coordinate pairs `(x, y)` in `(arrX, arrY)` at `idx`. -/
def IsCoordBufPrefix (arrX arrY : List ℕ) (pfx : List (ℕ × ℕ)) (idx : ℕ) : Prop :=
  IsArrBufPrefix arrX (pfx.map Prod.fst) idx ∧
  IsArrBufPrefix arrY (pfx.map Prod.snd) idx ∧
  arrX.length = arrY.length

/-- Push `(r_22, r_23)` into `(bufArr, bufArr2)` at `r_7` and increment `r_7`. -/
def pushCoordPairCmd : Cmd :=
  .seq (.write bufArr (.reg 7) (.reg 22))
    (.seq (.write bufArr2 (.reg 7) (.reg 23))
      (.assign 7 (.op .add (.reg 7) (.const 1))))

theorem pushCoordPairCmd_exec {w : ℕ} (pfx : List (ℕ × ℕ)) (p : ℕ × ℕ) {s : State}
    (hw1 : 1 < 2 ^ w)
    (hp1_w : p.1 < 2 ^ w)
    (hp2_w : p.2 < 2 ^ w)
    (hbuf_w : (s.arrs bufArr).length < 2 ^ w)
    (hbuf : IsCoordBufPrefix (s.arrs bufArr) (s.arrs bufArr2) pfx (s.regs 7))
    (hlt : pfx.length < (s.arrs bufArr).length)
    (hr22 : s.regs 22 = p.1)
    (hr23 : s.regs 23 = p.2) :
    ∃ s' t,
      Exec w pushCoordPairCmd s s' t ∧
      t ≤ 10 ∧
      IsCoordBufPrefix (s'.arrs bufArr) (s'.arrs bufArr2) (pfx ++ [p]) (s'.regs 7) ∧
      (s'.arrs bufArr).length = (s.arrs bufArr).length ∧
      (s'.arrs bufArr2).length = (s.arrs bufArr2).length ∧
      (∀ r : Reg, r ≠ 7 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ bufArr → a ≠ bufArr2 → s'.arrs a = s.arrs a) := by
  rcases hbuf with ⟨hbufX, hbufY, hlenXY⟩
  have hr7_eq : s.regs 7 = pfx.length := by simpa using hbufX.1
  have hr7_w : s.regs 7 < 2 ^ w := by omega
  have hr7_1_w : s.regs 7 + 1 < 2 ^ w := by omega
  have hltY : pfx.length < (s.arrs bufArr2).length := by omega
  let s₁ := s.writeArr bufArr (s.regs 7) p.1
  have hex₁ : Exec w (.write bufArr (.reg 7) (.reg 22)) s s₁ 3 :=
    .write (by simp [Expr.eval, checkWord, hr7_w])
      (by simp [Expr.eval, checkWord, hr22, hp1_w])
      (by omega)
  let s₂ := s₁.writeArr bufArr2 (s.regs 7) p.2
  have hex₂ : Exec w (.write bufArr2 (.reg 7) (.reg 23)) s₁ s₂ 3 :=
    .write (by simp [Expr.eval, checkWord, s₁, hr7_w])
      (by simp [Expr.eval, checkWord, s₁, hr23, hp2_w])
      (by simp [s₁]; omega)
  let s₃ := s₂.setReg 7 (s.regs 7 + 1)
  have hex₃ : Exec w (.assign 7 (.op .add (.reg 7) (.const 1))) s₂ s₃ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hr7_w, hw1, hr7_1_w])
  have hbufX' : IsArrBufPrefix (s₃.arrs bufArr) ((pfx ++ [p]).map Prod.fst) (s₃.regs 7) := by
    dsimp only [s₃, s₂, s₁]
    rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ (by decide : bufArr ≠ bufArr2),
      State.writeArr_arrs_self, State.setReg_regs_self, List.map_append, List.map_singleton]
    exact hbufX.write_end (by simpa using hlt) p.1
  have hbufY' : IsArrBufPrefix (s₃.arrs bufArr2) ((pfx ++ [p]).map Prod.snd) (s₃.regs 7) := by
    dsimp only [s₃, s₂, s₁]
    rw [State.setReg_arrs, State.writeArr_arrs_self,
      State.writeArr_arrs_ne _ _ _ (by decide : bufArr2 ≠ bufArr),
      State.setReg_regs_self, List.map_append, List.map_singleton]
    exact hbufY.write_end (by simpa using hltY) p.2
  refine ⟨s₃, 3 + (3 + 4), .seq hex₁ (.seq hex₂ hex₃), by omega,
    ⟨hbufX', hbufY', by simp [s₃, s₂, s₁, State.writeArr_arrs_self, State.writeArr_arrs_ne, hlenXY]⟩,
    by simp [s₃, s₂, s₁, State.writeArr_arrs_self, State.writeArr_arrs_ne],
    by simp [s₃, s₂, s₁, State.writeArr_arrs_self, State.writeArr_arrs_ne],
    fun r h7 => by simp [s₃, s₂, s₁, h7],
    fun a ha1 ha2 => by simp [s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha1, State.writeArr_arrs_ne _ _ _ ha2]⟩

/-- Loop body of `appendRowPathUpStepLoop`: pushes `(r_22, r_23)`, increments `r_22`, decrements `r_24`. -/
def appendRowPathUpStepBody : Cmd :=
  .seq pushCoordPairCmd
    (.seq (.assign 22 (.op .add (.reg 22) (.const 1)))
      (.assign 24 (.op .sub (.reg 24) (.const 1))))

/-- Loop performing `d = r_24` rightward steps in row `r_23` starting at `r_22`. -/
def appendRowPathUpStepLoop : Cmd :=
  .while (.op .lt (.const 0) (.reg 24)) appendRowPathUpStepBody

theorem appendRowPathUpStepLoop_exec {w : ℕ} (y : ℕ)
    (hw1 : 1 < 2 ^ w) (hy_w : y < 2 ^ w) :
    ∀ (d x : ℕ) (pfx : List (ℕ × ℕ)) {s : State}
      (_hxd_w : x + d < 2 ^ w)
      (_hd_w : d < 2 ^ w)
      (_hbuf_w : (s.arrs bufArr).length < 2 ^ w)
      (_hbuf : IsCoordBufPrefix (s.arrs bufArr) (s.arrs bufArr2) pfx (s.regs 7))
      (_hcap : pfx.length + (d + 1) ≤ (s.arrs bufArr).length)
      (_hr22 : s.regs 22 = x)
      (_hr23 : s.regs 23 = y)
      (_hr24 : s.regs 24 = d),
      ∃ s' t,
        Exec w (.seq appendRowPathUpStepLoop pushCoordPairCmd) s s' t ∧
        t ≤ 21 * d + 13 ∧
        IsCoordBufPrefix (s'.arrs bufArr) (s'.arrs bufArr2) (pfx ++ rowPathUp x d y) (s'.regs 7) ∧
        (s'.arrs bufArr).length = (s.arrs bufArr).length ∧
        (s'.arrs bufArr2).length = (s.arrs bufArr2).length ∧
        s'.regs 22 = x + d ∧
        s'.regs 23 = y ∧
        (∀ r : Reg, r ≠ 7 → r ≠ 22 → r ≠ 24 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, a ≠ bufArr → a ≠ bufArr2 → s'.arrs a = s.arrs a)
  | 0, x, pfx, s, hxd_w, _, hbuf_w, hbuf, hcap, hr22, hr23, hr24 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 24)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr24, h0_w]
    have hex_loop : Exec w appendRowPathUpStepLoop s s 3 := .while_false hcond
    rcases pushCoordPairCmd_exec pfx (x, y) hw1 (by omega) hy_w hbuf_w hbuf (by omega) hr22 hr23 with
      ⟨s', t_p, hex_p, ht_p, hbuf', hlen1', hlen2', hregs', harrs'⟩
    refine ⟨s', 3 + t_p, .seq hex_loop hex_p, by omega,
      by simpa [rowPathUp] using hbuf', hlen1', hlen2',
      by rw [hregs' 22 (by decide)]; omega,
      by rw [hregs' 23 (by decide)]; exact hr23,
      fun r h7 _ _ => hregs' r h7, harrs'⟩
  | d + 1, x, pfx, s, hxd_w, hd_w, hbuf_w, hbuf, hcap, hr22, hr23, hr24 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hx_w : x < 2 ^ w := by omega
    have hx1_w : x + 1 < 2 ^ w := by omega
    have hd0_w : d < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 24)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr24, h0_w, hw1, hd_w]
    rcases pushCoordPairCmd_exec pfx (x, y) hw1 hx_w hy_w hbuf_w hbuf (by omega) hr22 hr23 with
      ⟨s₁, t_p, hex₁, ht_p, hbuf₁, hlen1_1, hlen2_1, hregs₁, harrs₁⟩
    have hr22_1 : s₁.regs 22 = x := by rw [hregs₁ 22 (by decide), hr22]
    have hr24_1 : s₁.regs 24 = d + 1 := by rw [hregs₁ 24 (by decide), hr24]
    let s₂ := s₁.setReg 22 (x + 1)
    have hex₂ : Exec w (.assign 22 (.op .add (.reg 22) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr22_1, hx_w, hw1, hx1_w])
    let s₃ := s₂.setReg 24 d
    have hex₃ : Exec w (.assign 24 (.op .sub (.reg 24) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, hr24_1, hd_w, hw1, hd0_w])
    have hex_body : Exec w appendRowPathUpStepBody s s₃ (t_p + (4 + 4)) :=
      .seq hex₁ (.seq hex₂ hex₃)
    rcases appendRowPathUpStepLoop_exec y hw1 hy_w d (x + 1) (pfx ++ [(x, y)]) (s := s₃)
        (by omega) hd0_w (by simpa [s₃, s₂, hlen1_1] using hbuf_w)
        (by simpa [s₃, s₂] using hbuf₁)
        (by simp [s₃, s₂, hlen1_1]; omega)
        (by simp [s₃, s₂])
        (by simp [s₃, s₂, hregs₁ 23 (by decide), hr23])
        (by simp [s₃]) with
      ⟨s', t_rest, hex_rest, ht_rest, hbuf', hlen1', hlen2', hr22', hr23', hregs', harrs'⟩
    cases hex_rest with
    | @seq _ _ _ s_mid _ t_l t_last hex_l hex_last =>
      have hpfx_eq : (pfx ++ [(x, y)]) ++ rowPathUp (x + 1) d y = pfx ++ rowPathUp x (d + 1) y := by
        simp [rowPathUp, List.append_assoc]
      rw [hpfx_eq] at hbuf'
      refine ⟨s', (3 + (t_p + (4 + 4)) + t_l) + t_last,
        .seq (.while_true hcond (by omega) hex_body hex_l) hex_last,
        by omega, hbuf',
        by simpa [s₃, s₂, hlen1_1] using hlen1',
        by simpa [s₃, s₂, hlen2_1] using hlen2',
        by omega, hr23',
        fun r h7 h22 h24 => by
          rw [hregs' r h7 h22 h24]
          simp [s₃, s₂, hregs₁ r h7, h22, h24],
        fun a ha1 ha2 => by
          rw [harrs' a ha1 ha2]
          simp [s₃, s₂, harrs₁ a ha1 ha2]⟩

/-- Loop body of `appendRowPathDownStepLoop`: pushes `(r_22, r_23)`, decrements `r_22`, decrements `r_24`. -/
def appendRowPathDownStepBody : Cmd :=
  .seq pushCoordPairCmd
    (.seq (.assign 22 (.op .sub (.reg 22) (.const 1)))
      (.assign 24 (.op .sub (.reg 24) (.const 1))))

/-- Loop performing `d = r_24` leftward steps in row `r_23` starting at `r_22 = x₂ + d`. -/
def appendRowPathDownStepLoop : Cmd :=
  .while (.op .lt (.const 0) (.reg 24)) appendRowPathDownStepBody

theorem appendRowPathDownStepLoop_exec {w : ℕ} (x₂ y : ℕ)
    (hw1 : 1 < 2 ^ w) (hy_w : y < 2 ^ w) :
    ∀ (d : ℕ) (pfx : List (ℕ × ℕ)) {s : State}
      (_hxd_w : x₂ + d < 2 ^ w)
      (_hd_w : d < 2 ^ w)
      (_hbuf_w : (s.arrs bufArr).length < 2 ^ w)
      (_hbuf : IsCoordBufPrefix (s.arrs bufArr) (s.arrs bufArr2) pfx (s.regs 7))
      (_hcap : pfx.length + (d + 1) ≤ (s.arrs bufArr).length)
      (_hr22 : s.regs 22 = x₂ + d)
      (_hr23 : s.regs 23 = y)
      (_hr24 : s.regs 24 = d),
      ∃ s' t,
        Exec w (.seq appendRowPathDownStepLoop pushCoordPairCmd) s s' t ∧
        t ≤ 21 * d + 13 ∧
        IsCoordBufPrefix (s'.arrs bufArr) (s'.arrs bufArr2)
          (pfx ++ (rowPathUp x₂ d y).reverse) (s'.regs 7) ∧
        (s'.arrs bufArr).length = (s.arrs bufArr).length ∧
        (s'.arrs bufArr2).length = (s.arrs bufArr2).length ∧
        s'.regs 22 = x₂ ∧
        s'.regs 23 = y ∧
        (∀ r : Reg, r ≠ 7 → r ≠ 22 → r ≠ 24 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, a ≠ bufArr → a ≠ bufArr2 → s'.arrs a = s.arrs a)
  | 0, pfx, s, hxd_w, _, hbuf_w, hbuf, hcap, hr22, hr23, hr24 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 24)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr24, h0_w]
    have hex_loop : Exec w appendRowPathDownStepLoop s s 3 := .while_false hcond
    rcases pushCoordPairCmd_exec pfx (x₂, y) hw1 (by omega) hy_w hbuf_w hbuf (by omega)
        (by omega) hr23 with
      ⟨s', t_p, hex_p, ht_p, hbuf', hlen1', hlen2', hregs', harrs'⟩
    refine ⟨s', 3 + t_p, .seq hex_loop hex_p, by omega,
      by simpa [rowPathUp] using hbuf', hlen1', hlen2',
      by rw [hregs' 22 (by decide)]; omega,
      by rw [hregs' 23 (by decide)]; exact hr23,
      fun r h7 _ _ => hregs' r h7, harrs'⟩
  | d + 1, pfx, s, hxd_w, hd_w, hbuf_w, hbuf, hcap, hr22, hr23, hr24 => by
    have h0_w : 0 < 2 ^ w := by omega
    have hxd0_w : x₂ + d < 2 ^ w := by omega
    have hd0_w : d < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 24)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr24, h0_w, hw1, hd_w]
    rcases pushCoordPairCmd_exec pfx (x₂ + d + 1, y) hw1 (by omega) hy_w hbuf_w hbuf (by omega)
        (by omega) hr23 with
      ⟨s₁, t_p, hex₁, ht_p, hbuf₁, hlen1_1, hlen2_1, hregs₁, harrs₁⟩
    have hr22_1 : s₁.regs 22 = x₂ + (d + 1) := by rw [hregs₁ 22 (by decide), hr22]
    have hsub_xd : x₂ + (d + 1) - 1 = x₂ + d := by omega
    have hr24_1 : s₁.regs 24 = d + 1 := by rw [hregs₁ 24 (by decide), hr24]
    let s₂ := s₁.setReg 22 (x₂ + d)
    have hex₂ : Exec w (.assign 22 (.op .sub (.reg 22) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr22_1, hxd_w, hw1, hsub_xd, hxd0_w])
    let s₃ := s₂.setReg 24 d
    have hex₃ : Exec w (.assign 24 (.op .sub (.reg 24) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, hr24_1, hd_w, hw1, hd0_w])
    have hex_body : Exec w appendRowPathDownStepBody s s₃ (t_p + (4 + 4)) :=
      .seq hex₁ (.seq hex₂ hex₃)
    rcases appendRowPathDownStepLoop_exec x₂ y hw1 hy_w d (pfx ++ [(x₂ + d + 1, y)]) (s := s₃)
        hxd0_w hd0_w (by simpa [s₃, s₂, hlen1_1] using hbuf_w)
        (by simpa [s₃, s₂] using hbuf₁)
        (by simp [s₃, s₂, hlen1_1]; omega)
        (by simp [s₃, s₂])
        (by simp [s₃, s₂, hregs₁ 23 (by decide), hr23])
        (by simp [s₃]) with
      ⟨s', t_rest, hex_rest, ht_rest, hbuf', hlen1', hlen2', hr22', hr23', hregs', harrs'⟩
    cases hex_rest with
    | @seq _ _ _ s_mid _ t_l t_last hex_l hex_last =>
      have hpfx_eq :
          (pfx ++ [(x₂ + d + 1, y)]) ++ (rowPathUp x₂ d y).reverse =
            pfx ++ (rowPathUp x₂ (d + 1) y).reverse := by
        rw [reverse_rowPathUp_succ, List.append_assoc, List.singleton_append]
      rw [hpfx_eq] at hbuf'
      refine ⟨s', (3 + (t_p + (4 + 4)) + t_l) + t_last,
        .seq (.while_true hcond (by omega) hex_body hex_l) hex_last,
        by omega, hbuf',
        by simpa [s₃, s₂, hlen1_1] using hlen1',
        by simpa [s₃, s₂, hlen2_1] using hlen2',
        hr22', hr23',
        fun r h7 h22 h24 => by
          rw [hregs' r h7 h22 h24]
          simp [s₃, s₂, hregs₁ r h7, h22, h24],
        fun a ha1 ha2 => by
          rw [harrs' a ha1 ha2]
          simp [s₃, s₂, harrs₁ a ha1 ha2]⟩

/-- Append `rowPath x₁ x₂ y` (where `x₁ = r_22`, `y = r_23`, `x₂ = r_25`) to `(bufArr, bufArr2)`
at `r_7`, leaving `r_22 = x₂`. -/
def appendRowPathCmd : Cmd :=
  .ite (exprLe (.reg 22) (.reg 25))
    (.seq (.assign 24 (.op .sub (.reg 25) (.reg 22)))
      (.seq appendRowPathUpStepLoop pushCoordPairCmd))
    (.seq (.assign 24 (.op .sub (.reg 22) (.reg 25)))
      (.seq appendRowPathDownStepLoop pushCoordPairCmd))

theorem appendRowPathCmd_exec {w : ℕ} (x₁ x₂ y : ℕ) (pfx : List (ℕ × ℕ)) {s : State}
    (hw1 : 1 < 2 ^ w)
    (hx₁_w : x₁ < 2 ^ w)
    (hx₂_w : x₂ < 2 ^ w)
    (hy_w : y < 2 ^ w)
    (hbuf_w : (s.arrs bufArr).length < 2 ^ w)
    (hbuf : IsCoordBufPrefix (s.arrs bufArr) (s.arrs bufArr2) pfx (s.regs 7))
    (hcap : pfx.length + (rowPath x₁ x₂ y).length ≤ (s.arrs bufArr).length)
    (hr22 : s.regs 22 = x₁)
    (hr23 : s.regs 23 = y)
    (hr25 : s.regs 25 = x₂) :
    ∃ s' t,
      Exec w appendRowPathCmd s s' t ∧
      t ≤ 21 * (rowPath x₁ x₂ y).length + 25 ∧
      IsCoordBufPrefix (s'.arrs bufArr) (s'.arrs bufArr2) (pfx ++ rowPath x₁ x₂ y) (s'.regs 7) ∧
      (s'.arrs bufArr).length = (s.arrs bufArr).length ∧
      (s'.arrs bufArr2).length = (s.arrs bufArr2).length ∧
      s'.regs 22 = x₂ ∧
      s'.regs 23 = y ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 22 → r ≠ 24 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ bufArr → a ≠ bufArr2 → s'.arrs a = s.arrs a) := by
  have he22 : (Expr.reg 22).eval w s = some x₁ := by simp [Expr.eval, checkWord, hr22, hx₁_w]
  have he25 : (Expr.reg 25).eval w s = some x₂ := by simp [Expr.eval, checkWord, hr25, hx₂_w]
  have hcond := eval_exprLe hw1 he22 he25
  by_cases hle : x₁ ≤ x₂
  · rw [if_pos hle] at hcond
    let d := x₂ - x₁
    have hd_w : d < 2 ^ w := by omega
    have hrow : rowPath x₁ x₂ y = rowPathUp x₁ d y := by simp [rowPath, hle, d]
    have hlen_row : (rowPath x₁ x₂ y).length = d + 1 := by rw [hrow, length_rowPathUp]
    let s₁ := s.setReg 24 d
    have hex₁ : Exec w (.assign 24 (.op .sub (.reg 25) (.reg 22))) s s₁ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr25, hr22, hx₂_w, hx₁_w, hd_w, d])
    rcases appendRowPathUpStepLoop_exec y hw1 hy_w d x₁ pfx (s := s₁)
        (by omega) hd_w (by simpa [s₁] using hbuf_w) (by simpa [s₁] using hbuf)
        (by simp [s₁]; omega) (by simp [s₁, hr22]) (by simp [s₁, hr23]) (by simp [s₁]) with
      ⟨s', t_l, hex_l, ht_l, hbuf', hlen1', hlen2', hr22', hr23', hregs', harrs'⟩
    refine ⟨s', _, .ite_true hcond (by omega) (.seq hex₁ hex_l),
      by simp [exprLe, Expr.cost]; omega,
      by rwa [hrow], hlen1', hlen2', by omega, hr23',
      fun r h7 h22 h24 => by rw [hregs' r h7 h22 h24]; simp [s₁, h24],
      harrs'⟩
  · rw [if_neg hle] at hcond
    let d := x₁ - x₂
    have hd_w : d < 2 ^ w := by omega
    have hrow : rowPath x₁ x₂ y = (rowPathUp x₂ d y).reverse := by simp [rowPath, hle, d]
    have hlen_row : (rowPath x₁ x₂ y).length = d + 1 := by
      rw [hrow, List.length_reverse, length_rowPathUp]
    let s₁ := s.setReg 24 d
    have hex₁ : Exec w (.assign 24 (.op .sub (.reg 22) (.reg 25))) s s₁ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr22, hr25, hx₁_w, hx₂_w, hd_w, d])
    rcases appendRowPathDownStepLoop_exec x₂ y hw1 hy_w d pfx (s := s₁)
        (by omega) hd_w (by simpa [s₁] using hbuf_w) (by simpa [s₁] using hbuf)
        (by simp [s₁]; omega) (by simp [s₁, hr22]; omega) (by simp [s₁, hr23]) (by simp [s₁]) with
      ⟨s', t_l, hex_l, ht_l, hbuf', hlen1', hlen2', hr22', hr23', hregs', harrs'⟩
    refine ⟨s', _, .ite_false hcond (.seq hex₁ hex_l),
      by simp [exprLe, Expr.cost]; omega,
      by rwa [hrow], hlen1', hlen2', hr22', hr23',
      fun r h7 h22 h24 => by rw [hregs' r h7 h22 h24]; simp [s₁, h24],
      harrs'⟩

/-- Loop body of `appendElemWallUpPathLoop`: sets `r_25 := vertCol r_23`, appends
`rowPath r_22 r_25 r_23`, increments `r_23`, and decrements `r_26`. -/
def appendElemWallUpPathBody : Cmd :=
  .seq (.ite (exprEq (.op .mod (.reg 23) (.const 2)) (.const 0))
    (.assign 25 (.const 1))
    (.assign 25 (.const 2)))
    (.seq appendRowPathCmd
      (.seq (.assign 23 (.op .add (.reg 23) (.const 1)))
        (.assign 26 (.op .sub (.reg 26) (.const 1)))))

/-- Loop over the `d = r_26` vertical steps of `elemWallUpPath`. -/
def appendElemWallUpPathLoop : Cmd :=
  .while (.op .lt (.const 0) (.reg 26)) appendElemWallUpPathBody

/-- Append `elemWallUpPath x₂ d x₁ y₁` (where `x₁ = r_22`, `y₁ = r_23`, `d = r_26`, `x₂ = r_27`)
to `(bufArr, bufArr2)` at `r_7`. -/
def appendElemWallUpPathCmd : Cmd :=
  .seq appendElemWallUpPathLoop
    (.seq (.assign 25 (.reg 27))
      appendRowPathCmd)

theorem appendElemWallUpPathCmd_exec {w : ℕ} (x₂ : ℕ)
    (hw2 : 2 < 2 ^ w) (hx₂_w : x₂ < 2 ^ w) :
    ∀ (d x₁ y₁ : ℕ) (pfx : List (ℕ × ℕ)) {s : State}
      (_hx₁_w : x₁ < 2 ^ w)
      (_hy₁d_w : y₁ + d < 2 ^ w)
      (_hd_w : d < 2 ^ w)
      (_hbuf_w : (s.arrs bufArr).length < 2 ^ w)
      (_hbuf : IsCoordBufPrefix (s.arrs bufArr) (s.arrs bufArr2) pfx (s.regs 7))
      (_hcap : pfx.length + (elemWallUpPath x₂ d x₁ y₁).length ≤ (s.arrs bufArr).length)
      (_hr22 : s.regs 22 = x₁)
      (_hr23 : s.regs 23 = y₁)
      (_hr26 : s.regs 26 = d)
      (_hr27 : s.regs 27 = x₂),
      ∃ s' t,
        Exec w appendElemWallUpPathCmd s s' t ∧
        t ≤ 21 * (elemWallUpPath x₂ d x₁ y₁).length + 50 * d + 35 ∧
        IsCoordBufPrefix (s'.arrs bufArr) (s'.arrs bufArr2)
          (pfx ++ elemWallUpPath x₂ d x₁ y₁) (s'.regs 7) ∧
        (s'.arrs bufArr).length = (s.arrs bufArr).length ∧
        (s'.arrs bufArr2).length = (s.arrs bufArr2).length ∧
        (∀ r : Reg, r ≠ 7 → r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, a ≠ bufArr → a ≠ bufArr2 → s'.arrs a = s.arrs a)
  | 0, x₁, y₁, pfx, s, hx₁_w, hy₁d_w, _, hbuf_w, hbuf, hcap, hr22, hr23, hr26, hr27 => by
    have h0_w : 0 < 2 ^ w := by omega
    have h1_w : 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 26)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr26, h0_w]
    have hex_loop : Exec w appendElemWallUpPathLoop s s 3 := .while_false hcond
    let s₁ := s.setReg 25 x₂
    have hex₁ : Exec w (.assign 25 (.reg 27)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, hr27, hx₂_w])
    rcases appendRowPathCmd_exec x₁ x₂ y₁ pfx (s := s₁)
        h1_w hx₁_w hx₂_w (by omega) (by simpa [s₁] using hbuf_w) (by simpa [s₁] using hbuf)
        (by simpa [s₁, elemWallUpPath] using hcap)
        (by simp [s₁, hr22]) (by simp [s₁, hr23]) (by simp [s₁]) with
      ⟨s', t_r, hex_r, ht_r, hbuf', hlen1', hlen2', _, _, hregs', harrs'⟩
    refine ⟨s', 3 + (2 + t_r), .seq hex_loop (.seq hex₁ hex_r),
      by simpa [elemWallUpPath] using by omega,
      by simpa [elemWallUpPath] using hbuf', hlen1', hlen2',
      fun r h7 h22 _ h24 h25 _ => by rw [hregs' r h7 h22 h24]; simp [s₁, h25],
      harrs'⟩
  | d + 1, x₁, y₁, pfx, s, hx₁_w, hy₁d_w, hd_w, hbuf_w, hbuf, hcap, hr22, hr23, hr26, hr27 => by
    have h0_w : 0 < 2 ^ w := by omega
    have h1_w : 1 < 2 ^ w := by omega
    have hy₁_w : y₁ < 2 ^ w := by omega
    have hy₁1_w : y₁ + 1 < 2 ^ w := by omega
    have hd0_w : d < 2 ^ w := by omega
    have hvc_w : vertCol y₁ < 2 ^ w := by unfold vertCol; split_ifs <;> omega
    have hcond : (Expr.op .lt (.const 0) (.reg 26)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr26, h0_w, h1_w, hd_w]
    have hmod_eval : (Expr.op .mod (.reg 23) (.const 2)).eval w s = some (y₁ % 2) := by
      have : y₁ % 2 < 2 ^ w := by omega
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr23, hy₁_w, hw2, this]
    have hev_eval : (exprEq (.op .mod (.reg 23) (.const 2)) (.const 0)).eval w s =
        some (if y₁ % 2 = 0 then 1 else 0) :=
      eval_exprEq h1_w hmod_eval (by simp [Expr.eval, checkWord, h0_w])
    let s₁ := s.setReg 25 (vertCol y₁)
    have hex_vc : ∃ t_vc, Exec w (.ite (exprEq (.op .mod (.reg 23) (.const 2)) (.const 0))
        (.assign 25 (.const 1)) (.assign 25 (.const 2))) s s₁ t_vc ∧ t_vc ≤ 12 := by
      dsimp only [s₁, vertCol]
      by_cases hev : y₁ % 2 = 0
      · rw [if_pos hev] at hev_eval
        refine ⟨_, .ite_true hev_eval (by omega)
          (.assign (by simp [Expr.eval, checkWord, h1_w, hev])),
          by simp [exprEq, Expr.cost]⟩
      · rw [if_neg hev] at hev_eval
        refine ⟨_, .ite_false hev_eval
          (.assign (by simp [Expr.eval, checkWord, hw2, hev])),
          by simp [exprEq, Expr.cost]⟩
    rcases hex_vc with ⟨t_vc, hex₁, ht_vc⟩
    have hcap₁ : pfx.length + (rowPath x₁ (vertCol y₁) y₁).length ≤ (s₁.arrs bufArr).length := by
      simp only [s₁, State.setReg_arrs]
      simp only [elemWallUpPath, List.length_append] at hcap
      omega
    rcases appendRowPathCmd_exec x₁ (vertCol y₁) y₁ pfx (s := s₁)
        h1_w hx₁_w hvc_w hy₁_w (by simpa [s₁] using hbuf_w) (by simpa [s₁] using hbuf)
        hcap₁ (by simp [s₁, hr22]) (by simp [s₁, hr23]) (by simp [s₁]) with
      ⟨s₂, t_r, hex₂, ht_r, hbuf₂, hlen1_2, hlen2_2, hr22_2, hr23_2, hregs₂, harrs₂⟩
    have hr26_2 : s₂.regs 26 = d + 1 := by
      rw [hregs₂ 26 (by decide) (by decide) (by decide)]; simp [s₁, hr26]
    let s₃ := s₂.setReg 23 (y₁ + 1)
    have hex₃ : Exec w (.assign 23 (.op .add (.reg 23) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr23_2, hy₁_w, h1_w, hy₁1_w])
    let s₄ := s₃.setReg 26 d
    have hex₄ : Exec w (.assign 26 (.op .sub (.reg 26) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, hr26_2, hd_w, h1_w, hd0_w])
    have hex_body : Exec w appendElemWallUpPathBody s s₄ (t_vc + (t_r + (4 + 4))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
    rcases appendElemWallUpPathCmd_exec x₂ hw2 hx₂_w d (vertCol y₁) (y₁ + 1)
        (pfx ++ rowPath x₁ (vertCol y₁) y₁) (s := s₄)
        hvc_w (by omega) hd0_w (by simpa [s₄, s₃, hlen1_2, s₁] using hbuf_w)
        (by simpa [s₄, s₃] using hbuf₂)
        (by
          simp only [s₄, s₃, State.setReg_arrs, hlen1_2, s₁, List.length_append]
          simpa [elemWallUpPath, List.length_append, Nat.add_assoc] using hcap)
        (by simp [s₄, s₃, hr22_2])
        (by simp [s₄, s₃])
        (by simp [s₄])
        (by simp [s₄, s₃, hregs₂ 27 (by decide) (by decide) (by decide), s₁, hr27]) with
      ⟨s', t_rest, hex_rest, ht_rest, hbuf', hlen1', hlen2', hregs', harrs'⟩
    cases hex_rest with
    | @seq _ _ _ s_mid _ t_l t_end hex_l hex_end =>
      have hpfx_eq :
          (pfx ++ rowPath x₁ (vertCol y₁) y₁) ++ elemWallUpPath x₂ d (vertCol y₁) (y₁ + 1) =
            pfx ++ elemWallUpPath x₂ (d + 1) x₁ y₁ := by
        simp [elemWallUpPath, List.append_assoc]
      rw [hpfx_eq] at hbuf'
      refine ⟨s', (3 + (t_vc + (t_r + (4 + 4))) + t_l) + t_end,
        .seq (.while_true hcond (by omega) hex_body hex_l) hex_end,
        by simp only [elemWallUpPath, List.length_append]; omega,
        hbuf',
        by simpa [s₄, s₃, hlen1_2, s₁] using hlen1',
        by simpa [s₄, s₃, hlen2_2, s₁] using hlen2',
        fun r h7 h22 h23 h24 h25 h26 => by
          rw [hregs' r h7 h22 h23 h24 h25 h26]
          simp [s₄, s₃, hregs₂ r h7 h22 h24, s₁, h23, h25, h26],
        fun a ha1 ha2 => by
          rw [harrs' a ha1 ha2]
          simp [s₄, s₃, harrs₂ a ha1 ha2, s₁]⟩

/-- Build `(elemWallUpPath x₂ d x₁ y₁).map Prod.fst` in `coordXArr` and
`(elemWallUpPath x₂ d x₁ y₁).map Prod.snd` in `coordYArr` (where `x₁ = r_22`, `y₁ = r_23`,
`d = r_26`, `x₂ = r_27`, and `r_12 = elemWallNumVerts h`). -/
def buildElemWallUpPathCmd : Cmd :=
  .seq (.assign 6 (.op .add (.reg 12) (.const 2)))
  (.seq (.alloc bufArr (.reg 6))
  (.seq (.alloc bufArr2 (.reg 6))
  (.seq (.assign 7 (.const 0))
  (.seq appendElemWallUpPathCmd
  (.seq (.assign 8 (.const 0))
  (.seq (.assign 9 (.reg 7))
  (.seq (copySliceToArrCmd bufArr coordXArr)
  (.seq (.assign 8 (.const 0))
  (.seq (.assign 9 (.len coordXArr))
    (copySliceToArrCmd bufArr2 coordYArr))))))))))

theorem mem_elemWallUpPath_bounds {h x₂ : ℕ} (hh : 1 ≤ h) (hx₂ : x₂ < 2 * h + 2) :
    ∀ {d x₁ y₁ : ℕ} {p : ℕ × ℕ},
      x₁ < 2 * h + 2 →
      p ∈ elemWallUpPath x₂ d x₁ y₁ →
      p.1 < 2 * h + 2 ∧ p.2 ≤ y₁ + d
  | 0, x₁, y₁, p, hx₁, hp => by
    unfold elemWallUpPath rowPath at hp
    split_ifs at hp with hle
    · obtain ⟨_, h2, h3⟩ := mem_rowPathUp hp
      exact ⟨by omega, by omega⟩
    · rw [List.mem_reverse] at hp
      obtain ⟨_, h2, h3⟩ := mem_rowPathUp hp
      exact ⟨by omega, by omega⟩
  | d + 1, x₁, y₁, p, hx₁, hp => by
    rw [elemWallUpPath, List.mem_append] at hp
    rcases hp with hp | hp
    · have hvc := vertCol_lt hh y₁
      unfold rowPath at hp
      split_ifs at hp with hle
      · obtain ⟨_, h2, h3⟩ := mem_rowPathUp hp
        exact ⟨by omega, by omega⟩
      · rw [List.mem_reverse] at hp
        obtain ⟨_, h2, h3⟩ := mem_rowPathUp hp
        exact ⟨by omega, by omega⟩
    · obtain ⟨h1, h2⟩ := mem_elemWallUpPath_bounds hh hx₂ (vertCol_lt hh y₁) hp
      exact ⟨h1, by omega⟩

theorem buildElemWallUpPathCmd_exec {w h : ℕ} (hh : 1 ≤ h)
    (x₂ d x₁ y₁ : ℕ) {s : State}
    (hw2 : 2 < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (hx₁ : x₁ < 2 * h + 2)
    (hx₂ : x₂ < 2 * h + 2)
    (hy₁d : y₁ + d ≤ h)
    (hr12 : s.regs 12 = elemWallNumVerts h)
    (hr22 : s.regs 22 = x₁)
    (hr23 : s.regs 23 = y₁)
    (hr26 : s.regs 26 = d)
    (hr27 : s.regs 27 = x₂) :
    let P := elemWallUpPath x₂ d x₁ y₁
    ∃ s' t,
      Exec w buildElemWallUpPathCmd s s' t ∧
      t ≤ 65 * P.length + 50 * d + 2 * elemWallNumVerts h + 80 ∧
      s'.arrs coordXArr = P.map Prod.fst ∧
      s'.arrs coordYArr = P.map Prod.snd ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 11 →
        r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ bufArr → a ≠ bufArr2 → a ≠ coordXArr → a ≠ coordYArr →
        s'.arrs a = s.arrs a) := by
  intro P
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  let cap := elemWallNumVerts h + 2
  have hcap_eq : cap = (h + 1) * (2 * h + 2) := by
    dsimp [cap]
    rw [elemWallNumVerts_eq]
    have : 2 ≤ (h + 1) * (2 * h + 2) := by nlinarith
    omega
  have hVJ_w : elemWallNumVerts h < 2 ^ w := by omega
  have hcap_w : cap < 2 ^ w := by dsimp [cap]; omega
  have hP_le_cap : P.length ≤ cap := by
    rw [hcap_eq]
    calc P.length ≤ (d + 1) * (2 * h + 2) := length_elemWallUpPath_le hh hx₂ d x₁ y₁ hx₁
      _ ≤ (h + 1) * (2 * h + 2) := Nat.mul_le_mul_right _ (by omega)
  have hP_w : P.length < 2 ^ w := by omega
  let s₁ := s.setReg 6 cap
  have hex₁ : Exec w (.assign 6 (.op .add (.reg 12) (.const 2))) s s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr12, hVJ_w, hw2, hcap_w, cap])
  let s₂ := s₁.setArr bufArr (List.replicate cap 0)
  have hex₂ : Exec w (.alloc bufArr (.reg 6)) s₁ s₂ (1 + cap) :=
    .alloc (by simp [Expr.eval, checkWord, s₁, hcap_w])
  let s₃ := s₂.setArr bufArr2 (List.replicate cap 0)
  have hex₃ : Exec w (.alloc bufArr2 (.reg 6)) s₂ s₃ (1 + cap) :=
    .alloc (by simp [Expr.eval, checkWord, s₂, s₁, hcap_w])
  let s₄ := s₃.setReg 7 0
  have hex₄ : Exec w (.assign 7 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hbuf₄ : IsCoordBufPrefix (s₄.arrs bufArr) (s₄.arrs bufArr2) [] (s₄.regs 7) := by
    refine ⟨⟨by simp [s₄], by simp [s₄, s₃, s₂], fun _ hi => by simp at hi⟩,
      ⟨by simp [s₄], by simp [s₄, s₃], fun _ hi => by simp at hi⟩,
      by simp [s₄, s₃, s₂]⟩
  rcases appendElemWallUpPathCmd_exec x₂ hw2 (by omega) d x₁ y₁ [] (s := s₄)
      (by omega) (by omega) (by omega)
      (by simp [s₄, s₃, s₂, hcap_w]) hbuf₄
      (by simp [s₄, s₃, s₂]; exact hP_le_cap)
      (by simp [s₄, s₃, s₂, s₁, hr22])
      (by simp [s₄, s₃, s₂, s₁, hr23])
      (by simp [s₄, s₃, s₂, s₁, hr26])
      (by simp [s₄, s₃, s₂, s₁, hr27]) with
    ⟨s₅, t_up, hex₅, ht_up, hbuf₅, hlen1_5, hlen2_5, hregs₅, harrs₅⟩
  simp only [List.nil_append] at hbuf₅
  have hlen1_5' : (s₅.arrs bufArr).length = cap := by simpa [s₄, s₃, s₂] using hlen1_5
  have hlen2_5' : (s₅.arrs bufArr2).length = cap := by simpa [s₄, s₃] using hlen2_5
  have hr7_5 : s₅.regs 7 = P.length := by simpa using hbuf₅.1.1
  let s₆ := s₅.setReg 8 0
  have hex₆ : Exec w (.assign 8 (.const 0)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₇ := s₆.setReg 9 P.length
  have hex₇ : Exec w (.assign 9 (.reg 7)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₆, hr7_5, hP_w])
  have hwordsX : ∀ v ∈ P.map Prod.fst, v < 2 ^ w := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨p, hp, rfl⟩
    have := (mem_elemWallUpPath_bounds hh hx₂ hx₁ hp).1
    omega
  have hwordsY : ∀ v ∈ P.map Prod.snd, v < 2 ^ w := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨p, hp, rfl⟩
    have := (mem_elemWallUpPath_bounds hh hx₂ hx₁ hp).2
    omega
  rcases copySliceToArrCmd_exec bufArr coordXArr (by decide) (P.map Prod.fst) 0 (s := s₇)
      h1_w (by simp [s₇, s₆, hlen1_5', hcap_w])
      (by simp [s₇, s₆, hlen1_5', hP_le_cap])
      (fun j hj => by
        simp only [s₇, s₆, State.setReg_arrs, Nat.zero_add]
        exact hbuf₅.1.2.2 j hj)
      hwordsX (by simp [s₇, s₆]) (by simp [s₇]) with
    ⟨s₈, t_cx, hex₈, ht_cx, hcx₈, _, hregs₈, harrs₈⟩
  let s₉ := s₈.setReg 8 0
  have hex₉ : Exec w (.assign 8 (.const 0)) s₈ s₉ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₉' := s₉.setReg 9 P.length
  have hex₉' : Exec w (.assign 9 (.len coordXArr)) s₉ s₉' 2 :=
    .assign (eval_len (by simp [s₉, hcx₈]) hP_w)
  have hbuf2_9 : s₉'.arrs bufArr2 = s₅.arrs bufArr2 := by
    simp [s₉', s₉, harrs₈ bufArr2 (by decide), s₇, s₆]
  rcases copySliceToArrCmd_exec bufArr2 coordYArr (by decide) (P.map Prod.snd) 0 (s := s₉')
      h1_w (by rw [hbuf2_9, hlen2_5']; exact hcap_w)
      (by rw [hbuf2_9, hlen2_5']; simpa using hP_le_cap)
      (fun j hj => by
        rw [hbuf2_9, Nat.zero_add]
        exact hbuf₅.2.1.2.2 j hj)
      hwordsY (by simp [s₉', s₉]) (by simp [s₉']) with
    ⟨s₁₀, t_cy, hex₁₀, ht_cy, hcy₁₀, _, hregs₁₀, harrs₁₀⟩
  have hcx₁₀ : s₁₀.arrs coordXArr = P.map Prod.fst := by
    rw [harrs₁₀ coordXArr (by decide)]
    simpa [s₉', s₉] using hcx₈
  refine ⟨s₁₀,
    4 + ((1 + cap) + ((1 + cap) + (2 + (t_up + (2 + (2 + (t_cx + (2 + (2 + t_cy))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₉' hex₁₀))))))))),
    by simp only [List.length_map] at ht_cx ht_cy; dsimp [P, cap] at ht_up ht_cx ht_cy ⊢; omega,
    hcx₁₀, hcy₁₀,
    fun r h6 h7 h8 h9 h11 h22 h23 h24 h25 h26 => by
      rw [hregs₁₀ r h7 h8 h9 h11]
      dsimp only [s₉', s₉]
      rw [State.setReg_regs_ne _ _ h9, State.setReg_regs_ne _ _ h8, hregs₈ r h7 h8 h9 h11]
      dsimp only [s₇, s₆]
      rw [State.setReg_regs_ne _ _ h9, State.setReg_regs_ne _ _ h8,
        hregs₅ r h7 h22 h23 h24 h25 h26]
      simp [s₄, s₃, s₂, s₁, h6, h7],
    fun a ha1 ha2 ha3 ha4 => by
      rw [harrs₁₀ a ha4]
      dsimp only [s₉', s₉]
      rw [State.setReg_arrs, State.setReg_arrs, harrs₈ a ha3]
      dsimp only [s₇, s₆]
      rw [State.setReg_arrs, State.setReg_arrs, harrs₅ a ha1 ha2]
      simp [s₄, s₃, s₂, s₁, ha1, ha2]⟩

/-! ### Section 2: `buildElemWallCanonicalPathCmd`, `buildElemWallEdgeCanonicalPathCmd`, and `elemPathForVertCmd` -/

/-- Reverse `(coordXArr, coordYArr)` in place using `bufArr`. -/
def reverseCoordsCmd : Cmd :=
  .seq (reverseArrCmd coordXArr bufArr)
    (.seq (copyArrCmd bufArr coordXArr)
      (.seq (reverseArrCmd coordYArr bufArr)
        (copyArrCmd bufArr coordYArr)))

theorem reverseCoordsCmd_exec {w : ℕ} (L : List (ℕ × ℕ)) {s : State}
    (hw1 : 1 < 2 ^ w)
    (hL_w : L.length < 2 ^ w)
    (hX_w : ∀ v ∈ L, v.1 < 2 ^ w)
    (hY_w : ∀ v ∈ L, v.2 < 2 ^ w)
    (hcx : s.arrs coordXArr = L.map Prod.fst)
    (hcy : s.arrs coordYArr = L.map Prod.snd) :
    ∃ s' t,
      Exec w reverseCoordsCmd s s' t ∧
      t ≤ 88 * L.length + 52 ∧
      s'.arrs coordXArr = L.reverse.map Prod.fst ∧
      s'.arrs coordYArr = L.reverse.map Prod.snd ∧
      (∀ r : Reg, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ bufArr → a ≠ coordXArr → a ≠ coordYArr → s'.arrs a = s.arrs a) := by
  have hwordsX : ∀ v ∈ L.map Prod.fst, v < 2 ^ w := by
    intro v hv; rcases List.mem_map.mp hv with ⟨p, hp, rfl⟩; exact hX_w p hp
  have hwordsY : ∀ v ∈ L.map Prod.snd, v < 2 ^ w := by
    intro v hv; rcases List.mem_map.mp hv with ⟨p, hp, rfl⟩; exact hY_w p hp
  rcases reverseArrCmd_exec coordXArr bufArr (by decide) (s := s) hw1
      (by rw [hcx, List.length_map]; exact hL_w)
      (by rw [hcx]; exact hwordsX) with
    ⟨s₁, t₁, hex₁, ht₁, hbuf1, hregs₁, harrs₁⟩
  rw [hcx] at hbuf1 ht₁
  rcases copyArrCmd_exec bufArr coordXArr (by decide) (s := s₁) hw1
      (by rw [hbuf1, List.length_reverse, List.length_map]; exact hL_w)
      (by rw [hbuf1]; intro v hv; exact hwordsX v (List.mem_reverse.mp hv)) with
    ⟨s₂, t₂, hex₂, ht₂, hcx2, hregs₂, harrs₂⟩
  rw [hbuf1] at hcx2 ht₂
  have hcy2 : s₂.arrs coordYArr = L.map Prod.snd := by
    rw [harrs₂ coordYArr (by decide), harrs₁ coordYArr (by decide), hcy]
  rcases reverseArrCmd_exec coordYArr bufArr (by decide) (s := s₂) hw1
      (by rw [hcy2, List.length_map]; exact hL_w)
      (by rw [hcy2]; exact hwordsY) with
    ⟨s₃, t₃, hex₃, ht₃, hbuf3, hregs₃, harrs₃⟩
  rw [hcy2] at hbuf3 ht₃
  rcases copyArrCmd_exec bufArr coordYArr (by decide) (s := s₃) hw1
      (by rw [hbuf3, List.length_reverse, List.length_map]; exact hL_w)
      (by rw [hbuf3]; intro v hv; exact hwordsY v (List.mem_reverse.mp hv)) with
    ⟨s₄, t₄, hex₄, ht₄, hcy4, hregs₄, harrs₄⟩
  rw [hbuf3] at hcy4 ht₄
  have hcx4 : s₄.arrs coordXArr = L.reverse.map Prod.fst := by
    rw [harrs₄ coordXArr (by decide), harrs₃ coordXArr (by decide), hcx2, List.map_reverse]
  rw [← List.map_reverse] at hcy4
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by simp only [List.length_reverse, List.length_map] at ht₁ ht₂ ht₃ ht₄; omega,
    hcx4, hcy4,
    fun r h7 h8 h9 h11 => by
      rw [hregs₄ r h7 h8 h9 h11, hregs₃ r h7 h9 h11, hregs₂ r h7 h8 h9 h11, hregs₁ r h7 h9 h11],
    fun a ha1 ha2 ha3 => by
      rw [harrs₄ a ha3, harrs₃ a ha1, harrs₂ a ha2, harrs₁ a ha1]⟩

/-- Build `(elemWallCanonicalPath p q).map Prod.fst` in `coordXArr` and
`(elemWallCanonicalPath p q).map Prod.snd` in `coordYArr` from `p = (r_18, r_19)` and
`q = (r_20, r_21)`. -/
def buildElemWallCanonicalPathCmd : Cmd :=
  .ite (exprLe (.reg 19) (.reg 21))
    (.seq (.assign 22 (.reg 18))
      (.seq (.assign 23 (.reg 19))
        (.seq (.assign 26 (.op .sub (.reg 21) (.reg 19)))
          (.seq (.assign 27 (.reg 20))
            buildElemWallUpPathCmd))))
    (.seq (.assign 22 (.reg 20))
      (.seq (.assign 23 (.reg 21))
        (.seq (.assign 26 (.op .sub (.reg 19) (.reg 21)))
          (.seq (.assign 27 (.reg 18))
            (.seq buildElemWallUpPathCmd
              reverseCoordsCmd)))))

theorem buildElemWallCanonicalPathCmd_exec {w h : ℕ} (hh : 1 ≤ h)
    (p q : ℕ × ℕ) {s : State}
    (hw2 : 2 < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (hp1 : p.1 < 2 * h + 2) (hp2 : p.2 ≤ h)
    (hq1 : q.1 < 2 * h + 2) (hq2 : q.2 ≤ h)
    (hr12 : s.regs 12 = elemWallNumVerts h)
    (hr18 : s.regs 18 = p.1)
    (hr19 : s.regs 19 = p.2)
    (hr20 : s.regs 20 = q.1)
    (hr21 : s.regs 21 = q.2) :
    let P := elemWallCanonicalPath p q
    ∃ s' t,
      Exec w buildElemWallCanonicalPathCmd s s' t ∧
      t ≤ 153 * P.length + 50 * h + 2 * elemWallNumVerts h + 155 ∧
      s'.arrs coordXArr = P.map Prod.fst ∧
      s'.arrs coordYArr = P.map Prod.snd ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 11 →
        r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ bufArr → a ≠ bufArr2 → a ≠ coordXArr → a ≠ coordYArr →
        s'.arrs a = s.arrs a) := by
  intro P
  have h1_w : 1 < 2 ^ w := by omega
  have hp1_w : p.1 < 2 ^ w := by omega
  have hp2_w : p.2 < 2 ^ w := by omega
  have hq1_w : q.1 < 2 ^ w := by omega
  have hq2_w : q.2 < 2 ^ w := by omega
  have he19 : (Expr.reg 19).eval w s = some p.2 := by simp [Expr.eval, checkWord, hr19, hp2_w]
  have he21 : (Expr.reg 21).eval w s = some q.2 := by simp [Expr.eval, checkWord, hr21, hq2_w]
  have hcond := eval_exprLe h1_w he19 he21
  by_cases hle : p.2 ≤ q.2
  · rw [if_pos hle] at hcond
    let d := q.2 - p.2
    have hd_w : d < 2 ^ w := by omega
    have hP_eq : P = elemWallUpPath q.1 d p.1 p.2 := by simp [P, elemWallCanonicalPath, hle, d]
    let s₁ := s.setReg 22 p.1
    have hex₁ : Exec w (.assign 22 (.reg 18)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, hr18, hp1_w])
    let s₂ := s₁.setReg 23 p.2
    have hex₂ : Exec w (.assign 23 (.reg 19)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, s₁, hr19, hp2_w])
    let s₃ := s₂.setReg 26 d
    have hex₃ : Exec w (.assign 26 (.op .sub (.reg 21) (.reg 19))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hr21, hr19, hq2_w, hp2_w, hd_w, d])
    let s₄ := s₃.setReg 27 q.1
    have hex₄ : Exec w (.assign 27 (.reg 20)) s₃ s₄ 2 :=
      .assign (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hr20, hq1_w])
    rcases buildElemWallUpPathCmd_exec hh q.1 d p.1 p.2 (s := s₄)
        hw2 hVJW_w hp1 hq1 (by omega)
        (by simp [s₄, s₃, s₂, s₁, hr12])
        (by simp [s₄, s₃, s₂, s₁])
        (by simp [s₄, s₃, s₂])
        (by simp [s₄, s₃])
        (by simp [s₄]) with
      ⟨s', t_u, hex_u, ht_u, hcx', hcy', hregs', harrs'⟩
    have hd_le : d ≤ h := by omega
    refine ⟨s', _, .ite_true hcond (by omega) (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex_u)))),
      by simp [exprLe, Expr.cost]; rw [← hP_eq] at ht_u; omega,
      by rwa [hP_eq], by rwa [hP_eq],
      fun r h6 h7 h8 h9 h11 h22 h23 h24 h25 h26 h27 => by
        rw [hregs' r h6 h7 h8 h9 h11 h22 h23 h24 h25 h26]
        simp [s₄, s₃, s₂, s₁, h22, h23, h26, h27],
      harrs'⟩
  · rw [if_neg hle] at hcond
    let d := p.2 - q.2
    have hd_w : d < 2 ^ w := by omega
    let L := elemWallUpPath p.1 d q.1 q.2
    have hP_eq : P = L.reverse := by simp [P, elemWallCanonicalPath, hle, L, d]
    have hL_len : L.length = P.length := by rw [hP_eq, List.length_reverse]
    let s₁ := s.setReg 22 q.1
    have hex₁ : Exec w (.assign 22 (.reg 20)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, hr20, hq1_w])
    let s₂ := s₁.setReg 23 q.2
    have hex₂ : Exec w (.assign 23 (.reg 21)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, s₁, hr21, hq2_w])
    let s₃ := s₂.setReg 26 d
    have hex₃ : Exec w (.assign 26 (.op .sub (.reg 19) (.reg 21))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hr19, hr21, hp2_w, hq2_w, hd_w, d])
    let s₄ := s₃.setReg 27 p.1
    have hex₄ : Exec w (.assign 27 (.reg 18)) s₃ s₄ 2 :=
      .assign (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hr18, hp1_w])
    rcases buildElemWallUpPathCmd_exec hh p.1 d q.1 q.2 (s := s₄)
        hw2 hVJW_w hq1 hp1 (by omega)
        (by simp [s₄, s₃, s₂, s₁, hr12])
        (by simp [s₄, s₃, s₂, s₁])
        (by simp [s₄, s₃, s₂])
        (by simp [s₄, s₃])
        (by simp [s₄]) with
      ⟨s₅, t_u, hex₅, ht_u, hcx₅, hcy₅, hregs₅, harrs₅⟩
    have hL_w : L.length < 2 ^ w := by
      have h1 := length_elemWallUpPath_le hh hp1 d q.1 q.2 hq1
      have h2 : (d + 1) * (2 * h + 2) ≤ (h + 1) * (2 * h + 2) := Nat.mul_le_mul_right _ (by omega)
      have h3 := elemWallNumVerts_eq h
      have : 2 ≤ (h + 1) * (2 * h + 2) := by nlinarith
      dsimp [L]; omega
    rcases reverseCoordsCmd_exec L (s := s₅) h1_w hL_w
        (fun v hv => by have := (mem_elemWallUpPath_bounds hh hp1 hq1 hv).1; omega)
        (fun v hv => by have := (mem_elemWallUpPath_bounds hh hp1 hq1 hv).2; omega)
        hcx₅ hcy₅ with
      ⟨s', t_rev, hex_rev, ht_rev, hcx', hcy', hregs', harrs'⟩
    have hd_le : d ≤ h := by omega
    refine ⟨s', _,
      .ite_false hcond (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex_rev))))),
      by simp [exprLe, Expr.cost]; rw [hL_len] at ht_u ht_rev; omega,
      by rwa [hP_eq], by rwa [hP_eq],
      fun r h6 h7 h8 h9 h11 h22 h23 h24 h25 h26 h27 => by
        rw [hregs' r h7 h8 h9 h11, hregs₅ r h6 h7 h8 h9 h11 h22 h23 h24 h25 h26]
        simp [s₄, s₃, s₂, s₁, h22, h23, h26, h27],
      fun a ha1 ha2 ha3 ha4 => by
        rw [harrs' a ha1 ha3 ha4, harrs₅ a ha1 ha2 ha3 ha4]; rfl⟩

/-- Loop body of `findFirstCoordLoop`: checks whether `(coordXArr[r_8], coordYArr[r_8]) = (r_28, r_29)`,
sets `r_10 := 0` if equal else `1`, and adds `r_10` to `r_8`. -/
def findFirstCoordBody : Cmd :=
  .seq (.assign 6 (.read coordXArr (.reg 8)))
    (.seq (.assign 11 (.read coordYArr (.reg 8)))
      (.seq (.assign 10 (exprNot (exprAnd (exprEq (.reg 6) (.reg 28)) (exprEq (.reg 11) (.reg 29)))))
        (.assign 8 (.op .add (.reg 8) (.reg 10)))))

/-- Loop scanning `(coordXArr, coordYArr)` from `r_8` for `(r_28, r_29)`. -/
def findFirstCoordLoop : Cmd :=
  .while (.op .mul (.op .lt (.reg 8) (.len coordXArr)) (.reg 10))
    findFirstCoordBody

theorem findFirstCoordLoop_exec {w : ℕ} (p₂ : ℕ × ℕ)
    (hw1 : 1 < 2 ^ w) (hp₂1_w : p₂.1 < 2 ^ w) (hp₂2_w : p₂.2 < 2 ^ w) :
    ∀ (L : List (ℕ × ℕ)) (off : ℕ) {s : State}
      (_hsrc_w : (s.arrs coordXArr).length < 2 ^ w)
      (_hlenX : off + L.length = (s.arrs coordXArr).length)
      (_hlenY : (s.arrs coordYArr).length = (s.arrs coordXArr).length)
      (_hX_w : ∀ q ∈ L, q.1 < 2 ^ w)
      (_hY_w : ∀ q ∈ L, q.2 < 2 ^ w)
      (_hget : ∀ j (hj : j < L.length),
        (s.arrs coordXArr)[off + j]? = some (L[j]'hj).1 ∧
        (s.arrs coordYArr)[off + j]? = some (L[j]'hj).2)
      (_hr8 : s.regs 8 = off)
      (_hr10 : s.regs 10 = 1)
      (_hr28 : s.regs 28 = p₂.1)
      (_hr29 : s.regs 29 = p₂.2),
      ∃ s' t,
        Exec w findFirstCoordLoop s s' t ∧
        t ≤ 45 * L.length + 7 ∧
        s'.regs 8 + (suffixFrom p₂ L).length = (s.arrs coordXArr).length ∧
        (∀ j (hj : j < (suffixFrom p₂ L).length),
          (s.arrs coordXArr)[s'.regs 8 + j]? = some ((suffixFrom p₂ L)[j]'hj).1 ∧
          (s.arrs coordYArr)[s'.regs 8 + j]? = some ((suffixFrom p₂ L)[j]'hj).2) ∧
        (∀ r : Reg, r ≠ 6 → r ≠ 8 → r ≠ 10 → r ≠ 11 → s'.regs r = s.regs r) ∧
        s'.arrs = s.arrs
  | [], off, s, hsrc_w, hlenX, _, _, _, _, hr8, hr10, _, _ => by
    simp only [List.length_nil, Nat.add_zero] at hlenX
    have hlt : (Expr.op .lt (.reg 8) (.len coordXArr)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8, hlenX, hsrc_w]
    have hr10_eval : (Expr.reg 10).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hr10, hw1]
    have hcond : (Expr.op .mul (.op .lt (.reg 8) (.len coordXArr)) (.reg 10)).eval w s = some 0 := by
      simpa using eval_op_mul hlt hr10_eval (by omega)
    refine ⟨s, _, .while_false hcond, by simp [Expr.cost],
      by simp [suffixFrom, hr8, hlenX],
      fun j hj => by simp [suffixFrom] at hj,
      fun _ _ _ _ _ => rfl, rfl⟩
  | a :: rest, off, s, hsrc_w, hlenX, hlenY, hX_w, hY_w, hget, hr8, hr10, hr28, hr29 => by
    have h0_w : 0 < 2 ^ w := by omega
    simp only [List.length_cons] at hlenX
    have hoff_ltX : off < (s.arrs coordXArr).length := by omega
    have hoff_ltY : off < (s.arrs coordYArr).length := by omega
    have hoff_w : off < 2 ^ w := by omega
    have ha1_w : a.1 < 2 ^ w := hX_w a List.mem_cons_self
    have ha2_w : a.2 < 2 ^ w := hY_w a List.mem_cons_self
    have hlt : (Expr.op .lt (.reg 8) (.len coordXArr)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8, hoff_w, hsrc_w, hoff_ltX, hw1]
    have hr10_eval : (Expr.reg 10).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hr10, hw1]
    have hcond : (Expr.op .mul (.op .lt (.reg 8) (.len coordXArr)) (.reg 10)).eval w s = some 1 := by
      simpa using eval_op_mul hlt hr10_eval (by omega)
    have hgetX0 : (s.arrs coordXArr)[off]'hoff_ltX = a.1 := by
      have h := (hget 0 (by simp)).1
      simp only [Nat.add_zero, List.getElem_cons_zero] at h
      exact getElem_of_getElem? h hoff_ltX
    have hgetY0 : (s.arrs coordYArr)[off]'hoff_ltY = a.2 := by
      have h := (hget 0 (by simp)).2
      simp only [Nat.add_zero, List.getElem_cons_zero] at h
      exact getElem_of_getElem? h hoff_ltY
    let s₁ := s.setReg 6 a.1
    have hex₁ : Exec w (.assign 6 (.read coordXArr (.reg 8))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr8, hoff_w, hoff_ltX, hgetX0, ha1_w])
    let s₂ := s₁.setReg 11 a.2
    have hex₂ : Exec w (.assign 11 (.read coordYArr (.reg 8))) s₁ s₂ 3 :=
      .assign (by simp [Expr.eval, checkWord, s₁, hr8, hoff_w, hoff_ltY, hgetY0, ha2_w])
    let b : ℕ := if a = p₂ then 0 else 1
    have hb_w : b < 2 ^ w := by dsimp [b]; split_ifs <;> omega
    have heval_neq :
        (exprNot (exprAnd (exprEq (.reg 6) (.reg 28)) (exprEq (.reg 11) (.reg 29)))).eval w s₂ =
          some b := by
      have he6 : (Expr.reg 6).eval w s₂ = some a.1 := by simp [Expr.eval, checkWord, s₂, s₁, ha1_w]
      have he28 : (Expr.reg 28).eval w s₂ = some p₂.1 := by simp [Expr.eval, checkWord, s₂, s₁, hr28, hp₂1_w]
      have he11 : (Expr.reg 11).eval w s₂ = some a.2 := by simp [Expr.eval, checkWord, s₂, ha2_w]
      have he29 : (Expr.reg 29).eval w s₂ = some p₂.2 := by simp [Expr.eval, checkWord, s₂, s₁, hr29, hp₂2_w]
      have h1 : (exprEq (.reg 6) (.reg 28)).eval w s₂ = some (if decide (a.1 = p₂.1) then 1 else 0) := by
        simpa using eval_exprEq hw1 he6 he28
      have h2 : (exprEq (.reg 11) (.reg 29)).eval w s₂ = some (if decide (a.2 = p₂.2) then 1 else 0) := by
        simpa using eval_exprEq hw1 he11 he29
      have hand := eval_exprAnd_bool hw1 h1 h2
      have hnot := eval_exprNot_bool hw1 hand
      rw [hnot]
      dsimp [b]
      by_cases hap : a = p₂
      · subst hap; simp
      · have hne_coord : ¬ (a.1 = p₂.1 ∧ a.2 = p₂.2) := fun ⟨h1, h2⟩ => hap (Prod.ext h1 h2)
        simp [hap, hne_coord]
    let s₃ := s₂.setReg 10 b
    have hex₃ : Exec w (.assign 10 (exprNot (exprAnd (exprEq (.reg 6) (.reg 28)) (exprEq (.reg 11) (.reg 29)))))
        s₂ s₃ ((exprNot (exprAnd (exprEq (.reg 6) (.reg 28)) (exprEq (.reg 11) (.reg 29)))).cost + 1) :=
      .assign heval_neq
    have hoff_b_w : off + b < 2 ^ w := by dsimp [b]; split_ifs <;> omega
    let s₄ := s₃.setReg 8 (off + b)
    have hex₄ : Exec w (.assign 8 (.op .add (.reg 8) (.reg 10))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hr8, hoff_w, hb_w, hoff_b_w])
    have hex_body : Exec w findFirstCoordBody s s₄
        (3 + (3 + (((exprNot (exprAnd (exprEq (.reg 6) (.reg 28)) (exprEq (.reg 11) (.reg 29)))).cost + 1) + 4))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
    by_cases hap : a = p₂
    · subst hap
      have hb0 : b = 0 := by simp [b]
      have hlt₄ : (Expr.op .lt (.reg 8) (.len coordXArr)).eval w s₄ = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₄, s₃, s₂, s₁, hb0, hoff_w, hsrc_w, hoff_ltX, hw1]
      have hr10_4 : (Expr.reg 10).eval w s₄ = some 0 := by
        simp [Expr.eval, checkWord, s₄, s₃, hb0, h0_w]
      have hcond₄ : (Expr.op .mul (.op .lt (.reg 8) (.len coordXArr)) (.reg 10)).eval w s₄ = some 0 := by
        simpa using eval_op_mul hlt₄ hr10_4 (by omega)
      have hex_end : Exec w findFirstCoordLoop s₄ s₄
          (Expr.op .mul (.op .lt (.reg 8) (.len coordXArr)) (.reg 10)).cost :=
        .while_false hcond₄
      refine ⟨s₄, _, .while_true hcond (by omega) hex_body hex_end,
        by simp [exprNot, exprAnd, exprEq, Expr.cost]; omega,
        by simp [s₄, hb0, suffixFrom, hlenX],
        fun j hj => by
          simp only [s₄, s₃, s₂, s₁, hb0, Nat.add_zero, State.setReg_regs_self]
          have h := hget j (by simpa [suffixFrom] using hj)
          simpa [suffixFrom] using h,
        fun r h6 h8 h10 h11 => by simp [s₄, s₃, s₂, s₁, h6, h8, h10, h11],
        rfl⟩
    · have hb1 : b = 1 := by simp [b, hap]
      rcases findFirstCoordLoop_exec p₂ hw1 hp₂1_w hp₂2_w rest (off + 1) (s := s₄)
          (by simp [s₄, s₃, s₂, s₁, hsrc_w])
          (by simp [s₄, s₃, s₂, s₁]; omega)
          (by simp [s₄, s₃, s₂, s₁, hlenY])
          (fun q hq => hX_w q (List.mem_cons_of_mem a hq))
          (fun q hq => hY_w q (List.mem_cons_of_mem a hq))
          (fun j hj => by
            simp only [s₄, s₃, s₂, s₁, State.setReg_arrs]
            rw [show off + 1 + j = off + (j + 1) by omega]
            exact hget (j + 1) (by simp; omega))
          (by simp [s₄, hb1])
          (by simp [s₄, s₃, hb1])
          (by simp [s₄, s₃, s₂, s₁, hr28])
          (by simp [s₄, s₃, s₂, s₁, hr29]) with
        ⟨s', t_rest, hex_rest, ht_rest, hlen', hget', hregs', harrs'⟩
      have hsuf : suffixFrom p₂ (a :: rest) = suffixFrom p₂ rest := by
        simp [suffixFrom, hap]
      refine ⟨s', _, .while_true hcond (by omega) hex_body hex_rest,
        by simp [exprNot, exprAnd, exprEq, Expr.cost]; omega,
        by simpa [hsuf, s₄, s₃, s₂, s₁] using hlen',
        fun j hj => by
          have h := hget' j (by simpa [hsuf] using hj)
          simpa [hsuf, s₄, s₃, s₂, s₁] using h,
        fun r h6 h8 h10 h11 => by rw [hregs' r h6 h8 h10 h11]; simp [s₄, s₃, s₂, s₁, h6, h8, h10, h11],
        harrs'⟩

/-- Prepend `headCoord = (r_22, r_23)` to the slice `[r_8 .. len coordXArr)` of
`(coordXArr, coordYArr)` and copy the result back to `(coordXArr, coordYArr)`. -/
def prependCoordAndSliceCmd : Cmd :=
  .seq (.assign 24 (.reg 8))
  (.seq (.assign 25 (.op .sub (.len coordXArr) (.reg 24)))
  (.seq (.assign 26 (.op .add (.const 1) (.reg 25)))
  (.seq (.alloc bufArr (.reg 26))
  (.seq (.write bufArr (.const 0) (.reg 22))
  (.seq (.assign 7 (.const 1))
  (.seq (.assign 8 (.reg 24))
  (.seq (.assign 9 (.reg 25))
  (.seq (appendForwardSlice6Loop coordXArr bufArr)
  (.seq (.alloc bufArr2 (.reg 26))
  (.seq (.write bufArr2 (.const 0) (.reg 23))
  (.seq (.assign 7 (.const 1))
  (.seq (.assign 8 (.reg 24))
  (.seq (.assign 9 (.reg 25))
  (.seq (appendForwardSlice6Loop coordYArr bufArr2)
  (.seq (copyArrCmd bufArr coordXArr)
    (copyArrCmd bufArr2 coordYArr))))))))))))))))

theorem prependCoordAndSliceCmd_exec {w : ℕ} (headCoord : ℕ × ℕ) (tailList : List (ℕ × ℕ))
    (off : ℕ) {s : State}
    (hw1 : 1 < 2 ^ w)
    (hh1_w : headCoord.1 < 2 ^ w)
    (hh2_w : headCoord.2 < 2 ^ w)
    (hsrc_w : (s.arrs coordXArr).length + 1 < 2 ^ w)
    (hlenX : off + tailList.length = (s.arrs coordXArr).length)
    (hlenY : (s.arrs coordYArr).length = (s.arrs coordXArr).length)
    (hX_w : ∀ q ∈ tailList, q.1 < 2 ^ w)
    (hY_w : ∀ q ∈ tailList, q.2 < 2 ^ w)
    (hget : ∀ j (hj : j < tailList.length),
      (s.arrs coordXArr)[off + j]? = some (tailList[j]'hj).1 ∧
      (s.arrs coordYArr)[off + j]? = some (tailList[j]'hj).2)
    (hr8 : s.regs 8 = off)
    (hr22 : s.regs 22 = headCoord.1)
    (hr23 : s.regs 23 = headCoord.2) :
    ∃ s' t,
      Exec w prependCoordAndSliceCmd s s' t ∧
      t ≤ 90 * tailList.length + 120 ∧
      s'.arrs coordXArr = (headCoord :: tailList).map Prod.fst ∧
      s'.arrs coordYArr = (headCoord :: tailList).map Prod.snd ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 11 →
        r ≠ 24 → r ≠ 25 → r ≠ 26 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ bufArr → a ≠ bufArr2 → a ≠ coordXArr → a ≠ coordYArr →
        s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hoff_w : off < 2 ^ w := by omega
  have htail_w : tailList.length < 2 ^ w := by omega
  have h1tail_w : 1 + tailList.length < 2 ^ w := by omega
  have hcx_w : (s.arrs coordXArr).length < 2 ^ w := by omega
  have hsub_len : (s.arrs coordXArr).length - off = tailList.length := by omega
  let s₁ := s.setReg 24 off
  have hex₁ : Exec w (.assign 24 (.reg 8)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr8, hoff_w])
  let s₂ := s₁.setReg 25 tailList.length
  have hex₂ : Exec w (.assign 25 (.op .sub (.len coordXArr) (.reg 24))) s₁ s₂ 4 :=
    .assign (by
      rw [← hsub_len]
      exact eval_op_sub (eval_len rfl (by simpa [s₁] using hcx_w))
        (by simp [Expr.eval, checkWord, s₁, hoff_w]))
  let s₃ := s₂.setReg 26 (1 + tailList.length)
  have hex₃ : Exec w (.assign 26 (.op .add (.const 1) (.reg 25))) s₂ s₃ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, hw1, htail_w, h1tail_w])
  let s₄ := s₃.setArr bufArr (List.replicate (1 + tailList.length) 0)
  have hex₄ : Exec w (.alloc bufArr (.reg 26)) s₃ s₄ (1 + (1 + tailList.length)) :=
    .alloc (by simp [Expr.eval, checkWord, s₃, h1tail_w])
  let s₅ := s₄.writeArr bufArr 0 headCoord.1
  have hex₅ : Exec w (.write bufArr (.const 0) (.reg 22)) s₄ s₅ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, s₄, s₃, s₂, s₁, hr22, hh1_w])
      (by simp [s₄])
  let s₆ := s₅.setReg 7 1
  have hex₆ : Exec w (.assign 7 (.const 1)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw1])
  let s₇ := s₆.setReg 8 off
  have hex₇ : Exec w (.assign 8 (.reg 24)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₆, s₅, s₄, s₃, s₂, s₁, hoff_w])
  let s₈ := s₇.setReg 9 tailList.length
  have hex₈ : Exec w (.assign 9 (.reg 25)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₇, s₆, s₅, s₄, s₃, s₂, htail_w])
  have hbuf₈ : IsArrBufPrefix (s₈.arrs bufArr) [headCoord.1] (s₈.regs 7) := by
    refine ⟨by simp [s₈, s₇, s₆], by simp [s₈, s₇, s₆, s₅, s₄], fun i hi => ?_⟩
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simp [s₈, s₇, s₆, s₅, s₄, State.writeArr_arrs_self]
  have hwordsX : ∀ v ∈ tailList.map Prod.fst, v < 2 ^ w := by
    intro v hv; rcases List.mem_map.mp hv with ⟨q, hq, rfl⟩; exact hX_w q hq
  rcases appendForwardSlice6Loop_exec coordXArr bufArr (by decide) hw1
      (tailList.map Prod.fst) off [headCoord.1] (s := s₈)
      (by simp; omega)
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne]; omega)
      (fun j hj => by
        simp only [List.length_map] at hj
        simp only [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg_arrs,
          State.writeArr_arrs_ne _ _ _ (by decide : coordXArr ≠ bufArr),
           State.setArr_arrs_ne _ _ (by decide : coordXArr ≠ bufArr), List.getElem_map]
        exact (hget j hj).1)
      hwordsX hbuf₈
      (by simp [s₈, s₇, s₆, s₅, s₄, State.writeArr_arrs_self])
      (by simp [s₈, s₇, s₆, s₅, s₄, State.writeArr_arrs_self]; omega)
      (by simp [s₈, s₇]) (by simp [s₈]) with
    ⟨s₉, t_fx, hex₉, ht_fx, hbuf₉, hlen1_9, _, _, hregs₉, harrs₉⟩
  have hbuf₉_eq : s₉.arrs bufArr = (headCoord :: tailList).map Prod.fst := by
    apply hbuf₉.to_eq
    simpa [s₈, s₇, s₆, s₅, s₄, State.writeArr_arrs_self, Nat.add_comm] using hlen1_9
  have hr26_9 : s₉.regs 26 = 1 + tailList.length := by
    rw [hregs₉ 26 (by decide) (by decide) (by decide) (by decide)]
    simp [s₈, s₇, s₆, s₅, s₄, s₃]
  let s₁₀ := s₉.setArr bufArr2 (List.replicate (1 + tailList.length) 0)
  have hex₁₀ : Exec w (.alloc bufArr2 (.reg 26)) s₉ s₁₀ (1 + (1 + tailList.length)) :=
    .alloc (by simp [Expr.eval, checkWord, hr26_9, h1tail_w])
  have hr23_10 : s₁₀.regs 23 = headCoord.2 := by
    simp only [s₁₀, State.setArr_regs]
    rw [hregs₉ 23 (by decide) (by decide) (by decide) (by decide)]
    simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr23]
  let s₁₁ := s₁₀.writeArr bufArr2 0 headCoord.2
  have hex₁₁ : Exec w (.write bufArr2 (.const 0) (.reg 23)) s₁₀ s₁₁ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, hr23_10, hh2_w])
      (by simp [s₁₀])
  let s₁₂ := s₁₁.setReg 7 1
  have hex₁₂ : Exec w (.assign 7 (.const 1)) s₁₁ s₁₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw1])
  have hr24_12 : s₁₂.regs 24 = off := by
    simp only [s₁₂, s₁₁, s₁₀, State.setReg_regs_ne _ _ (by decide : (24 : Reg) ≠ 7),
      State.writeArr_regs, State.setArr_regs]
    rw [hregs₉ 24 (by decide) (by decide) (by decide) (by decide)]
    simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁]
  let s₁₃ := s₁₂.setReg 8 off
  have hex₁₃ : Exec w (.assign 8 (.reg 24)) s₁₂ s₁₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr24_12, hoff_w])
  have hr25_13 : s₁₃.regs 25 = tailList.length := by
    simp only [s₁₃, s₁₂, s₁₁, s₁₀, State.setReg_regs_ne _ _ (by decide : (25 : Reg) ≠ 8),
      State.setReg_regs_ne _ _ (by decide : (25 : Reg) ≠ 7), State.writeArr_regs, State.setArr_regs]
    rw [hregs₉ 25 (by decide) (by decide) (by decide) (by decide)]
    simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂]
  let s₁₄ := s₁₃.setReg 9 tailList.length
  have hex₁₄ : Exec w (.assign 9 (.reg 25)) s₁₃ s₁₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr25_13, htail_w])
  have hbuf₁₄ : IsArrBufPrefix (s₁₄.arrs bufArr2) [headCoord.2] (s₁₄.regs 7) := by
    refine ⟨by simp [s₁₄, s₁₃, s₁₂], by simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀], fun i hi => ?_⟩
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, State.writeArr_arrs_self]
  have hcy₁₄ : s₁₄.arrs coordYArr = s.arrs coordYArr := by
    simp only [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, State.setReg_arrs,
      State.writeArr_arrs_ne _ _ _ (by decide : coordYArr ≠ bufArr2),
      State.setArr_arrs_ne _ _ (by decide : coordYArr ≠ bufArr2)]
    rw [harrs₉ coordYArr (by decide)]
    simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne]
  have hwordsY : ∀ v ∈ tailList.map Prod.snd, v < 2 ^ w := by
    intro v hv; rcases List.mem_map.mp hv with ⟨q, hq, rfl⟩; exact hY_w q hq
  rcases appendForwardSlice6Loop_exec coordYArr bufArr2 (by decide) hw1
      (tailList.map Prod.snd) off [headCoord.2] (s := s₁₄)
      (by simp; omega)
      (by rw [hcy₁₄, hlenY]; simp; omega)
      (fun j hj => by
        simp only [List.length_map] at hj
        rw [hcy₁₄, List.getElem_map]
        exact (hget j hj).2)
      hwordsY hbuf₁₄
      (by simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, State.writeArr_arrs_self])
      (by simp [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, State.writeArr_arrs_self]; omega)
      (by simp [s₁₄, s₁₃]) (by simp [s₁₄]) with
    ⟨s₁₅, t_fy, hex₁₅, ht_fy, hbuf₁₅, hlen2_15, _, _, hregs₁₅, harrs₁₅⟩
  have hbuf₁₅_eq : s₁₅.arrs bufArr2 = (headCoord :: tailList).map Prod.snd := by
    apply hbuf₁₅.to_eq
    simpa [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, State.writeArr_arrs_self, Nat.add_comm] using hlen2_15
  have hbuf1_15 : s₁₅.arrs bufArr = (headCoord :: tailList).map Prod.fst := by
    rw [harrs₁₅ bufArr (by decide)]
    simpa [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, State.writeArr_arrs_ne] using hbuf₉_eq
  rcases copyArrCmd_exec bufArr coordXArr (by decide) (s := s₁₅) hw1
      (by rw [hbuf1_15]; simp; omega)
      (by rw [hbuf1_15]; intro v hv; rcases List.mem_cons.mp hv with rfl | hmem; exact hh1_w; exact hwordsX v hmem) with
    ⟨s₁₆, t_cx, hex₁₆, ht_cx, hcx₁₆, hregs₁₆, harrs₁₆⟩
  rw [hbuf1_15] at hcx₁₆ ht_cx
  have hbuf2_16 : s₁₆.arrs bufArr2 = (headCoord :: tailList).map Prod.snd := by
    rw [harrs₁₆ bufArr2 (by decide), hbuf₁₅_eq]
  rcases copyArrCmd_exec bufArr2 coordYArr (by decide) (s := s₁₆) hw1
      (by rw [hbuf2_16]; simp; omega)
      (by rw [hbuf2_16]; intro v hv; rcases List.mem_cons.mp hv with rfl | hmem; exact hh2_w; exact hwordsY v hmem) with
    ⟨s₁₇, t_cy, hex₁₇, ht_cy, hcy₁₇, hregs₁₇, harrs₁₇⟩
  rw [hbuf2_16] at hcy₁₇ ht_cy
  have hcx₁₇ : s₁₇.arrs coordXArr = (headCoord :: tailList).map Prod.fst := by
    rw [harrs₁₇ coordXArr (by decide), hcx₁₆]
  refine ⟨s₁₇, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈
      (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ (.seq hex₁₃ (.seq hex₁₄
        (.seq hex₁₅ (.seq hex₁₆ hex₁₇))))))))))))))),
    by simp only [List.length_cons, List.length_map] at ht_fx ht_fy ht_cx ht_cy; omega,
    hcx₁₇, hcy₁₇,
    fun r h6 h7 h8 h9 h11 h24 h25 h26 => by
      rw [hregs₁₇ r h7 h8 h9 h11, hregs₁₆ r h7 h8 h9 h11, hregs₁₅ r h6 h7 h8 h9]
      simp only [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, State.setReg_regs_ne _ _ h9,
        State.setReg_regs_ne _ _ h8, State.setReg_regs_ne _ _ h7,
        State.writeArr_regs, State.setArr_regs,
        hregs₉ r h6 h7 h8 h9]
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, h7, h8, h9, h24, h25, h26],
    fun a ha1 ha2 ha3 ha4 => by
      rw [harrs₁₇ a ha4, harrs₁₆ a ha3, harrs₁₅ a ha2]
      simp only [s₁₄, s₁₃, s₁₂, s₁₁, s₁₀, State.setReg_arrs,
        State.writeArr_arrs_ne _ _ _ ha2, State.setArr_arrs_ne _ _ ha2,
        harrs₉ a ha1]
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha1]⟩

/-- Build `(elemWallEdgeCanonicalPath p₁ p₂ q).map Prod.fst` in `coordXArr` and
`(elemWallEdgeCanonicalPath p₁ p₂ q).map Prod.snd` in `coordYArr` from `p₁ = (r_18, r_19)`,
`p₂ = (r_28, r_29)`, and `q = (r_20, r_21)`. -/
def buildElemWallEdgeCanonicalPathCmd : Cmd :=
  .seq buildElemWallCanonicalPathCmd
  (.seq (.assign 8 (.const 0))
  (.seq (.assign 10 (.const 1))
  (.seq findFirstCoordLoop
  (.seq (.ite (.op .lt (.reg 8) (.len coordXArr))
      (.seq (.assign 22 (.reg 18))
        (.assign 23 (.reg 19)))
      (.seq (.assign 22 (.reg 28))
        (.seq (.assign 23 (.reg 29))
          (.assign 8 (.const 0)))))
    prependCoordAndSliceCmd))))

theorem mem_elemWallCanonicalPath_bounds {h : ℕ} (hh : 1 ≤ h)
    {p q v : ℕ × ℕ}
    (hp1 : p.1 < 2 * h + 2) (hp2 : p.2 ≤ h)
    (hq1 : q.1 < 2 * h + 2) (hq2 : q.2 ≤ h)
    (hv : v ∈ elemWallCanonicalPath p q) :
    v.1 < 2 * h + 2 ∧ v.2 ≤ h := by
  unfold elemWallCanonicalPath at hv
  split_ifs at hv with hle
  · obtain ⟨h1, h2⟩ := mem_elemWallUpPath_bounds hh hq1 hp1 hv
    exact ⟨h1, by omega⟩
  · rw [List.mem_reverse] at hv
    obtain ⟨h1, h2⟩ := mem_elemWallUpPath_bounds hh hp1 hq1 hv
    exact ⟨h1, by omega⟩

theorem length_elemWallCanonicalPath_le {h : ℕ} (hh : 1 ≤ h)
    {p q : ℕ × ℕ}
    (hp1 : p.1 < 2 * h + 2) (hp2 : p.2 ≤ h)
    (hq1 : q.1 < 2 * h + 2) (hq2 : q.2 ≤ h) :
    (elemWallCanonicalPath p q).length ≤ elemWallNumVerts h + 2 := by
  have hcap_eq : elemWallNumVerts h + 2 = (h + 1) * (2 * h + 2) := by
    rw [elemWallNumVerts_eq]
    have : 2 ≤ (h + 1) * (2 * h + 2) := by nlinarith
    omega
  rw [hcap_eq]
  unfold elemWallCanonicalPath
  split_ifs with hle
  · calc (elemWallUpPath q.1 (q.2 - p.2) p.1 p.2).length
        ≤ (q.2 - p.2 + 1) * (2 * h + 2) := length_elemWallUpPath_le hh hq1 _ p.1 p.2 hp1
      _ ≤ (h + 1) * (2 * h + 2) := Nat.mul_le_mul_right _ (by omega)
  · rw [List.length_reverse]
    calc (elemWallUpPath p.1 (p.2 - q.2) q.1 q.2).length
        ≤ (p.2 - q.2 + 1) * (2 * h + 2) := length_elemWallUpPath_le hh hp1 _ q.1 q.2 hq1
      _ ≤ (h + 1) * (2 * h + 2) := Nat.mul_le_mul_right _ (by omega)

theorem buildElemWallEdgeCanonicalPathCmd_exec {w h : ℕ} (hh : 1 ≤ h)
    (p₁ p₂ q : ℕ × ℕ) {s : State}
    (hw2 : 2 < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (hp₁1 : p₁.1 < 2 * h + 2) (hp₁2 : p₁.2 ≤ h)
    (hp₂1 : p₂.1 < 2 * h + 2) (hp₂2 : p₂.2 ≤ h)
    (hq1 : q.1 < 2 * h + 2) (hq2 : q.2 ≤ h)
    (hr12 : s.regs 12 = elemWallNumVerts h)
    (hr18 : s.regs 18 = p₁.1)
    (hr19 : s.regs 19 = p₁.2)
    (hr20 : s.regs 20 = q.1)
    (hr21 : s.regs 21 = q.2)
    (hr28 : s.regs 28 = p₂.1)
    (hr29 : s.regs 29 = p₂.2) :
    let P := elemWallEdgeCanonicalPath p₁ p₂ q
    ∃ s' t,
      Exec w buildElemWallEdgeCanonicalPathCmd s s' t ∧
      t ≤ 290 * (elemWallCanonicalPath p₁ q).length + 50 * h + 2 * elemWallNumVerts h + 300 ∧
      s'.arrs coordXArr = P.map Prod.fst ∧
      s'.arrs coordYArr = P.map Prod.snd ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ bufArr → a ≠ bufArr2 → a ≠ coordXArr → a ≠ coordYArr →
        s'.arrs a = s.arrs a) := by
  intro P
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  let L := elemWallCanonicalPath p₁ q
  have hL_le : L.length ≤ elemWallNumVerts h + 2 :=
    length_elemWallCanonicalPath_le hh hp₁1 hp₁2 hq1 hq2
  have hL1_w : L.length + 1 < 2 ^ w := by omega
  have hL_w : L.length < 2 ^ w := by omega
  rcases buildElemWallCanonicalPathCmd_exec hh p₁ q (s := s)
      hw2 hVJW_w hp₁1 hp₁2 hq1 hq2 hr12 hr18 hr19 hr20 hr21 with
    ⟨s₁, t_can, hex₁, ht_can, hcx₁, hcy₁, hregs₁, harrs₁⟩
  let s₂ := s₁.setReg 8 0
  have hex₂ : Exec w (.assign 8 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₃ := s₂.setReg 10 1
  have hex₃ : Exec w (.assign 10 (.const 1)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h1_w])
  have hr28_3 : s₃.regs 28 = p₂.1 := by
    simp only [s₃, s₂, State.setReg_regs_ne _ _ (by decide : (28 : Reg) ≠ 10),
      State.setReg_regs_ne _ _ (by decide : (28 : Reg) ≠ 8)]
    rw [hregs₁ 28 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr28]
  have hr29_3 : s₃.regs 29 = p₂.2 := by
    simp only [s₃, s₂, State.setReg_regs_ne _ _ (by decide : (29 : Reg) ≠ 10),
      State.setReg_regs_ne _ _ (by decide : (29 : Reg) ≠ 8)]
    rw [hregs₁ 29 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr29]
  rcases findFirstCoordLoop_exec p₂ h1_w (by omega) (by omega) L 0 (s := s₃)
      (by simp [s₃, s₂, hcx₁, L, hL_w])
      (by simp [s₃, s₂, hcx₁, L])
      (by simp [s₃, s₂, hcx₁, hcy₁])
      (fun v hv => by have := (mem_elemWallCanonicalPath_bounds hh hp₁1 hp₁2 hq1 hq2 hv).1; omega)
      (fun v hv => by have := (mem_elemWallCanonicalPath_bounds hh hp₁1 hp₁2 hq1 hq2 hv).2; omega)
      (fun j hj => by
        simp only [s₃, s₂, State.setReg_arrs, hcx₁, hcy₁, Nat.zero_add]
        exact ⟨by rw [List.getElem?_eq_getElem (by simpa using hj), List.getElem_map],
          by rw [List.getElem?_eq_getElem (by simpa using hj), List.getElem_map]⟩)
      (by simp [s₃, s₂]) (by simp [s₃]) hr28_3 hr29_3 with
    ⟨s₄, t_find, hex₄, ht_find, hlen₄, hget₄, hregs₄, harrs₄⟩
  have hcx₄ : s₄.arrs coordXArr = L.map Prod.fst := by rw [harrs₄]; simpa [s₃, s₂] using hcx₁
  have hcy₄ : s₄.arrs coordYArr = L.map Prod.snd := by rw [harrs₄]; simpa [s₃, s₂] using hcy₁
  have hlen₄' : s₄.regs 8 + (suffixFrom p₂ L).length = L.length := by
    simpa [s₃, s₂, hcx₁] using hlen₄
  have hr8_w : s₄.regs 8 < 2 ^ w := by omega
  have hr18_4 : s₄.regs 18 = p₁.1 := by
    rw [hregs₄ 18 (by decide) (by decide) (by decide) (by decide)]
    simp only [s₃, s₂, State.setReg_regs_ne _ _ (by decide : (18 : Reg) ≠ 10),
      State.setReg_regs_ne _ _ (by decide : (18 : Reg) ≠ 8)]
    rw [hregs₁ 18 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr18]
  have hr19_4 : s₄.regs 19 = p₁.2 := by
    rw [hregs₄ 19 (by decide) (by decide) (by decide) (by decide)]
    simp only [s₃, s₂, State.setReg_regs_ne _ _ (by decide : (19 : Reg) ≠ 10),
      State.setReg_regs_ne _ _ (by decide : (19 : Reg) ≠ 8)]
    rw [hregs₁ 19 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr19]
  have hr28_4 : s₄.regs 28 = p₂.1 := by
    rw [hregs₄ 28 (by decide) (by decide) (by decide) (by decide), hr28_3]
  have hr29_4 : s₄.regs 29 = p₂.2 := by
    rw [hregs₄ 29 (by decide) (by decide) (by decide) (by decide), hr29_3]
  let headCoord : ℕ × ℕ := if p₂ ∈ L then p₁ else p₂
  let tailList : List (ℕ × ℕ) := if p₂ ∈ L then suffixFrom p₂ L else L
  let off : ℕ := if p₂ ∈ L then s₄.regs 8 else 0
  have hP_eq : P = headCoord :: tailList := by
    unfold P elemWallEdgeCanonicalPath
    dsimp [headCoord, tailList, L]
    split_ifs <;> rfl
  have hex_ite : ∃ s₅ t_ite,
      Exec w (.ite (.op .lt (.reg 8) (.len coordXArr))
        (.seq (.assign 22 (.reg 18)) (.assign 23 (.reg 19)))
        (.seq (.assign 22 (.reg 28)) (.seq (.assign 23 (.reg 29)) (.assign 8 (.const 0))))) s₄ s₅ t_ite ∧
      t_ite ≤ 12 ∧
      s₅.regs 8 = off ∧
      s₅.regs 22 = headCoord.1 ∧
      s₅.regs 23 = headCoord.2 ∧
      (∀ r : Reg, r ≠ 8 → r ≠ 22 → r ≠ 23 → s₅.regs r = s₄.regs r) ∧
      s₅.arrs = s₄.arrs := by
    by_cases hp₂ : p₂ ∈ L
    · have hsuf_pos : 0 < (suffixFrom p₂ L).length :=
        List.length_pos_iff.mpr (suffixFrom_ne_nil hp₂)
      have hr8_lt : s₄.regs 8 < L.length := by omega
      have hcond : (Expr.op .lt (.reg 8) (.len coordXArr)).eval w s₄ = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_w, hcx₄, hL_w, hr8_lt, h1_w]
      let s₅a := s₄.setReg 22 p₁.1
      have hex₅a : Exec w (.assign 22 (.reg 18)) s₄ s₅a 2 :=
        .assign (by simp [Expr.eval, checkWord, hr18_4, show p₁.1 < 2 ^ w by omega])
      let s₅b := s₅a.setReg 23 p₁.2
      have hex₅b : Exec w (.assign 23 (.reg 19)) s₅a s₅b 2 :=
        .assign (by simp [Expr.eval, checkWord, s₅a, hr19_4, show p₁.2 < 2 ^ w by omega])
      refine ⟨s₅b, _, .ite_true hcond (by omega) (.seq hex₅a hex₅b), by simp [Expr.cost],
        by simp [s₅b, s₅a, off, hp₂],
        by simp [s₅b, s₅a, headCoord, hp₂],
        by simp [s₅b, headCoord, hp₂],
        fun r _ h22 h23 => by simp [s₅b, s₅a, h22, h23], rfl⟩
    · have hsuf_nil : suffixFrom p₂ L = [] := suffixFrom_eq_nil_of_not_mem hp₂
      have hr8_eq : s₄.regs 8 = L.length := by simp [hsuf_nil] at hlen₄'; omega
      have hcond : (Expr.op .lt (.reg 8) (.len coordXArr)).eval w s₄ = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_eq, hcx₄, hL_w, h0_w]
      let s₅a := s₄.setReg 22 p₂.1
      have hex₅a : Exec w (.assign 22 (.reg 28)) s₄ s₅a 2 :=
        .assign (by simp [Expr.eval, checkWord, hr28_4, show p₂.1 < 2 ^ w by omega])
      let s₅b := s₅a.setReg 23 p₂.2
      have hex₅b : Exec w (.assign 23 (.reg 29)) s₅a s₅b 2 :=
        .assign (by simp [Expr.eval, checkWord, s₅a, hr29_4, show p₂.2 < 2 ^ w by omega])
      let s₅c := s₅b.setReg 8 0
      have hex₅c : Exec w (.assign 8 (.const 0)) s₅b s₅c 2 :=
        .assign (by simp [Expr.eval, checkWord, h0_w])
      refine ⟨s₅c, _, .ite_false hcond (.seq hex₅a (.seq hex₅b hex₅c)), by simp [Expr.cost],
        by simp [s₅c, off, hp₂],
        by simp [s₅c, s₅b, s₅a, headCoord, hp₂],
        by simp [s₅c, s₅b, headCoord, hp₂],
        fun r h8 h22 h23 => by simp [s₅c, s₅b, s₅a, h8, h22, h23], rfl⟩
  rcases hex_ite with ⟨s₅, t_ite, hex₅, ht_ite, hr8_5, hr22_5, hr23_5, hregs₅, harrs₅⟩
  have hcx₅ : s₅.arrs coordXArr = L.map Prod.fst := by rw [harrs₅, hcx₄]
  have hcy₅ : s₅.arrs coordYArr = L.map Prod.snd := by rw [harrs₅, hcy₄]
  have htail_sub : ∀ v ∈ tailList, v ∈ L := by
    intro v hv
    dsimp [tailList] at hv
    split_ifs at hv
    · exact mem_of_mem_suffixFrom hv
    · exact hv
  have htail_le : tailList.length ≤ L.length := by
    dsimp [tailList]
    split_ifs <;> omega
  rcases prependCoordAndSliceCmd_exec headCoord tailList off (s := s₅)
      h1_w
      (by dsimp [headCoord]; split_ifs <;> omega)
      (by dsimp [headCoord]; split_ifs <;> omega)
      (by rw [hcx₅, List.length_map]; exact hL1_w)
      (by rw [hcx₅, List.length_map]; dsimp [off, tailList]; split_ifs <;> omega)
      (by rw [hcx₅, hcy₅]; simp)
      (fun v hv => by
        have := (mem_elemWallCanonicalPath_bounds hh hp₁1 hp₁2 hq1 hq2 (htail_sub v hv)).1; omega)
      (fun v hv => by
        have := (mem_elemWallCanonicalPath_bounds hh hp₁1 hp₁2 hq1 hq2 (htail_sub v hv)).2; omega)
      (fun j hj => by
        rw [harrs₅]
        dsimp [off, tailList] at hj ⊢
        split_ifs at hj ⊢ with hp₂
        · rw [harrs₄]; exact hget₄ j hj
        · rw [hcx₄, hcy₄, Nat.zero_add]
          exact ⟨by rw [List.getElem?_eq_getElem (by simpa using hj), List.getElem_map],
            by rw [List.getElem?_eq_getElem (by simpa using hj), List.getElem_map]⟩)
      hr8_5 hr22_5 hr23_5 with
    ⟨s₆, t_prep, hex₆, ht_prep, hcx₆, hcy₆, hregs₆, harrs₆⟩
  refine ⟨s₆, t_can + (2 + (2 + (t_find + (t_ite + t_prep)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by dsimp [L] at ht_can ht_find ht_prep htail_le; omega,
    by rwa [hP_eq], by rwa [hP_eq],
    fun r h6 h7 h8 h9 h10 h11 h22 h23 h24 h25 h26 h27 => by
      rw [hregs₆ r h6 h7 h8 h9 h11 h24 h25 h26, hregs₅ r h8 h22 h23, hregs₄ r h6 h8 h10 h11]
      simp only [s₃, s₂, State.setReg_regs_ne _ _ h10, State.setReg_regs_ne _ _ h8]
      exact hregs₁ r h6 h7 h8 h9 h11 h22 h23 h24 h25 h26 h27,
    fun a ha1 ha2 ha3 ha4 => by
      rw [harrs₆ a ha1 ha2 ha3 ha4, harrs₅, harrs₄]
      simpa [s₃, s₂] using harrs₁ a ha1 ha2 ha3 ha4⟩

theorem WallOfHeight.elemPathForVert_of_termLocCode {h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) {v : Fin n} (hv : v ∈ W.vertexFinset) (q : ℕ × ℕ) :
    let loc := termLocCode W v
    W.elemPathForVert v q =
      if hbr : loc < elemWallNumVerts h then
        elemWallCanonicalPath (elemWallVertCoord h ⟨loc, hbr⟩) q
      else if hloc : loc < elemWallNumVerts h + (elemWallEdges h).length then
        let k : Fin (elemWallEdges h).length := ⟨loc - elemWallNumVerts h, by omega⟩
        let e := (elemWallEdges h)[k.1]'k.2
        elemWallEdgeCanonicalPath (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) q
      else
        [q] := by
  intro loc
  have hloc_def : loc = termLocCode W v := rfl
  unfold WallOfHeight.elemPathForVert
  unfold termLocCode at hloc_def
  cases hfind1 : (List.finRange (elemWallNumVerts h)).find? (fun u => decide (W.branchVert u = v)) with
  | some u =>
    dsimp only
    have hloc_eq : loc = u.1 := by simp [hloc_def, hfind1]
    have hbr : loc < elemWallNumVerts h := hloc_eq ▸ u.2
    rw [dif_pos hbr]
    have hu_eq : (⟨loc, hbr⟩ : Fin (elemWallNumVerts h)) = u := Fin.ext hloc_eq
    rw [hu_eq]
  | none =>
    cases hfind2 : (List.finRange (elemWallEdges h).length).find?
        (fun k => decide (v ∈ W.internalVerts k)) with
    | none =>
      rcases W.mem_vertexFinset_cases hv with ⟨u, hu⟩ | ⟨k, hvk⟩
      · have hnone := List.find?_eq_none.mp hfind1 u (List.mem_finRange u)
        simp [hu] at hnone
      · have hnone := List.find?_eq_none.mp hfind2 k (List.mem_finRange k)
        simp [hvk] at hnone
    | some k =>
      dsimp only
      have hloc_eq : loc = elemWallNumVerts h + k.1 := by simp [hloc_def, hfind1, hfind2]
      have hnot1 : ¬ (loc < elemWallNumVerts h) := by omega
      have hlt2 : loc < elemWallNumVerts h + (elemWallEdges h).length := by
        have := k.2; omega
      rw [dif_neg hnot1, dif_pos hlt2]
      have hsub : loc - elemWallNumVerts h = k.1 := by omega
      simp only [hsub]

/-- Build `(W.elemPathForVert v q).map Prod.fst` in `coordXArr` and
`(W.elemPathForVert v q).map Prod.snd` in `coordYArr` from `v.1 = r_17` and `q = (r_20, r_21)`. -/
def elemPathForVertCmd : Cmd :=
  .seq (.assign 15 (.read locArr (.reg 17)))
    (.ite (.op .lt (.reg 15) (.reg 12))
      (.seq (.assign 16 (.op .add (.reg 15) (.const 1)))
        (.seq (.assign 18 (.op .mod (.reg 16) (.reg 14)))
          (.seq (.assign 19 (.op .div (.reg 16) (.reg 14)))
            buildElemWallCanonicalPathCmd)))
      (.seq (.assign 15 (.op .sub (.reg 15) (.reg 12)))
        (.seq (.assign 16 (.op .add (.read edgeU1Arr (.reg 15)) (.const 1)))
          (.seq (.assign 18 (.op .mod (.reg 16) (.reg 14)))
            (.seq (.assign 19 (.op .div (.reg 16) (.reg 14)))
              (.seq (.assign 16 (.op .add (.read edgeU2Arr (.reg 15)) (.const 1)))
                (.seq (.assign 28 (.op .mod (.reg 16) (.reg 14)))
                  (.seq (.assign 29 (.op .div (.reg 16) (.reg 14)))
                    buildElemWallEdgeCanonicalPathCmd))))))))

theorem elemPathForVertCmd_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (hh : 1 ≤ h) (hW : W.IsValid)
    (v : Fin n) (hv : v ∈ W.vertexFinset)
    (q : ℕ × ℕ) (hq : q ∈ GM13.elementaryWallVerts h)
    {s : State}
    (hw2 : 2 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (hs : WallStateHolds W s)
    (hr17 : s.regs 17 = v.1)
    (hr20 : s.regs 20 = q.1)
    (hr21 : s.regs 21 = q.2) :
    let P := W.elemPathForVert v q
    ∃ s' t,
      Exec w elemPathForVertCmd s s' t ∧
      t ≤ 350 * elemWallNumVerts h + 50 * h + 1000 ∧
      s'.arrs coordXArr = P.map Prod.fst ∧
      s'.arrs coordYArr = P.map Prod.snd ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 15 → r ≠ 16 → r ≠ 18 → r ≠ 19 →
        r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
        r ≠ 28 → r ≠ 29 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ bufArr → a ≠ bufArr2 → a ≠ coordXArr → a ≠ coordYArr →
        s'.arrs a = s.arrs a) := by
  intro P
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  obtain ⟨hq1, hq2, _, _, _, _⟩ := elemWallVerts_bounds hq
  have hv_lt : v.1 < n := v.2
  have hv_w : v.1 < 2 ^ w := by omega
  let loc := termLocCode W v
  have hloc_lt : loc < elemWallNumVerts h + (elemWallEdges h).length :=
    termLocCode_lt_of_mem_vertexFinset hW hv
  have hloc_val_w : loc < 2 ^ w := by omega
  have hVJ_w : elemWallNumVerts h < 2 ^ w := by omega
  have hW_w : 2 * h + 2 < 2 ^ w := by omega
  have hget_loc : (s.arrs locArr)[v.1]'(by rw [hs.hloc_len]; exact hv_lt) = loc :=
    getElem_of_getElem? (hs.hloc_val v hv) (by rw [hs.hloc_len]; exact hv_lt)
  let s₁ := s.setReg 15 loc
  have hex₁ : Exec w (.assign 15 (.read locArr (.reg 17))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hr17, hv_w, hs.hloc_len, hv_lt, hget_loc, hloc_val_w])
  have hP_char := W.elemPathForVert_of_termLocCode hv q
  change P = _ at hP_char
  by_cases hbr : loc < elemWallNumVerts h
  · have hcond : (Expr.op .lt (.reg 15) (.reg 12)).eval w s₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hs.hr12, hloc_val_w, hVJ_w, hbr, h1_w]
    let u : Fin (elemWallNumVerts h) := ⟨loc, hbr⟩
    let p := elemWallVertCoord h u
    have hp_eq : p = ((loc + 1) % (2 * h + 2), (loc + 1) / (2 * h + 2)) :=
      elemWallVertCoord_eq h u
    have hp1_eq : (loc + 1) % (2 * h + 2) = p.1 := (congrArg Prod.fst hp_eq).symm
    have hp2_eq : (loc + 1) / (2 * h + 2) = p.2 := (congrArg Prod.snd hp_eq).symm
    obtain ⟨hp1, hp2, _, _, _, _⟩ := elemWallVerts_bounds (elemWallVertCoord_mem_elementaryWallVerts h u)
    have hloc1_w : loc + 1 < 2 ^ w := by omega
    have hp1_w : p.1 < 2 ^ w := by dsimp [p]; omega
    have hp2_w : p.2 < 2 ^ w := by dsimp [p]; omega
    let s₂ := s₁.setReg 16 (loc + 1)
    have hex₂ : Exec w (.assign 16 (.op .add (.reg 15) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hloc_val_w, h1_w, hloc1_w])
    let s₃ := s₂.setReg 18 p.1
    have hex₃ : Exec w (.assign 18 (.op .mod (.reg 16) (.reg 14))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hs.hr14,
        hloc1_w, hW_w, hp1_eq, hp1_w])
    let s₄ := s₃.setReg 19 p.2
    have hex₄ : Exec w (.assign 19 (.op .div (.reg 16) (.reg 14))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hs.hr14,
        hloc1_w, hW_w, hp2_eq, hp2_w])
    rcases buildElemWallCanonicalPathCmd_exec hh p q (s := s₄)
        hw2 hVJW_w hp1 hp2 hq1 hq2
        (by simp [s₄, s₃, s₂, s₁, hs.hr12])
        (by simp [s₄, s₃]) (by simp [s₄])
        (by simp [s₄, s₃, s₂, s₁, hr20])
        (by simp [s₄, s₃, s₂, s₁, hr21]) with
      ⟨s', t_can, hex_can, ht_can, hcx', hcy', hregs', harrs'⟩
    have hP_eq : P = elemWallCanonicalPath p q := by
      dsimp [loc] at hbr
      simp [hP_char, hbr, p, u, loc]
    have hlen_le : (elemWallCanonicalPath p q).length ≤ elemWallNumVerts h + 2 :=
      length_elemWallCanonicalPath_le hh hp1 hp2 hq1 hq2
    refine ⟨s', _,
      .seq hex₁ (.ite_true hcond (by omega) (.seq hex₂ (.seq hex₃ (.seq hex₄ hex_can)))),
      by simp [Expr.cost]; omega,
      by rwa [hP_eq], by rwa [hP_eq],
      fun r h6 h7 h8 h9 _ h11 h15 h16 h18 h19 h22 h23 h24 h25 h26 h27 _ _ => by
        rw [hregs' r h6 h7 h8 h9 h11 h22 h23 h24 h25 h26 h27]
        simp [s₄, s₃, s₂, s₁, h15, h16, h18, h19],
      harrs'⟩
  · have hcond : (Expr.op .lt (.reg 15) (.reg 12)).eval w s₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hs.hr12, hloc_val_w, hVJ_w, hbr, h0_w]
    let k : Fin (elemWallEdges h).length := ⟨loc - elemWallNumVerts h, by omega⟩
    let e := (elemWallEdges h)[k.1]'k.2
    let p₁ := elemWallVertCoord h e.1
    let p₂ := elemWallVertCoord h e.2
    have hp₁_eq : p₁ = ((e.1.1 + 1) % (2 * h + 2), (e.1.1 + 1) / (2 * h + 2)) :=
      elemWallVertCoord_eq h e.1
    have hp₂_eq : p₂ = ((e.2.1 + 1) % (2 * h + 2), (e.2.1 + 1) / (2 * h + 2)) :=
      elemWallVertCoord_eq h e.2
    have hp₁1_eq : (e.1.1 + 1) % (2 * h + 2) = p₁.1 := (congrArg Prod.fst hp₁_eq).symm
    have hp₁2_eq : (e.1.1 + 1) / (2 * h + 2) = p₁.2 := (congrArg Prod.snd hp₁_eq).symm
    have hp₂1_eq : (e.2.1 + 1) % (2 * h + 2) = p₂.1 := (congrArg Prod.fst hp₂_eq).symm
    have hp₂2_eq : (e.2.1 + 1) / (2 * h + 2) = p₂.2 := (congrArg Prod.snd hp₂_eq).symm
    obtain ⟨hp₁1, hp₁2, _, _, _, _⟩ := elemWallVerts_bounds (elemWallVertCoord_mem_elementaryWallVerts h e.1)
    obtain ⟨hp₂1, hp₂2, _, _, _, _⟩ := elemWallVerts_bounds (elemWallVertCoord_mem_elementaryWallVerts h e.2)
    have hk_w : k.1 < 2 ^ w := by dsimp [k]; omega
    have hu1_w : e.1.1 < 2 ^ w := by have := e.1.2; omega
    have hu1_1_w : e.1.1 + 1 < 2 ^ w := by have := e.1.2; omega
    have hu2_w : e.2.1 < 2 ^ w := by have := e.2.2; omega
    have hu2_1_w : e.2.1 + 1 < 2 ^ w := by have := e.2.2; omega
    have hp₁1_w : p₁.1 < 2 ^ w := by dsimp [p₁]; omega
    have hp₁2_w : p₁.2 < 2 ^ w := by dsimp [p₁]; omega
    have hp₂1_w : p₂.1 < 2 ^ w := by dsimp [p₂]; omega
    have hp₂2_w : p₂.2 < 2 ^ w := by dsimp [p₂]; omega
    have hget_u1 : (s.arrs edgeU1Arr)[k.1]'(by rw [hs.hu1_len]; exact k.2) = e.1.1 :=
      getElem_of_getElem? (hs.hu_val k).1 (by rw [hs.hu1_len]; exact k.2)
    have hget_u2 : (s.arrs edgeU2Arr)[k.1]'(by rw [hs.hu2_len]; exact k.2) = e.2.1 :=
      getElem_of_getElem? (hs.hu_val k).2 (by rw [hs.hu2_len]; exact k.2)
    let s₂ := s₁.setReg 15 k.1
    have hex₂ : Exec w (.assign 15 (.op .sub (.reg 15) (.reg 12))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hs.hr12,
        hloc_val_w, hVJ_w, hk_w, k])
    let s₃ := s₂.setReg 16 (e.1.1 + 1)
    have hex₃ : Exec w (.assign 16 (.op .add (.read edgeU1Arr (.reg 15)) (.const 1))) s₂ s₃ 5 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁,
        hk_w, hs.hu1_len, k.2, hget_u1, hu1_w, h1_w, hu1_1_w])
    let s₄ := s₃.setReg 18 p₁.1
    have hex₄ : Exec w (.assign 18 (.op .mod (.reg 16) (.reg 14))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hs.hr14,
        hu1_1_w, hW_w, hp₁1_eq, hp₁1_w])
    let s₅ := s₄.setReg 19 p₁.2
    have hex₅ : Exec w (.assign 19 (.op .div (.reg 16) (.reg 14))) s₄ s₅ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₄, s₃, s₂, s₁, hs.hr14,
        hu1_1_w, hW_w, hp₁2_eq, hp₁2_w])
    let s₆ := s₅.setReg 16 (e.2.1 + 1)
    have hex₆ : Exec w (.assign 16 (.op .add (.read edgeU2Arr (.reg 15)) (.const 1))) s₅ s₆ 5 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, s₄, s₃, s₂, s₁,
        hk_w, hs.hu2_len, k.2, hget_u2, hu2_w, h1_w, hu2_1_w])
    let s₇ := s₆.setReg 28 p₂.1
    have hex₇ : Exec w (.assign 28 (.op .mod (.reg 16) (.reg 14))) s₆ s₇ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₆, s₅, s₄, s₃, s₂, s₁, hs.hr14,
        hu2_1_w, hW_w, hp₂1_eq, hp₂1_w])
    let s₈ := s₇.setReg 29 p₂.2
    have hex₈ : Exec w (.assign 29 (.op .div (.reg 16) (.reg 14))) s₇ s₈ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hs.hr14,
        hu2_1_w, hW_w, hp₂2_eq, hp₂2_w])
    rcases buildElemWallEdgeCanonicalPathCmd_exec hh p₁ p₂ q (s := s₈)
        hw2 hVJW_w hp₁1 hp₁2 hp₂1 hp₂2 hq1 hq2
        (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hs.hr12])
        (by simp [s₈, s₇, s₆, s₅, s₄])
        (by simp [s₈, s₇, s₆, s₅])
        (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr20])
        (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr21])
        (by simp [s₈, s₇])
        (by simp [s₈]) with
      ⟨s', t_ed, hex_ed, ht_ed, hcx', hcy', hregs', harrs'⟩
    have hP_eq : P = elemWallEdgeCanonicalPath p₁ p₂ q := by
      dsimp [loc] at hbr hloc_lt
      simp [hP_char, hbr, hloc_lt, p₁, p₂, e, k, loc]
    have hlen_le : (elemWallCanonicalPath p₁ q).length ≤ elemWallNumVerts h + 2 :=
      length_elemWallCanonicalPath_le hh hp₁1 hp₁2 hq1 hq2
    refine ⟨s', _,
      .seq hex₁ (.ite_false hcond (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
        (.seq hex₆ (.seq hex₇ (.seq hex₈ hex_ed)))))))),
      by simp [Expr.cost]; omega,
      by rwa [hP_eq], by rwa [hP_eq],
      fun r h6 h7 h8 h9 h10 h11 h15 h16 h18 h19 h22 h23 h24 h25 h26 h27 h28 h29 => by
        rw [hregs' r h6 h7 h8 h9 h10 h11 h22 h23 h24 h25 h26 h27]
        simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, h15, h16, h18, h19, h28, h29],
      harrs'⟩

/-! ### Section 3: `liftElemPathCmd`, `pathToSubwallCmd`, and `extendOneRayCmd` -/

theorem mem_elementaryWallVerts_of_isChain {h : ℕ} :
    ∀ {rest : List (ℕ × ℕ)} {a p : ℕ × ℕ},
      a ∈ GM13.elementaryWallVerts h →
      List.IsChain (GM13.elementaryWallAdj h) (a :: rest) →
      p ∈ a :: rest →
      p ∈ GM13.elementaryWallVerts h
  | [], a, p, ha, _, hp => by
    rcases List.mem_singleton.mp hp with rfl
    exact ha
  | b :: bs, a, p, ha, hc, hp => by
    rcases List.mem_cons.mp hp with rfl | hp_rest
    · exact ha
    · have hab := (List.isChain_cons_cons.mp hc).1
      exact mem_elementaryWallVerts_of_isChain hab.2.1 (List.isChain_cons_cons.mp hc).2 hp_rest

theorem length_le_elemWallNumVerts_of_isChain_nodup {h : ℕ} {a : ℕ × ℕ} {rest : List (ℕ × ℕ)}
    (ha : a ∈ GM13.elementaryWallVerts h)
    (hc : List.IsChain (GM13.elementaryWallAdj h) (a :: rest))
    (hnd : (a :: rest).Nodup) :
    (a :: rest).length ≤ elemWallNumVerts h := by
  have hmem : ∀ p ∈ a :: rest, p ∈ GM13.elementaryWallVerts h :=
    fun _ hp => mem_elementaryWallVerts_of_isChain ha hc hp
  have hinj : Function.Injective (fun i : Fin (a :: rest).length =>
      elemWallCoordIdx h ((a :: rest)[i.1]'i.2) (hmem _ (List.getElem_mem i.2))) := by
    intro i j hij
    have hcoord := congrArg (elemWallVertCoord h) hij
    rw [elemWallVertCoord_elemWallCoordIdx, elemWallVertCoord_elemWallCoordIdx] at hcoord
    exact (List.nodup_iff_injective_getElem.mp hnd) hcoord
  have hcard := Fintype.card_le_of_injective _ hinj
  simpa using hcard

/-- Lift a non-empty coordinate chain `P` stored in `(coordXArr, coordYArr)` into `liftArr`
(`s'.arrs liftArr = (W.liftElemPath P).map Fin.val`). -/
def liftElemPathCmd : Cmd :=
  .seq (.alloc bufArr2 (.reg 0))
  (.seq (.assign 18 (.read coordXArr (.const 0)))
  (.seq (.assign 19 (.read coordYArr (.const 0)))
  (.seq (.assign 7 (.const 0))
  (.seq (pushCoordBranchVertCmd bufArr2)
  (.seq (.assign 10 (.const 1))
  (.seq (.assign 11 (.op .sub (.len coordXArr) (.const 1)))
  (.seq (appendLiftElemStepsLoop bufArr2)
  (.seq (.assign 8 (.const 0))
  (.seq (.assign 9 (.reg 7))
    (copySliceToArrCmd bufArr2 liftArr))))))))))

theorem liftElemPathCmd_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (hW : W.IsValid)
    (a : ℕ × ℕ) (rest : List (ℕ × ℕ))
    (ha : a ∈ GM13.elementaryWallVerts h)
    (hc : List.IsChain (GM13.elementaryWallAdj h) (a :: rest))
    (hnd : (a :: rest).Nodup)
    {s : State}
    (hw2 : 2 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w)
    (hs : WallStateHolds W s)
    (hcx : s.arrs coordXArr = (a :: rest).map Prod.fst)
    (hcy : s.arrs coordYArr = (a :: rest).map Prod.snd) :
    let L := W.liftElemPath (a :: rest)
    ∃ s' t,
      Exec w liftElemPathCmd s s' t ∧
      t ≤ 90 * rest.length + 45 * n + 85 ∧
      WallStateHolds W s' ∧
      s'.arrs liftArr = L.map Fin.val ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → s'.regs r = s.regs r) ∧
      (∀ arr : Arr, arr ≠ bufArr2 → arr ≠ liftArr → s'.arrs arr = s.arrs arr) := by
  intro L
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hndP : (a :: rest).length ≤ elemWallNumVerts h :=
    length_le_elemWallNumVerts_of_isChain_nodup ha hc hnd
  have hP_w : (a :: rest).length < 2 ^ w := by omega
  have hrest_w : rest.length < 2 ^ w := by simp at hP_w; omega
  have hndL : L.Nodup := W.nodup_liftElemPath hW hc ha hnd
  have hL_le_n : L.length ≤ n := length_le_of_nodup_fin hndL
  have hL_eq : L = W.coordBranchVertList a ++ liftElemSteps W a rest :=
    liftElemPath_cons_eq_liftElemSteps W a rest
  obtain ⟨ha1, ha2, _, _, _, _⟩ := elemWallVerts_bounds ha
  have ha1_w : a.1 < 2 ^ w := by omega
  have ha2_w : a.2 < 2 ^ w := by omega
  let s₁ := s.setArr bufArr2 (List.replicate n 0)
  have hex₁ : Exec w (.alloc bufArr2 (.reg 0)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hs.hr0, hn_w])
  have hgetX0 : (s₁.arrs coordXArr)[0]'(by simp [s₁, hcx]) = a.1 := by
    simp [s₁, hcx]
  have hgetY0 : (s₁.arrs coordYArr)[0]'(by simp [s₁, hcy]) = a.2 := by
    simp [s₁, hcy]
  let s₂ := s₁.setReg 18 a.1
  have hex₂ : Exec w (.assign 18 (.read coordXArr (.const 0))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, s₁, hcx, ha1_w])
  let s₃ := s₂.setReg 19 a.2
  have hex₃ : Exec w (.assign 19 (.read coordYArr (.const 0))) s₂ s₃ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, s₂, s₁, hcy, ha2_w])
  let s₄ := s₃.setReg 7 0
  have hex₄ : Exec w (.assign 7 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hs₄ : WallStateHolds W s₄ :=
    hs.of_preserve (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁])
      (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁])
      (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁])
      (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁])
      (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁])
  have hbuf₄ : IsArrBufPrefix (s₄.arrs bufArr2) [] (s₄.regs 7) :=
    ⟨by simp [s₄], by simp [s₄, s₃, s₂, s₁], fun _ hi => by simp at hi⟩
  have hbr_len : (W.coordBranchVertList a).length = 1 := by
    rw [W.coordBranchVertList_of_mem ha]; rfl
  have h1_le_n : 1 ≤ n := by
    have : 1 ≤ L.length := by rw [hL_eq, List.length_append, hbr_len]; omega
    omega
  rcases pushCoordBranchVertCmd_exec W bufArr2 (by decide) ha [] (s := s₄)
      hw2 hn_w hVJW_w henc_w hs₄ hbuf₄
      (by simp [s₄, s₃, s₂, s₁, h1_le_n])
      (by simp [s₄, s₃, s₂, s₁, hn_w])
      (by simp [s₄, s₃, s₂]) (by simp [s₄, s₃]) with
    ⟨s₅, t_br, hex₅, ht_br, hbuf₅, hlen5, hregs₅, harrs₅⟩
  simp only [List.nil_append] at hbuf₅
  have hlen5' : (s₅.arrs bufArr2).length = n := by simpa [s₄, s₃, s₂, s₁] using hlen5
  let s₆ := s₅.setReg 10 1
  have hex₆ : Exec w (.assign 10 (.const 1)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, h1_w])
  have hcx₆ : s₆.arrs coordXArr = (a :: rest).map Prod.fst := by
    simp [s₆, harrs₅ coordXArr (by decide), s₄, s₃, s₂, s₁, hcx]
  have hcy₆ : s₆.arrs coordYArr = (a :: rest).map Prod.snd := by
    simp [s₆, harrs₅ coordYArr (by decide), s₄, s₃, s₂, s₁, hcy]
  let s₇ := s₆.setReg 11 rest.length
  have hex₇ : Exec w (.assign 11 (.op .sub (.len coordXArr) (.const 1))) s₆ s₇ 4 :=
    .assign (by
      have hlen_cx : (s₆.arrs coordXArr).length = rest.length + 1 := by simp [hcx₆]
      have hsub : (s₆.arrs coordXArr).length - 1 = rest.length := by omega
      rw [← hsub]
      exact eval_op_sub (eval_len rfl (by rw [hlen_cx]; simpa using hP_w))
        (by simp [Expr.eval, checkWord, h1_w]))
  have hs₇ : WallStateHolds W s₇ := by
    refine hs₄.of_arr_ne ?_ ?_ ?_ ?_ ?_ bufArr2
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) ?_
    · simp [s₇, s₆, hregs₅ 0 (by decide) (by decide) (by decide)]
    · simp [s₇, s₆, hregs₅ 3 (by decide) (by decide) (by decide)]
    · simp [s₇, s₆, hregs₅ 12 (by decide) (by decide) (by decide)]
    · simp [s₇, s₆, hregs₅ 13 (by decide) (by decide) (by decide)]
    · simp [s₇, s₆, hregs₅ 14 (by decide) (by decide) (by decide)]
    · intro arr harr; simp [s₇, s₆, harrs₅ arr harr]
  rcases appendLiftElemStepsLoop_exec W bufArr2
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw2 hn_w hVJW_w hloc_w henc_w rest a 1 ((W.coordBranchVertList a).map Fin.val) (s := s₇)
      ha hc hs₇ (by simp at hP_w; omega)
      (by simp [s₇, hcx₆]; omega)
      (by simp [s₇, hcy₆]; omega)
      (fun j hj => by
        simp only [s₇, State.setReg_arrs, hcx₆, hcy₆]
        have hidx : 1 + j = j + 1 := Nat.add_comm 1 j
        rw [hidx]
        exact ⟨by rw [List.getElem?_eq_getElem (by simp; omega)]; simp,
          by rw [List.getElem?_eq_getElem (by simp; omega)]; simp⟩)
      (by simpa [s₇, s₆] using hbuf₅)
      (by
        simp only [s₇, s₆, State.setReg_arrs, hlen5', List.length_map]
        rw [← List.length_append, ← hL_eq]
        exact hL_le_n)
      (by simp [s₇, s₆, hlen5', hn_w])
      (by simp [s₇, s₆]) (by simp [s₇])
      (by simp [s₇, s₆, hregs₅ 18 (by decide) (by decide) (by decide), s₄, s₃, s₂])
      (by simp [s₇, s₆, hregs₅ 19 (by decide) (by decide) (by decide), s₄, s₃]) with
    ⟨s₈, t_lift, hex₈, ht_lift, hbuf₈, hlen8, _, _, hregs₈, harrs₈⟩
  have hbuf₈' : IsArrBufPrefix (s₈.arrs bufArr2) (L.map Fin.val) (s₈.regs 7) := by
    rwa [hL_eq, List.map_append]
  have hlen8' : (s₈.arrs bufArr2).length = n := by simpa [s₇, s₆, hlen5'] using hlen8
  have hr7_8 : s₈.regs 7 = L.length := by simpa using hbuf₈'.1
  let s₉ := s₈.setReg 8 0
  have hex₉ : Exec w (.assign 8 (.const 0)) s₈ s₉ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₁₀ := s₉.setReg 9 L.length
  have hex₁₀ : Exec w (.assign 9 (.reg 7)) s₉ s₁₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₉, hr7_8, show L.length < 2 ^ w by omega])
  rcases copySliceToArrCmd_exec bufArr2 liftArr (by decide) (L.map Fin.val) 0 (s := s₁₀)
      h1_w (by simp [s₁₀, s₉, hlen8', hn_w])
      (by simp [s₁₀, s₉, hlen8', hL_le_n])
      (fun j hj => by
        simp only [s₁₀, s₉, State.setReg_arrs, Nat.zero_add]
        exact hbuf₈'.2.2 j hj)
      (fun v hv => by rcases List.mem_map.mp hv with ⟨u, _, rfl⟩; exact Nat.lt_trans u.2 hn_w)
      (by simp [s₁₀, s₉]) (by simp [s₁₀]) with
    ⟨s₁₁, t_cp, hex₁₁, ht_cp, hlift₁₁, _, hregs₁₁, harrs₁₁⟩
  have hkeep_reg : ∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
      r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → s₁₁.regs r = s.regs r := by
    intro r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21
    rw [hregs₁₁ r h7 h8 h9 h11]
    simp only [s₁₀, s₉, State.setReg_regs_ne _ _ h9, State.setReg_regs_ne _ _ h8,
      hregs₈ r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21]
    simp only [s₇, s₆, State.setReg_regs_ne _ _ h11, State.setReg_regs_ne _ _ h10,
      hregs₅ r h6 h7 h8]
    simp [s₄, s₃, s₂, s₁, h7, h18, h19]
  have hkeep_arr : ∀ arr : Arr, arr ≠ bufArr2 → arr ≠ liftArr → s₁₁.arrs arr = s.arrs arr := by
    intro arr ha1 ha2
    rw [harrs₁₁ arr ha2]
    simp only [s₁₀, s₉, State.setReg_arrs, harrs₈ arr ha1, s₇, s₆, harrs₅ arr ha1]
    simp [s₄, s₃, s₂, s₁, ha1]
  have hs₁₁ : WallStateHolds W s₁₁ :=
    hs.of_preserve
      (hkeep_reg 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr wallEncArr (by decide) (by decide))
      (hkeep_arr locArr (by decide) (by decide))
      (hkeep_arr wallMemArr (by decide) (by decide))
      (hkeep_arr edgeOffArr (by decide) (by decide))
      (hkeep_arr edgeLenArr (by decide) (by decide))
      (hkeep_arr edgeU1Arr (by decide) (by decide))
      (hkeep_arr edgeU2Arr (by decide) (by decide))
      (hkeep_arr horizEdgeIdxArr (by decide) (by decide))
      (hkeep_arr vertEdgeIdxArr (by decide) (by decide))
  have hsteps_le : (liftElemSteps W a rest).length ≤ n := by
    have : (W.coordBranchVertList a).length + (liftElemSteps W a rest).length ≤ n := by
      rw [← List.length_append, ← hL_eq]; exact hL_le_n
    omega
  refine ⟨s₁₁,
    (1 + n) + (3 + (3 + (2 + (t_br + (2 + (4 + (t_lift + (2 + (2 + t_cp))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ hex₁₁))))))))),
    by simp only [List.length_map] at ht_cp; omega,
    hs₁₁, hlift₁₁, hkeep_reg, hkeep_arr⟩

/-- Compute `(W.pathToSubwall S v q).map Fin.val` in `tmpPathArr2` from `v.1 = r_17`,
`q = (r_30, r_31)`, and membership indicator of `S` in `newWallMemArr`. -/
def pathToSubwallCmd : Cmd :=
  .seq (.assign 20 (.reg 30))
  (.seq (.assign 21 (.reg 31))
  (.seq elemPathForVertCmd
  (.seq liftElemPathCmd
  (.seq (suffixFromArrCmd liftArr tmpPathArr1 17)
    (prefixUntilArrCmd tmpPathArr1 newWallMemArr tmpPathArr2)))))

theorem pathToSubwallCmd_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (hh : 1 ≤ h) (hW : W.IsValid)
    (S : Finset (Fin n))
    (v : Fin n) (hv : v ∈ W.vertexFinset)
    (q : ℕ × ℕ) (hq : q ∈ GM13.elementaryWallVerts h)
    {s : State}
    (hw2 : 2 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w)
    (hs : WallStateHolds W s)
    (hmem_len : (s.arrs newWallMemArr).length = n)
    (hmem_val : ∀ u : Fin n, (s.arrs newWallMemArr)[u.1]? = some (if u ∈ S then 1 else 0))
    (hr17 : s.regs 17 = v.1)
    (hr30 : s.regs 30 = q.1)
    (hr31 : s.regs 31 = q.2) :
    let Q := W.pathToSubwall S v q
    ∃ s' t,
      Exec w pathToSubwallCmd s s' t ∧
      t ≤ 440 * elemWallNumVerts h + 50 * h + 140 * n + 1150 ∧
      WallStateHolds W s' ∧
      s'.arrs tmpPathArr2 = Q.map Fin.val ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 15 → r ≠ 16 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 →
        r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
        r ≠ 28 → r ≠ 29 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ bufArr → a ≠ bufArr2 → a ≠ coordXArr → a ≠ coordYArr →
        a ≠ liftArr → a ≠ tmpPathArr1 → a ≠ tmpPathArr2 → s'.arrs a = s.arrs a) := by
  intro Q
  have h1_w : 1 < 2 ^ w := by omega
  obtain ⟨hq1, hq2, _, _, _, _⟩ := elemWallVerts_bounds hq
  have hq1_w : q.1 < 2 ^ w := by omega
  have hq2_w : q.2 < 2 ^ w := by omega
  let s₁ := s.setReg 20 q.1
  have hex₁ : Exec w (.assign 20 (.reg 30)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr30, hq1_w])
  let s₂ := s₁.setReg 21 q.2
  have hex₂ : Exec w (.assign 21 (.reg 31)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₁, hr31, hq2_w])
  have hs₂ : WallStateHolds W s₂ :=
    hs.of_preserve (by simp [s₂, s₁]) (by simp [s₂, s₁]) (by simp [s₂, s₁])
      (by simp [s₂, s₁]) (by simp [s₂, s₁])
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rcases elemPathForVertCmd_exec W hh hW v hv q hq (s := s₂)
      hw2 hn_w hVJW_w hloc_w hs₂ (by simp [s₂, s₁, hr17]) (by simp [s₂, s₁]) (by simp [s₂]) with
    ⟨s₃, t_ep, hex₃, ht_ep, hcx₃, hcy₃, hregs₃, harrs₃⟩
  have hs₃ : WallStateHolds W s₃ :=
    hs₂.of_preserve
      (hregs₃ 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hregs₃ 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hregs₃ 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hregs₃ 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hregs₃ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harrs₃ wallEncArr (by decide) (by decide) (by decide) (by decide))
      (harrs₃ locArr (by decide) (by decide) (by decide) (by decide))
      (harrs₃ wallMemArr (by decide) (by decide) (by decide) (by decide))
      (harrs₃ edgeOffArr (by decide) (by decide) (by decide) (by decide))
      (harrs₃ edgeLenArr (by decide) (by decide) (by decide) (by decide))
      (harrs₃ edgeU1Arr (by decide) (by decide) (by decide) (by decide))
      (harrs₃ edgeU2Arr (by decide) (by decide) (by decide) (by decide))
      (harrs₃ horizEdgeIdxArr (by decide) (by decide) (by decide) (by decide))
      (harrs₃ vertEdgeIdxArr (by decide) (by decide) (by decide) (by decide))
  obtain ⟨hneP, hheadP, _, hcP, hndP, _⟩ := W.elemPathForVert_props hh hv hq
  rcases List.exists_cons_of_ne_nil hneP with ⟨a, rest, hP_cons⟩
  have ha : a ∈ GM13.elementaryWallVerts h := by
    have : a = (W.elemPathForVert v q).head hneP := by simp [hP_cons]
    exact this ▸ hheadP
  have hc_cons : List.IsChain (GM13.elementaryWallAdj h) (a :: rest) := hP_cons ▸ hcP
  have hnd_cons : (a :: rest).Nodup := hP_cons ▸ hndP
  have hrest_le : rest.length ≤ elemWallNumVerts h := by
    have := length_le_elemWallNumVerts_of_isChain_nodup ha hc_cons hnd_cons
    simp at this; omega
  rcases liftElemPathCmd_exec W hW a rest ha hc_cons hnd_cons (s := s₃)
      hw2 hn_w hVJW_w hloc_w henc_w hs₃ (by rwa [← hP_cons]) (by rwa [← hP_cons]) with
    ⟨s₄, t_lift, hex₄, ht_lift, hs₄, hlift₄, hregs₄, harrs₄⟩
  rw [← hP_cons] at hlift₄
  let L := W.liftElemPath (W.elemPathForVert v q)
  have hndL : L.Nodup := by
    dsimp [L]; rw [hP_cons]; exact W.nodup_liftElemPath hW hc_cons ha hnd_cons
  have hL_le_n : L.length ≤ n := length_le_of_nodup_fin hndL
  have hL_w : L.length < 2 ^ w := by omega
  have hr17_4 : s₄.regs 17 = v.1 := by
    rw [hregs₄ 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hregs₃ 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s₂, s₁, hr17]
  rcases suffixFromArrCmd_exec liftArr tmpPathArr1 17 (by decide)
      (by decide) (by decide) (by decide) v L (s := s₄)
      h1_w hn_w hlift₄ hL_w hr17_4 with
    ⟨s₅, t_suf, hex₅, ht_suf, hsuf₅, hregs₅, harrs₅⟩
  let S_list := suffixFrom v L
  have hndS : S_list.Nodup := nodup_suffixFrom hndL
  have hS_le_n : S_list.length ≤ n := length_le_of_nodup_fin hndS
  have hS_w : S_list.length < 2 ^ w := by omega
  have hmem₅ : s₅.arrs newWallMemArr = s.arrs newWallMemArr := by
    rw [harrs₅ newWallMemArr (by decide), harrs₄ newWallMemArr (by decide) (by decide),
      harrs₃ newWallMemArr (by decide) (by decide) (by decide) (by decide)]
    rfl
  rcases prefixUntilArrCmd_exec tmpPathArr1 newWallMemArr tmpPathArr2 (by decide) S S_list (s := s₅)
      h1_w hn_w hsuf₅ hS_w (by rw [hmem₅]; exact hmem_len) (fun u => by rw [hmem₅]; exact hmem_val u) with
    ⟨s₆, t_pref, hex₆, ht_pref, hpref₆, hregs₆, harrs₆⟩
  have hkeep_reg : ∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
      r ≠ 15 → r ≠ 16 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 →
      r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
      r ≠ 28 → r ≠ 29 → s₆.regs r = s.regs r := by
    intro r h6 h7 h8 h9 h10 h11 h15 h16 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29
    rw [hregs₆ r h7 h8 h9 h10 h11, hregs₅ r h7 h8 h9 h10 h11,
      hregs₄ r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21,
      hregs₃ r h6 h7 h8 h9 h10 h11 h15 h16 h18 h19 h22 h23 h24 h25 h26 h27 h28 h29]
    simp [s₂, s₁, h20, h21]
  have hkeep_arr : ∀ arr : Arr, arr ≠ bufArr → arr ≠ bufArr2 → arr ≠ coordXArr → arr ≠ coordYArr →
      arr ≠ liftArr → arr ≠ tmpPathArr1 → arr ≠ tmpPathArr2 → s₆.arrs arr = s.arrs arr := by
    intro arr ha1 ha2 ha3 ha4 ha5 ha6 ha7
    rw [harrs₆ arr ha7, harrs₅ arr ha6, harrs₄ arr ha2 ha5, harrs₃ arr ha1 ha2 ha3 ha4]
    rfl
  have hs₆ : WallStateHolds W s₆ :=
    hs.of_preserve
      (hkeep_reg 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr wallEncArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr locArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr wallMemArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr edgeOffArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr edgeLenArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr edgeU1Arr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr edgeU2Arr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr horizEdgeIdxArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr vertEdgeIdxArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨s₆, 2 + (2 + (t_ep + (t_lift + (t_suf + t_pref)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hs₆, hpref₆, hkeep_reg, hkeep_arr⟩

/-- Extend star ray `(a, i)` in `starRayArr l a i` (with center in `regCenter a` and target
coordinate `q₀ = (r_30, r_31)`) to the subwall whose vertex membership is in `newWallMemArr`. -/
def extendOneRayCmd (l a i : ℕ) : Cmd :=
  let arrP := starRayArr l a i
  let regC := regCenter a
  .seq (.assign 17 (.read arrP (.op .sub (.len arrP) (.const 1))))
  (.seq pathToSubwallCmd
  (.seq (extendStarRayCmd arrP tmpPathArr2 tmpPathArr3 regC)
    (copyArrCmd tmpPathArr3 arrP)))

theorem extendOneRayCmd_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (hh : 1 ≤ h) (hW : W.IsValid)
    (S : Finset (Fin n))
    (l a i : ℕ)
    (c : Fin n) (P : List (Fin n)) (hpre : W.IsPreStarRay c P)
    (q₀ : ℕ × ℕ) (hq₀ : q₀ ∈ GM13.elementaryWallVerts h)
    {s : State}
    (hw2 : 2 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (h2n_w : 2 * n < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w)
    (hs : WallStateHolds W s)
    (hmem_len : (s.arrs newWallMemArr).length = n)
    (hmem_val : ∀ u : Fin n, (s.arrs newWallMemArr)[u.1]? = some (if u ∈ S then 1 else 0))
    (harrP : s.arrs (starRayArr l a i) = P.map Fin.val)
    (hregC : s.regs (regCenter a) = c.1)
    (hr30 : s.regs 30 = q₀.1)
    (hr31 : s.regs 31 = q₀.2) :
    let u := P.getLast?.getD c
    let Q := W.pathToSubwall S u q₀
    let R_ray := extendStarRay c P Q
    ∃ s' t,
      Exec w (extendOneRayCmd l a i) s s' t ∧
      t ≤ 440 * elemWallNumVerts h + 50 * h + 255 * n + 1230 ∧
      WallStateHolds W s' ∧
      s'.arrs (starRayArr l a i) = R_ray.map Fin.val ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 15 → r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 →
        r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
        r ≠ 28 → r ≠ 29 → s'.regs r = s.regs r) ∧
      (∀ arr : Arr, arr ≠ bufArr → arr ≠ bufArr2 → arr ≠ coordXArr → arr ≠ coordYArr →
        arr ≠ liftArr → arr ≠ tmpPathArr1 → arr ≠ tmpPathArr2 → arr ≠ tmpPathArr3 →
        arr ≠ starRayArr l a i → s'.arrs arr = s.arrs arr) := by
  intro u Q R_ray
  have h1_w : 1 < 2 ^ w := by omega
  obtain ⟨hneP, _, hndP, _, hlastP_mem, _, _⟩ := hpre
  have hu_eq : P.getLast hneP = u := by
    dsimp [u]; rw [List.getLast?_eq_some_getLast hneP, Option.getD_some]
  have hu_mem : u ∈ W.vertexFinset := hu_eq ▸ hlastP_mem
  have hP_pos : 0 < P.length := List.length_pos_iff.mpr hneP
  have hP_le_n : P.length ≤ n := length_le_of_nodup_fin hndP
  have hP_w : P.length < 2 ^ w := by omega
  have hP1_w : P.length - 1 < 2 ^ w := by omega
  have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
  let arrP := starRayArr l a i
  let regC := regCenter a
  have hlen_arrP : (s.arrs arrP).length = P.length := by simp [arrP, harrP]
  have hlt_last : P.length - 1 < (s.arrs arrP).length := by omega
  have hget_last : (s.arrs arrP)[P.length - 1]'hlt_last = u.1 := by
    apply getElem_of_getElem? _ hlt_last
    rw [show s.arrs arrP = P.map Fin.val from harrP,
      List.getElem?_eq_getElem (by simp; omega), List.getElem_map]
    rw [← hu_eq, List.getLast_eq_getElem]
  let s₁ := s.setReg 17 u.1
  have hex₁ : Exec w (.assign 17 (.read arrP (.op .sub (.len arrP) (.const 1)))) s s₁ 5 :=
    .assign (by
      have he_len : (Expr.len arrP).eval w s = some P.length := eval_len hlen_arrP hP_w
      have he_sub : (Expr.op .sub (.len arrP) (.const 1)).eval w s = some (P.length - 1) :=
        eval_op_sub he_len (by simp [Expr.eval, checkWord, h1_w])
      exact eval_read he_sub hlt_last hget_last hu_w)
  have hs₁ : WallStateHolds W s₁ :=
    hs.of_preserve (by simp [s₁]) (by simp [s₁]) (by simp [s₁]) (by simp [s₁]) (by simp [s₁])
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rcases pathToSubwallCmd_exec W hh hW S u hu_mem q₀ hq₀ (s := s₁)
      hw2 hn_w hVJW_w hloc_w henc_w hs₁ hmem_len hmem_val
      (by simp [s₁]) (by simp [s₁, hr30]) (by simp [s₁, hr31]) with
    ⟨s₂, t_path, hex₂, ht_path, hs₂, hQ₂, hregs₂, harrs₂⟩
  have hndQ : Q.Nodup := by
    obtain ⟨hneEP, hheadEP, _, hcEP, hndEP, _⟩ := W.elemPathForVert_props hh hu_mem hq₀
    rcases List.exists_cons_of_ne_nil hneEP with ⟨p0, rest0, hcons0⟩
    have hp0 : p0 ∈ GM13.elementaryWallVerts h := by
      have : p0 = (W.elemPathForVert u q₀).head hneEP := by simp [hcons0]
      exact this ▸ hheadEP
    have hndL : (W.liftElemPath (W.elemPathForVert u q₀)).Nodup := by
      rw [hcons0]
      exact W.nodup_liftElemPath hW (hcons0 ▸ hcEP) hp0 (hcons0 ▸ hndEP)
    exact nodup_prefixUntil S (nodup_suffixFrom hndL)
  have hQ_le_n : Q.length ≤ n := length_le_of_nodup_fin hndQ
  have hQ_w : Q.length < 2 ^ w := by omega
  have hPQ_w : (P.length - 1) + Q.length < 2 ^ w := by omega
  have harrP_2 : s₂.arrs arrP = P.map Fin.val := by
    rw [harrs₂ arrP (by dsimp [arrP, starRayArr, bufArr, Arr]; omega)
      (by dsimp [arrP, starRayArr, bufArr2, Arr]; omega)
      (by dsimp [arrP, starRayArr, coordXArr, Arr]; omega)
      (by dsimp [arrP, starRayArr, coordYArr, Arr]; omega)
      (by dsimp [arrP, starRayArr, liftArr, Arr]; omega)
      (by dsimp [arrP, starRayArr, tmpPathArr1, Arr]; omega)
      (by dsimp [arrP, starRayArr, tmpPathArr2, Arr]; omega)]
    exact harrP
  have hregC_2 : s₂.regs regC = c.1 := by
    rw [hregs₂ regC (by dsimp [regC, regCenter, Reg]; omega) (by dsimp [regC, regCenter, Reg]; omega)
      (by dsimp [regC, regCenter, Reg]; omega) (by dsimp [regC, regCenter, Reg]; omega)
      (by dsimp [regC, regCenter, Reg]; omega) (by dsimp [regC, regCenter, Reg]; omega)
      (by dsimp [regC, regCenter, Reg]; omega) (by dsimp [regC, regCenter, Reg]; omega)
      (by dsimp [regC, regCenter, Reg]; omega) (by dsimp [regC, regCenter, Reg]; omega)
      (by dsimp [regC, regCenter, Reg]; omega) (by dsimp [regC, regCenter, Reg]; omega)
      (by dsimp [regC, regCenter, Reg]; omega) (by dsimp [regC, regCenter, Reg]; omega)
      (by dsimp [regC, regCenter, Reg]; omega) (by dsimp [regC, regCenter, Reg]; omega)
      (by dsimp [regC, regCenter, Reg]; omega) (by dsimp [regC, regCenter, Reg]; omega)
      (by dsimp [regC, regCenter, Reg]; omega) (by dsimp [regC, regCenter, Reg]; omega)]
    rw [State.setReg_regs_ne _ _ (by dsimp [regC, regCenter, Reg]; omega : regC ≠ 17)]
    exact hregC
  rcases extendStarRayCmd_exec arrP tmpPathArr2 tmpPathArr3 regC
      (by dsimp [arrP, starRayArr, tmpPathArr3, Arr]; omega) (by decide)
      (by dsimp [regC, regCenter, Reg]; omega) (by dsimp [regC, regCenter, Reg]; omega)
      (by dsimp [regC, regCenter, Reg]; omega)
      c P Q (s := s₂) h1_w hn_w hneP harrP_2 hQ₂ hPQ_w hP_w hQ_w hregC_2 with
    ⟨s₃, t_ext, hex₃, ht_ext, hR₃, hregs₃, harrs₃⟩
  have hR_len_le : (extendStarRay c P Q).length ≤ 2 * n := by
    dsimp [extendStarRay]
    split_ifs
    · have hle_n : (suffixFrom c Q).length ≤ n :=
        length_le_of_nodup_fin (nodup_suffixFrom (u := c) hndQ)
      omega
    · simp only [List.length_append, List.length_dropLast]
      omega
  rcases copyArrCmd_exec tmpPathArr3 arrP
      (by dsimp [arrP, starRayArr, tmpPathArr3, Arr]; omega) (s := s₃) h1_w
      (by rw [hR₃, List.length_map]; omega)
      (by rw [hR₃]; intro v hv; rcases List.mem_map.mp hv with ⟨u', _, rfl⟩; exact Nat.lt_trans u'.2 hn_w) with
    ⟨s₄, t_cp, hex₄, ht_cp, harrP_4, hregs₄, harrs₄⟩
  rw [hR₃] at harrP_4 ht_cp
  have hkeep_reg : ∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
      r ≠ 15 → r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 →
      r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
      r ≠ 28 → r ≠ 29 → s₄.regs r = s.regs r := by
    intro r h6 h7 h8 h9 h10 h11 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29
    rw [hregs₄ r h7 h8 h9 h11, hregs₃ r h7 h8 h9 h10 h11,
      hregs₂ r h6 h7 h8 h9 h10 h11 h15 h16 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29]
    simp [s₁, h17]
  have hkeep_arr : ∀ arr : Arr, arr ≠ bufArr → arr ≠ bufArr2 → arr ≠ coordXArr → arr ≠ coordYArr →
      arr ≠ liftArr → arr ≠ tmpPathArr1 → arr ≠ tmpPathArr2 → arr ≠ tmpPathArr3 →
      arr ≠ starRayArr l a i → s₄.arrs arr = s.arrs arr := by
    intro arr ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9
    rw [harrs₄ arr ha9, harrs₃ arr ha8, harrs₂ arr ha1 ha2 ha3 ha4 ha5 ha6 ha7]
    rfl
  have hs₄ : WallStateHolds W s₄ :=
    hs.of_preserve
      (hkeep_reg 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr wallEncArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by dsimp [wallEncArr, starRayArr, Arr]; omega))
      (hkeep_arr locArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by dsimp [locArr, starRayArr, Arr]; omega))
      (hkeep_arr wallMemArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by dsimp [wallMemArr, starRayArr, Arr]; omega))
      (hkeep_arr edgeOffArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by dsimp [edgeOffArr, starRayArr, Arr]; omega))
      (hkeep_arr edgeLenArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by dsimp [edgeLenArr, starRayArr, Arr]; omega))
      (hkeep_arr edgeU1Arr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by dsimp [edgeU1Arr, starRayArr, Arr]; omega))
      (hkeep_arr edgeU2Arr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by dsimp [edgeU2Arr, starRayArr, Arr]; omega))
      (hkeep_arr horizEdgeIdxArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by dsimp [horizEdgeIdxArr, starRayArr, Arr]; omega))
      (hkeep_arr vertEdgeIdxArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by dsimp [vertEdgeIdxArr, starRayArr, Arr]; omega))
  refine ⟨s₄, 5 + (t_path + (t_ext + t_cp)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by simp only [List.length_map] at ht_cp; omega,
    hs₄, harrP_4, hkeep_reg, hkeep_arr⟩

end GraphMinor.Compute

