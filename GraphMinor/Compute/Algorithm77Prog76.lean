module

public import GraphMinor.Compute.Algorithm77Prog73

/-!
# Word RAM Program for Graph Minors XIII, Step (7.6)

This file implements Step (7.6) (GM XIII, page 92) on the Word RAM, proving that it
computes the exact subwall `W' = (runStep76 hp hl hm x).W` and extended external `(l, m)`-stars
`(runStep76 hp hl hm x).rays` defined in `Algorithm77Step76.lean`.

## Structure
1. **Section 1: Deleting Realization Coordinate Maps and Inner Path Loading**
   (`rotVCmd`, `natHoleVmapCmd`, `vmapOfCodeCmd`, `loadInnerOfCodeCmd`).
2. **Section 2: Subwall Realization and Membership Marking**
   (`realizeSubwallCmd`, `markWallEncMemCmd`).
3. **Section 3: Canonical Elementary-Wall Paths and `pathToSubwallCmd`**
   (`appendRowPathCmd`, `appendElemWallUpPathCmd`, `elemWallCanonicalPathCmd`,
   `elemWallEdgeCanonicalPathCmd`, `elemPathForVertCmd`, `pathToSubwallCmd`).
4. **Section 4: Step (7.6) Iteration (`step76OneCmd`, `runStep76Cmd`)**.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

set_option linter.deprecated false

attribute [local irreducible] elemWallCoords elemWallNumVerts elemWallEdges

/-! ### Section 1: Deleting Realization Coordinate Maps and Inner Path Loading -/

/-- Rotate coordinates `(regX, regY)` by `GM13.rotV h = (2 * h + 1 - x, h - y)` where `eH` evaluates
to `h`. -/
def rotVCmd (eH : Expr) (regX regY : Reg) : Cmd :=
  .seq (.assign regX (.op .sub (.op .add (.op .mul (.const 2) eH) (.const 1)) (.reg regX)))
    (.assign regY (.op .sub eH (.reg regY)))

theorem rotVCmd_exec {w h : ℕ} {eH : Expr} (regX regY : Reg) (hne : regX ≠ regY)
    (p : ℕ × ℕ) {s : State}
    (hw2 : 2 < 2 ^ w)
    (h2h1_w : 2 * h + 1 < 2 ^ w)
    (hp1_w : p.1 < 2 ^ w)
    (hp2_w : p.2 < 2 ^ w)
    (heH : ∀ s' : State, (∀ r, r ≠ regX → s'.regs r = s.regs r) → eH.eval w s' = some h)
    (hrX : s.regs regX = p.1)
    (hrY : s.regs regY = p.2) :
    ∃ s' t,
      Exec w (rotVCmd eH regX regY) s s' t ∧
      t ≤ 2 * eH.cost + 10 ∧
      s'.regs regX = (GM13.rotV h p).1 ∧
      s'.regs regY = (GM13.rotV h p).2 ∧
      (∀ r : Reg, r ≠ regX → r ≠ regY → s'.regs r = s.regs r) ∧
      s'.arrs = s.arrs := by
  have h1_w : 1 < 2 ^ w := by omega
  have hh_w : h < 2 ^ w := by omega
  have h2h_w : 2 * h < 2 ^ w := by omega
  have hrot1_w : 2 * h + 1 - p.1 < 2 ^ w := by omega
  have hrot2_w : h - p.2 < 2 ^ w := by omega
  have heH_s : eH.eval w s = some h := heH s (fun _ _ => rfl)
  let s₁ := s.setReg regX (2 * h + 1 - p.1)
  have hex₁ :
      Exec w (.assign regX (.op .sub (.op .add (.op .mul (.const 2) eH) (.const 1)) (.reg regX)))
        s s₁ _ :=
    .assign (by simp [Expr.eval, heH_s, BinOp.eval, BinOp.raw, checkWord, hrX,
      hw2, h2h_w, h1_w, h2h1_w, hp1_w, hrot1_w])
  have heH_s₁ : eH.eval w s₁ = some h :=
    heH s₁ (fun r hr => by simp [s₁, hr])
  let s₂ := s₁.setReg regY (h - p.2)
  have hex₂ : Exec w (.assign regY (.op .sub eH (.reg regY))) s₁ s₂ _ :=
    .assign (by simp [Expr.eval, heH_s₁, BinOp.eval, BinOp.raw, checkWord, s₁,
      State.setReg_regs_ne _ _ hne.symm, hrY, hp2_w, hrot2_w])
  refine ⟨s₂, _, .seq hex₁ hex₂, by simp [Expr.cost]; omega,
    by simp [s₂, s₁, State.setReg_regs_ne _ _ hne, GM13.rotV],
    by simp [s₂, GM13.rotV],
    fun r hX hY => by simp [s₂, s₁, hX, hY],
    rfl⟩

/-- Apply `natHoleVmap Y0 c0` in place to `(regX, regY)` where `r_16 = Y0` and `r_17 = c0`. -/
def natHoleVmapCmd (regX regY : Reg) : Cmd :=
  .ite (.op .lt (.reg regY) (.reg 16))
    (.ite (.op .lt (.reg regX) (.reg 17))
      .skip
      (.assign regX (.op .add (.reg regX) (.const 4))))
    (.seq (.assign regX (.op .add (.reg regX) (.const 2)))
      (.assign regY (.op .add (.reg regY) (.const 2))))

theorem natHoleVmapCmd_exec {w Y0 c0 : ℕ} (regX regY : Reg) (hne : regX ≠ regY)
    (_hne_Y16 : regY ≠ 16) (_hne_X17 : regX ≠ 17)
    (p : ℕ × ℕ) {s : State}
    (hw4 : 4 < 2 ^ w)
    (hY0_w : Y0 < 2 ^ w)
    (hc0_w : c0 < 2 ^ w)
    (hp1_w : p.1 + 4 < 2 ^ w)
    (hp2_w : p.2 + 2 < 2 ^ w)
    (hr16 : s.regs 16 = Y0)
    (hr17 : s.regs 17 = c0)
    (hrX : s.regs regX = p.1)
    (hrY : s.regs regY = p.2) :
    ∃ s' t,
      Exec w (natHoleVmapCmd regX regY) s s' t ∧
      t ≤ 15 ∧
      s'.regs regX = (natHoleVmap Y0 c0 p).1 ∧
      s'.regs regY = (natHoleVmap Y0 c0 p).2 ∧
      (∀ r : Reg, r ≠ regX → r ≠ regY → s'.regs r = s.regs r) ∧
      s'.arrs = s.arrs := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hp1_0_w : p.1 < 2 ^ w := by omega
  have hp1_2_w : p.1 + 2 < 2 ^ w := by omega
  have hp2_0_w : p.2 < 2 ^ w := by omega
  by_cases hy : p.2 < Y0
  · have hcondY : (Expr.op .lt (.reg regY) (.reg 16)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrY, hr16, hp2_0_w, hY0_w, hy, h1_w]
    by_cases hx : p.1 < c0
    · have hcondX : (Expr.op .lt (.reg regX) (.reg 17)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrX, hr17, hp1_0_w, hc0_w, hx, h1_w]
      refine ⟨s, _, .ite_true hcondY (by omega) (.ite_true hcondX (by omega) (.skip s)),
        by simp [Expr.cost],
        by simp [natHoleVmap, hy, hx, hrX],
        by simp [natHoleVmap, hy, hx, hrY],
        fun _ _ _ => rfl, rfl⟩
    · have hcondX : (Expr.op .lt (.reg regX) (.reg 17)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrX, hr17, hp1_0_w, hc0_w, hx, h0_w]
      let s₁ := s.setReg regX (p.1 + 4)
      have hex₁ : Exec w (.assign regX (.op .add (.reg regX) (.const 4))) s s₁ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrX, hp1_0_w, hw4, hp1_w])
      refine ⟨s₁, _, .ite_true hcondY (by omega) (.ite_false hcondX hex₁),
        by simp [Expr.cost],
        by simp [s₁, natHoleVmap, hy, hx],
        by simp [s₁, State.setReg_regs_ne _ _ hne.symm, natHoleVmap, hy, hx, hrY],
        fun r hX _ => by simp [s₁, hX], rfl⟩
  · have hcondY : (Expr.op .lt (.reg regY) (.reg 16)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrY, hr16, hp2_0_w, hY0_w, hy, h0_w]
    let s₁ := s.setReg regX (p.1 + 2)
    have hex₁ : Exec w (.assign regX (.op .add (.reg regX) (.const 2))) s s₁ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrX, hp1_0_w, h2_w, hp1_2_w])
    let s₂ := s₁.setReg regY (p.2 + 2)
    have hex₂ : Exec w (.assign regY (.op .add (.reg regY) (.const 2))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁,
        State.setReg_regs_ne _ _ hne.symm, hrY, hp2_0_w, h2_w, hp2_w])
    refine ⟨s₂, _, .ite_false hcondY (.seq hex₁ hex₂),
      by simp [Expr.cost],
      by simp [s₂, s₁, State.setReg_regs_ne _ _ hne, natHoleVmap, hy],
      by simp [s₂, natHoleVmap, hy],
      fun r hX hY => by simp [s₂, s₁, hX, hY], rfl⟩

/-- Apply `vmapOfCode h' code` in place to `(regX, regY)` where `r_22 = h'` and
`(r_15, r_16, r_17) = (code.mode, code.Y0, code.c0)`. -/
def vmapOfCodeCmd (regX regY : Reg) : Cmd :=
  .ite (exprEq (.reg 15) (.const 0))
    (.seq (.assign regX (.op .add (.reg regX) (.const 1)))
      (.assign regY (.op .add (.reg regY) (.const 1))))
    (.ite (exprEq (.reg 15) (.const 1))
      (.seq (.assign regX (.op .add (.reg regX) (.const 3)))
        (.assign regY (.op .add (.reg regY) (.const 1))))
      (.ite (exprEq (.reg 15) (.const 2))
        (natHoleVmapCmd regX regY)
        (.seq (rotVCmd (.reg 22) regX regY)
          (.seq (natHoleVmapCmd regX regY)
            (rotVCmd (.op .add (.reg 22) (.const 2)) regX regY)))))

theorem vmapOfCodeCmd_exec {w h' : ℕ} (code : RealizationCode)
    (regX regY : Reg) (hne : regX ≠ regY)
    (_hne_X15 : regX ≠ 15) (hne_X16 : regX ≠ 16) (hne_X17 : regX ≠ 17) (hne_X22 : regX ≠ 22)
    (_hne_Y15 : regY ≠ 15) (hne_Y16 : regY ≠ 16) (hne_Y17 : regY ≠ 17) (hne_Y22 : regY ≠ 22)
    (p : ℕ × ℕ) {s : State}
    (hw4 : 4 < 2 ^ w)
    (hmode_w : code.mode < 2 ^ w)
    (hY0_w : code.Y0 < 2 ^ w)
    (hc0_w : code.c0 < 2 ^ w)
    (h2h'9_w : 2 * h' + 9 < 2 ^ w)
    (hp1_le : p.1 ≤ 2 * h' + 1)
    (hp2_le : p.2 ≤ h')
    (hr15 : s.regs 15 = code.mode)
    (hr16 : s.regs 16 = code.Y0)
    (hr17 : s.regs 17 = code.c0)
    (hr22 : s.regs 22 = h')
    (hrX : s.regs regX = p.1)
    (hrY : s.regs regY = p.2) :
    ∃ s' t,
      Exec w (vmapOfCodeCmd regX regY) s s' t ∧
      t ≤ 80 ∧
      s'.regs regX = (vmapOfCode h' code p).1 ∧
      s'.regs regY = (vmapOfCode h' code p).2 ∧
      (∀ r : Reg, r ≠ regX → r ≠ regY → s'.regs r = s.regs r) ∧
      s'.arrs = s.arrs := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have hh'_w : h' < 2 ^ w := by omega
  have hp1_w : p.1 < 2 ^ w := by omega
  have hp1_1_w : p.1 + 1 < 2 ^ w := by omega
  have hp1_3_w : p.1 + 3 < 2 ^ w := by omega
  have hp1_4_w : p.1 + 4 < 2 ^ w := by omega
  have hp2_w : p.2 < 2 ^ w := by omega
  have hp2_1_w : p.2 + 1 < 2 ^ w := by omega
  have hp2_2_w : p.2 + 2 < 2 ^ w := by omega
  have he15 : (Expr.reg 15).eval w s = some code.mode := by
    simp [Expr.eval, checkWord, hr15, hmode_w]
  have hcond0 : (exprEq (.reg 15) (.const 0)).eval w s = some (if code.mode = 0 then 1 else 0) :=
    eval_exprEq h1_w he15 (by simp [Expr.eval, checkWord, h0_w])
  by_cases hm0 : code.mode = 0
  · rw [if_pos hm0] at hcond0
    let s₁ := s.setReg regX (p.1 + 1)
    have hex₁ : Exec w (.assign regX (.op .add (.reg regX) (.const 1))) s s₁ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrX, hp1_w, h1_w, hp1_1_w])
    let s₂ := s₁.setReg regY (p.2 + 1)
    have hex₂ : Exec w (.assign regY (.op .add (.reg regY) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁,
        State.setReg_regs_ne _ _ hne.symm, hrY, hp2_w, h1_w, hp2_1_w])
    refine ⟨s₂, _, .ite_true hcond0 (by omega) (.seq hex₁ hex₂),
      by simp [exprEq, Expr.cost],
      by simp [s₂, s₁, State.setReg_regs_ne _ _ hne, vmapOfCode, hm0],
      by simp [s₂, vmapOfCode, hm0],
      fun r hX hY => by simp [s₂, s₁, hX, hY], rfl⟩
  · rw [if_neg hm0] at hcond0
    have hcond1 : (exprEq (.reg 15) (.const 1)).eval w s = some (if code.mode = 1 then 1 else 0) :=
      eval_exprEq h1_w he15 (by simp [Expr.eval, checkWord, h1_w])
    by_cases hm1 : code.mode = 1
    · rw [if_pos hm1] at hcond1
      let s₁ := s.setReg regX (p.1 + 3)
      have hex₁ : Exec w (.assign regX (.op .add (.reg regX) (.const 3))) s s₁ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrX, hp1_w, h3_w, hp1_3_w])
      let s₂ := s₁.setReg regY (p.2 + 1)
      have hex₂ : Exec w (.assign regY (.op .add (.reg regY) (.const 1))) s₁ s₂ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁,
          State.setReg_regs_ne _ _ hne.symm, hrY, hp2_w, h1_w, hp2_1_w])
      refine ⟨s₂, _, .ite_false hcond0 (.ite_true hcond1 (by omega) (.seq hex₁ hex₂)),
        by simp [exprEq, Expr.cost],
        by simp [s₂, s₁, State.setReg_regs_ne _ _ hne, vmapOfCode, hm1],
        by simp [s₂, vmapOfCode, hm1],
        fun r hX hY => by simp [s₂, s₁, hX, hY], rfl⟩
    · rw [if_neg hm1] at hcond1
      have hcond2 : (exprEq (.reg 15) (.const 2)).eval w s = some (if code.mode = 2 then 1 else 0) :=
        eval_exprEq h1_w he15 (by simp [Expr.eval, checkWord, h2_w])
      by_cases hm2 : code.mode = 2
      · rw [if_pos hm2] at hcond2
        rcases natHoleVmapCmd_exec regX regY hne hne_Y16 hne_X17 p
            hw4 hY0_w hc0_w hp1_4_w hp2_2_w hr16 hr17 hrX hrY with
          ⟨s', t_v, hex_v, ht_v, hX', hY', hregs', harrs'⟩
        refine ⟨s', _,
          .ite_false hcond0 (.ite_false hcond1 (.ite_true hcond2 (by omega) hex_v)),
          by simp [exprEq, Expr.cost]; omega,
          by simpa [vmapOfCode, hm2] using hX',
          by simpa [vmapOfCode, hm2] using hY',
          hregs', harrs'⟩
      · rw [if_neg hm2] at hcond2
        rcases rotVCmd_exec (h := h') (eH := .reg 22) regX regY hne p (s := s)
            h2_w (by omega) hp1_w hp2_w
            (fun s' hs' => by simp [Expr.eval, checkWord, hs' 22 hne_X22.symm, hr22, hh'_w])
            hrX hrY with
          ⟨s₁, t₁, hex₁, ht₁, hX₁, hY₁, hregs₁, harrs₁⟩
        let p₁ := GM13.rotV h' p
        have hp₁1_le : p₁.1 ≤ 2 * h' + 1 := by dsimp [p₁, GM13.rotV]; omega
        have hp₁2_le : p₁.2 ≤ h' := by dsimp [p₁, GM13.rotV]; omega
        rcases natHoleVmapCmd_exec regX regY hne hne_Y16 hne_X17 p₁ (s := s₁)
            hw4 hY0_w hc0_w (by omega) (by omega)
            (by rw [hregs₁ 16 hne_X16.symm hne_Y16.symm, hr16])
            (by rw [hregs₁ 17 hne_X17.symm hne_Y17.symm, hr17])
            hX₁ hY₁ with
          ⟨s₂, t₂, hex₂, ht₂, hX₂, hY₂, hregs₂, harrs₂⟩
        let p₂ := natHoleVmap code.Y0 code.c0 p₁
        have hp₂1_w : p₂.1 < 2 ^ w := by
          dsimp [p₂, natHoleVmap]; split_ifs <;> omega
        have hp₂2_w : p₂.2 < 2 ^ w := by
          dsimp [p₂, natHoleVmap]; split_ifs <;> omega
        have hh'2_w : h' + 2 < 2 ^ w := by omega
        rcases rotVCmd_exec (h := h' + 2) (eH := .op .add (.reg 22) (.const 2)) regX regY hne p₂
            (s := s₂) h2_w (by omega) hp₂1_w hp₂2_w
            (fun s' hs' => by
              have hr22' : s'.regs 22 = h' := by
                rw [hs' 22 hne_X22.symm, hregs₂ 22 hne_X22.symm hne_Y22.symm,
                  hregs₁ 22 hne_X22.symm hne_Y22.symm, hr22]
              simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr22', hh'_w, h2_w, hh'2_w])
            hX₂ hY₂ with
          ⟨s₃, t₃, hex₃, ht₃, hX₃, hY₃, hregs₃, harrs₃⟩
        refine ⟨s₃, _,
          .ite_false hcond0 (.ite_false hcond1 (.ite_false hcond2
            (.seq hex₁ (.seq hex₂ hex₃)))),
          by simp [exprEq, Expr.cost] at ht₁ ht₃ ⊢; omega,
          by simpa [vmapOfCode, hm0, hm1, hm2, p₂, p₁] using hX₃,
          by simpa [vmapOfCode, hm0, hm1, hm2, p₂, p₁] using hY₃,
          fun r hX hY => by
            rw [hregs₃ r hX hY, hregs₂ r hX hY, hregs₁ r hX hY],
          harrs₃.trans (harrs₂.trans harrs₁)⟩

/-- Write `[]` to `(coordXArr, coordYArr)` and set `r_11 := 0`. -/
def write0InnerCoordsCmd : Cmd :=
  .seq (.alloc coordXArr (.const 0))
    (.seq (.alloc coordYArr (.const 0))
      (.assign 11 (.const 0)))

/-- Write one point `(eX, eY)` (rotated by `rotV (h' + 2)` if `r_15 == 3`) into index `idx` of
`(coordXArr, coordYArr)`. Uses scratch registers `r_8, r_9`. -/
def writeOneInnerCoordCmd (idx : ℕ) (eX eY : Expr) : Cmd :=
  .seq (.assign 8 eX)
    (.seq (.assign 9 eY)
      (.seq (.ite (exprEq (.reg 15) (.const 3))
          (rotVCmd (.op .add (.reg 22) (.const 2)) 8 9)
          .skip)
        (.seq (.write coordXArr (.const idx) (.reg 8))
          (.write coordYArr (.const idx) (.reg 9)))))

/-- Write 4 points sequentially into indices `0, 1, 2, 3` of `(coordXArr, coordYArr)`. -/
def write4SeqCmd (eX0 eY0 eX1 eY1 eX2 eY2 eX3 eY3 : Expr) : Cmd :=
  .seq (writeOneInnerCoordCmd 0 eX0 eY0)
    (.seq (writeOneInnerCoordCmd 1 eX1 eY1)
      (.seq (writeOneInnerCoordCmd 2 eX2 eY2)
        (writeOneInnerCoordCmd 3 eX3 eY3)))

/-- Allocate `(coordXArr, coordYArr)` of length `4`, write 4 points in forward order (`r_6 != 0`)
or reverse order (`r_6 == 0`), each rotated by `rotV (h' + 2)` if `r_15 == 3`, and set `r_11 := 4`. -/
def write4InnerCoordsCmd (eX0 eY0 eX1 eY1 eX2 eY2 eX3 eY3 : Expr) : Cmd :=
  .seq (.alloc coordXArr (.const 4))
    (.seq (.alloc coordYArr (.const 4))
      (.seq (.ite (.reg 6)
          (write4SeqCmd eX0 eY0 eX1 eY1 eX2 eY2 eX3 eY3)
          (write4SeqCmd eX3 eY3 eX2 eY2 eX1 eY1 eX0 eY0))
        (.assign 11 (.const 4))))

/-- Postcondition for `loadInnerOfCodeCmd` leaves: `(coordXArr, coordYArr)` store `L` and `r_11 = L.length`. -/
def InnerCoordsPost (s : State) (L : List (ℕ × ℕ)) (s' : State) : Prop :=
  s'.arrs coordXArr = L.map Prod.fst ∧
  s'.arrs coordYArr = L.map Prod.snd ∧
  s'.regs 11 = L.length ∧
  (∀ r : Reg, r ≠ 8 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
  (∀ a : Arr, a ≠ coordXArr → a ≠ coordYArr → s'.arrs a = s.arrs a)

/-- Uniform evaluation predicate for expressions depending only on `(r_18, r_19, r_20, r_21) = (a.1, a.2, b.1, b.2)`. -/
def EvalAB (w : ℕ) (a b : ℕ × ℕ) (e : Expr) (val : ℕ) : Prop :=
  ∀ s : State, s.regs 18 = a.1 → s.regs 19 = a.2 → s.regs 20 = b.1 → s.regs 21 = b.2 →
    e.eval w s = some val

theorem write0InnerCoordsCmd_exec {w : ℕ} {s : State}
    (hw1 : 1 < 2 ^ w) :
    ∃ s' t,
      Exec w write0InnerCoordsCmd s s' t ∧
      t ≤ 6 ∧
      InnerCoordsPost s [] s' := by
  have h0_w : 0 < 2 ^ w := by omega
  have he0_s : (Expr.const 0).eval w s = some 0 := by simp [Expr.eval, checkWord, h0_w]
  let s₁ := s.setArr coordXArr (List.replicate 0 0)
  have hex₁ : Exec w (.alloc coordXArr (.const 0)) s s₁ _ := .alloc he0_s
  have he0_s₁ : (Expr.const 0).eval w s₁ = some 0 := by simp [Expr.eval, checkWord, h0_w]
  let s₂ := s₁.setArr coordYArr (List.replicate 0 0)
  have hex₂ : Exec w (.alloc coordYArr (.const 0)) s₁ s₂ _ := .alloc he0_s₁
  let s₃ := s₂.setReg 11 0
  have hex₃ : Exec w (.assign 11 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  refine ⟨s₃, _, .seq hex₁ (.seq hex₂ hex₃), by simp [Expr.cost],
    by simp [s₃, s₂, s₁], by simp [s₃, s₂], by simp [s₃],
    fun r _ _ h11 => by simp [s₃, s₂, s₁, h11],
    fun a ha1 ha2 => by simp [s₃, s₂, s₁, ha1, ha2]⟩

theorem writeOneInnerCoordCmd_exec {w h' mode : ℕ} (a b : ℕ × ℕ)
    (idx : ℕ) (hidx : idx < 4)
    (p : ℕ × ℕ) (eX eY : Expr) {s : State}
    (hw4 : 4 < 2 ^ w)
    (hmode_w : mode < 2 ^ w)
    (h2h'5_w : 2 * h' + 5 < 2 ^ w)
    (hp1_w : p.1 < 2 ^ w)
    (hp2_w : p.2 < 2 ^ w)
    (heX : EvalAB w a b eX p.1)
    (heY : EvalAB w a b eY p.2)
    (hr15 : s.regs 15 = mode)
    (hr22 : s.regs 22 = h')
    (hr18 : s.regs 18 = a.1)
    (hr19 : s.regs 19 = a.2)
    (hr20 : s.regs 20 = b.1)
    (hr21 : s.regs 21 = b.2)
    (hcx_len : (s.arrs coordXArr).length = 4)
    (hcy_len : (s.arrs coordYArr).length = 4) :
    let q := if mode = 3 then GM13.rotV (h' + 2) p else p
    ∃ s' t,
      Exec w (writeOneInnerCoordCmd idx eX eY) s s' t ∧
      t ≤ eX.cost + eY.cost + 40 ∧
      s'.arrs coordXArr = (s.arrs coordXArr).set idx q.1 ∧
      s'.arrs coordYArr = (s.arrs coordYArr).set idx q.2 ∧
      (∀ r : Reg, r ≠ 8 → r ≠ 9 → s'.regs r = s.regs r) ∧
      (∀ arr : Arr, arr ≠ coordXArr → arr ≠ coordYArr → s'.arrs arr = s.arrs arr) := by
  intro q
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have hh'_w : h' < 2 ^ w := by omega
  have hh'2_w : h' + 2 < 2 ^ w := by omega
  have hidx_w : idx < 2 ^ w := by omega
  let s₁ := s.setReg 8 p.1
  have hex₁ : Exec w (.assign 8 eX) s s₁ (eX.cost + 1) :=
    .assign (heX s hr18 hr19 hr20 hr21)
  let s₂ := s₁.setReg 9 p.2
  have hex₂ : Exec w (.assign 9 eY) s₁ s₂ (eY.cost + 1) :=
    .assign (heY s₁ (by simp [s₁, hr18]) (by simp [s₁, hr19]) (by simp [s₁, hr20]) (by simp [s₁, hr21]))
  have he15 : (Expr.reg 15).eval w s₂ = some mode := by
    simp [Expr.eval, checkWord, s₂, s₁, hr15, hmode_w]
  have hcond3 : (exprEq (.reg 15) (.const 3)).eval w s₂ = some (if mode = 3 then 1 else 0) :=
    eval_exprEq h1_w he15 (by simp [Expr.eval, checkWord, h3_w])
  have hrot :
      ∃ s₃ t_rot,
        Exec w (.ite (exprEq (.reg 15) (.const 3))
          (rotVCmd (.op .add (.reg 22) (.const 2)) 8 9) .skip) s₂ s₃ t_rot ∧
        t_rot ≤ 25 ∧
        s₃.regs 8 = q.1 ∧
        s₃.regs 9 = q.2 ∧
        (∀ r : Reg, r ≠ 8 → r ≠ 9 → s₃.regs r = s.regs r) ∧
        s₃.arrs = s.arrs := by
    by_cases hm3 : mode = 3
    · rw [if_pos hm3] at hcond3
      rcases rotVCmd_exec (h := h' + 2) (eH := .op .add (.reg 22) (.const 2)) 8 9 (by decide) p
          (s := s₂) h2_w (by omega) hp1_w hp2_w
          (fun s' hs' => by
            have hr22' : s'.regs 22 = h' := by
              rw [hs' 22 (by decide)]; simp [s₂, s₁, hr22]
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr22', hh'_w, h2_w, hh'2_w])
          (by simp [s₂, s₁]) (by simp [s₂]) with
        ⟨s₃, t_r, hex_r, ht_r, h8, h9, hregs₃, harrs₃⟩
      refine ⟨s₃, _, .ite_true hcond3 (by omega) hex_r,
        by simp [exprEq, Expr.cost] at ht_r ⊢; omega,
        by simpa [q, hm3] using h8,
        by simpa [q, hm3] using h9,
        fun r h8' h9' => by rw [hregs₃ r h8' h9']; simp [s₂, s₁, h8', h9'],
        harrs₃⟩
    · rw [if_neg hm3] at hcond3
      refine ⟨s₂, _, .ite_false hcond3 (.skip s₂),
        by simp [exprEq, Expr.cost],
        by simp [s₂, s₁, q, hm3],
        by simp [s₂, q, hm3],
        fun r h8' h9' => by simp [s₂, s₁, h8', h9'],
        rfl⟩
  rcases hrot with ⟨s₃, t_rot, hex_rot, ht_rot, hr8_3, hr9_3, hregs₃, harrs₃⟩
  have hq1_w : q.1 < 2 ^ w := by dsimp [q, GM13.rotV]; split_ifs <;> omega
  have hq2_w : q.2 < 2 ^ w := by dsimp [q, GM13.rotV]; split_ifs <;> omega
  let s₄ := s₃.writeArr coordXArr idx q.1
  have hex₄ : Exec w (.write coordXArr (.const idx) (.reg 8)) s₃ s₄ 3 :=
    .write (by simp [Expr.eval, checkWord, hidx_w])
      (by simp [Expr.eval, checkWord, hr8_3, hq1_w])
      (by rw [harrs₃, hcx_len]; exact hidx)
  let s₅ := s₄.writeArr coordYArr idx q.2
  have hex₅ : Exec w (.write coordYArr (.const idx) (.reg 9)) s₄ s₅ 3 :=
    .write (by simp [Expr.eval, checkWord, hidx_w])
      (by simp [Expr.eval, checkWord, s₄, hr9_3, hq2_w])
      (by simp [s₄, State.writeArr_arrs_ne, harrs₃, hcy_len, hidx])
  refine ⟨s₅, (eX.cost + 1) + ((eY.cost + 1) + (t_rot + (3 + 3))),
    .seq hex₁ (.seq hex₂ (.seq hex_rot (.seq hex₄ hex₅))),
    by omega,
    by simp [s₅, s₄, harrs₃],
    by simp [s₅, s₄, harrs₃],
    fun r h8 h9 => by simp [s₅, s₄, hregs₃ r h8 h9],
    fun arr ha1 ha2 => by
      simp [s₅, s₄, State.writeArr_arrs_ne _ _ _ ha1, State.writeArr_arrs_ne _ _ _ ha2, harrs₃]⟩

theorem write4SeqCmd_exec {w h' mode : ℕ} (a b p₀ p₁ p₂ p₃ : ℕ × ℕ)
    (eX0 eY0 eX1 eY1 eX2 eY2 eX3 eY3 : Expr) {s : State}
    (hw4 : 4 < 2 ^ w)
    (hmode_w : mode < 2 ^ w)
    (h2h'5_w : 2 * h' + 5 < 2 ^ w)
    (hp₀_w : p₀.1 < 2 ^ w ∧ p₀.2 < 2 ^ w)
    (hp₁_w : p₁.1 < 2 ^ w ∧ p₁.2 < 2 ^ w)
    (hp₂_w : p₂.1 < 2 ^ w ∧ p₂.2 < 2 ^ w)
    (hp₃_w : p₃.1 < 2 ^ w ∧ p₃.2 < 2 ^ w)
    (heX0 : EvalAB w a b eX0 p₀.1) (heY0 : EvalAB w a b eY0 p₀.2)
    (heX1 : EvalAB w a b eX1 p₁.1) (heY1 : EvalAB w a b eY1 p₁.2)
    (heX2 : EvalAB w a b eX2 p₂.1) (heY2 : EvalAB w a b eY2 p₂.2)
    (heX3 : EvalAB w a b eX3 p₃.1) (heY3 : EvalAB w a b eY3 p₃.2)
    (hr15 : s.regs 15 = mode) (hr22 : s.regs 22 = h')
    (hr18 : s.regs 18 = a.1) (hr19 : s.regs 19 = a.2)
    (hr20 : s.regs 20 = b.1) (hr21 : s.regs 21 = b.2)
    (hcx : s.arrs coordXArr = List.replicate 4 0)
    (hcy : s.arrs coordYArr = List.replicate 4 0) :
    let L := if mode = 3 then [p₀, p₁, p₂, p₃].map (GM13.rotV (h' + 2)) else [p₀, p₁, p₂, p₃]
    ∃ s' t,
      Exec w (write4SeqCmd eX0 eY0 eX1 eY1 eX2 eY2 eX3 eY3) s s' t ∧
      t ≤ (eX0.cost + eY0.cost + eX1.cost + eY1.cost +
           eX2.cost + eY2.cost + eX3.cost + eY3.cost) + 160 ∧
      s'.arrs coordXArr = L.map Prod.fst ∧
      s'.arrs coordYArr = L.map Prod.snd ∧
      (∀ r : Reg, r ≠ 8 → r ≠ 9 → s'.regs r = s.regs r) ∧
      (∀ arr : Arr, arr ≠ coordXArr → arr ≠ coordYArr → s'.arrs arr = s.arrs arr) := by
  intro L
  rcases writeOneInnerCoordCmd_exec a b 0 (by decide) p₀ eX0 eY0
      hw4 hmode_w h2h'5_w hp₀_w.1 hp₀_w.2 heX0 heY0
      hr15 hr22 hr18 hr19 hr20 hr21
      (by rw [hcx]; rfl) (by rw [hcy]; rfl) with
    ⟨s₁, t₁, hex₁, ht₁, hcx₁, hcy₁, hregs₁, harrs₁⟩
  rcases writeOneInnerCoordCmd_exec a b 1 (by decide) p₁ eX1 eY1 (s := s₁)
      hw4 hmode_w h2h'5_w hp₁_w.1 hp₁_w.2 heX1 heY1
      (by rw [hregs₁ 15 (by decide) (by decide), hr15])
      (by rw [hregs₁ 22 (by decide) (by decide), hr22])
      (by rw [hregs₁ 18 (by decide) (by decide), hr18])
      (by rw [hregs₁ 19 (by decide) (by decide), hr19])
      (by rw [hregs₁ 20 (by decide) (by decide), hr20])
      (by rw [hregs₁ 21 (by decide) (by decide), hr21])
      (by rw [hcx₁, hcx]; rfl) (by rw [hcy₁, hcy]; rfl) with
    ⟨s₂, t₂, hex₂, ht₂, hcx₂, hcy₂, hregs₂, harrs₂⟩
  rcases writeOneInnerCoordCmd_exec a b 2 (by decide) p₂ eX2 eY2 (s := s₂)
      hw4 hmode_w h2h'5_w hp₂_w.1 hp₂_w.2 heX2 heY2
      (by rw [hregs₂ 15 (by decide) (by decide), hregs₁ 15 (by decide) (by decide), hr15])
      (by rw [hregs₂ 22 (by decide) (by decide), hregs₁ 22 (by decide) (by decide), hr22])
      (by rw [hregs₂ 18 (by decide) (by decide), hregs₁ 18 (by decide) (by decide), hr18])
      (by rw [hregs₂ 19 (by decide) (by decide), hregs₁ 19 (by decide) (by decide), hr19])
      (by rw [hregs₂ 20 (by decide) (by decide), hregs₁ 20 (by decide) (by decide), hr20])
      (by rw [hregs₂ 21 (by decide) (by decide), hregs₁ 21 (by decide) (by decide), hr21])
      (by rw [hcx₂, hcx₁, hcx]; rfl) (by rw [hcy₂, hcy₁, hcy]; rfl) with
    ⟨s₃, t₃, hex₃, ht₃, hcx₃, hcy₃, hregs₃, harrs₃⟩
  rcases writeOneInnerCoordCmd_exec a b 3 (by decide) p₃ eX3 eY3 (s := s₃)
      hw4 hmode_w h2h'5_w hp₃_w.1 hp₃_w.2 heX3 heY3
      (by rw [hregs₃ 15 (by decide) (by decide), hregs₂ 15 (by decide) (by decide),
            hregs₁ 15 (by decide) (by decide), hr15])
      (by rw [hregs₃ 22 (by decide) (by decide), hregs₂ 22 (by decide) (by decide),
            hregs₁ 22 (by decide) (by decide), hr22])
      (by rw [hregs₃ 18 (by decide) (by decide), hregs₂ 18 (by decide) (by decide),
            hregs₁ 18 (by decide) (by decide), hr18])
      (by rw [hregs₃ 19 (by decide) (by decide), hregs₂ 19 (by decide) (by decide),
            hregs₁ 19 (by decide) (by decide), hr19])
      (by rw [hregs₃ 20 (by decide) (by decide), hregs₂ 20 (by decide) (by decide),
            hregs₁ 20 (by decide) (by decide), hr20])
      (by rw [hregs₃ 21 (by decide) (by decide), hregs₂ 21 (by decide) (by decide),
            hregs₁ 21 (by decide) (by decide), hr21])
      (by rw [hcx₃, hcx₂, hcx₁, hcx]; rfl) (by rw [hcy₃, hcy₂, hcy₁, hcy]; rfl) with
    ⟨s₄, t₄, hex₄, ht₄, hcx₄, hcy₄, hregs₄, harrs₄⟩
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega,
    by
      rw [hcx₄, hcx₃, hcx₂, hcx₁, hcx]
      dsimp [L]
      split_ifs <;> rfl,
    by
      rw [hcy₄, hcy₃, hcy₂, hcy₁, hcy]
      dsimp [L]
      split_ifs <;> rfl,
    fun r h8 h9 => by rw [hregs₄ r h8 h9, hregs₃ r h8 h9, hregs₂ r h8 h9, hregs₁ r h8 h9],
    fun arr ha1 ha2 => by rw [harrs₄ arr ha1 ha2, harrs₃ arr ha1 ha2, harrs₂ arr ha1 ha2, harrs₁ arr ha1 ha2]⟩

theorem write4InnerCoordsCmd_exec {w h' mode : ℕ} (b_lt : Bool) (a b p₀ p₁ p₂ p₃ : ℕ × ℕ)
    (eX0 eY0 eX1 eY1 eX2 eY2 eX3 eY3 : Expr) {s : State}
    (hw4 : 4 < 2 ^ w)
    (hmode_w : mode < 2 ^ w)
    (h2h'5_w : 2 * h' + 5 < 2 ^ w)
    (hp₀_w : p₀.1 < 2 ^ w ∧ p₀.2 < 2 ^ w)
    (hp₁_w : p₁.1 < 2 ^ w ∧ p₁.2 < 2 ^ w)
    (hp₂_w : p₂.1 < 2 ^ w ∧ p₂.2 < 2 ^ w)
    (hp₃_w : p₃.1 < 2 ^ w ∧ p₃.2 < 2 ^ w)
    (heX0 : EvalAB w a b eX0 p₀.1) (heY0 : EvalAB w a b eY0 p₀.2)
    (heX1 : EvalAB w a b eX1 p₁.1) (heY1 : EvalAB w a b eY1 p₁.2)
    (heX2 : EvalAB w a b eX2 p₂.1) (heY2 : EvalAB w a b eY2 p₂.2)
    (heX3 : EvalAB w a b eX3 p₃.1) (heY3 : EvalAB w a b eY3 p₃.2)
    (hr6 : s.regs 6 = if b_lt then 1 else 0)
    (hr15 : s.regs 15 = mode) (hr22 : s.regs 22 = h')
    (hr18 : s.regs 18 = a.1) (hr19 : s.regs 19 = a.2)
    (hr20 : s.regs 20 = b.1) (hr21 : s.regs 21 = b.2) :
    let L_dir := if b_lt then [p₀, p₁, p₂, p₃] else [p₀, p₁, p₂, p₃].reverse
    let L := if mode = 3 then L_dir.map (GM13.rotV (h' + 2)) else L_dir
    ∃ s' t,
      Exec w (write4InnerCoordsCmd eX0 eY0 eX1 eY1 eX2 eY2 eX3 eY3) s s' t ∧
      t ≤ (eX0.cost + eY0.cost + eX1.cost + eY1.cost +
           eX2.cost + eY2.cost + eX3.cost + eY3.cost) + 180 ∧
      InnerCoordsPost s L s' := by
  intro L_dir L
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have he4_s : (Expr.const 4).eval w s = some 4 := by simp [Expr.eval, checkWord, hw4]
  let s₁ := s.setArr coordXArr (List.replicate 4 0)
  have hex₁ : Exec w (.alloc coordXArr (.const 4)) s s₁ _ := .alloc he4_s
  have he4_s₁ : (Expr.const 4).eval w s₁ = some 4 := by simp [Expr.eval, checkWord, hw4]
  let s₂ := s₁.setArr coordYArr (List.replicate 4 0)
  have hex₂ : Exec w (.alloc coordYArr (.const 4)) s₁ s₂ _ := .alloc he4_s₁
  have hcx₂ : s₂.arrs coordXArr = List.replicate 4 0 := by simp [s₂, s₁]
  have hcy₂ : s₂.arrs coordYArr = List.replicate 4 0 := by simp [s₂]
  cases b_lt
  · have hcond : (Expr.reg 6).eval w s₂ = some 0 := by
      simp [Expr.eval, checkWord, s₂, s₁, hr6, h0_w]
    rcases write4SeqCmd_exec a b p₃ p₂ p₁ p₀ eX3 eY3 eX2 eY2 eX1 eY1 eX0 eY0 (s := s₂)
        hw4 hmode_w h2h'5_w hp₃_w hp₂_w hp₁_w hp₀_w
        heX3 heY3 heX2 heY2 heX1 heY1 heX0 heY0
        (by simp [s₂, s₁, hr15]) (by simp [s₂, s₁, hr22])
        (by simp [s₂, s₁, hr18]) (by simp [s₂, s₁, hr19])
        (by simp [s₂, s₁, hr20]) (by simp [s₂, s₁, hr21])
        hcx₂ hcy₂ with
      ⟨s₃, t₃, hex₃, ht₃, hcx₃, hcy₃, hregs₃, harrs₃⟩
    let s₄ := s₃.setReg 11 4
    have hex₄ : Exec w (.assign 11 (.const 4)) s₃ s₄ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw4])
    refine ⟨s₄, _,
      .seq hex₁ (.seq hex₂ (.seq (.ite_false hcond hex₃) hex₄)),
      by simp [Expr.cost]; omega,
      by simpa [s₄, L, L_dir] using hcx₃,
      by simpa [s₄, L, L_dir] using hcy₃,
      by dsimp [s₄, L, L_dir]; split_ifs <;> rfl,
      fun r h8 h9 h11 => by simp [s₄, hregs₃ r h8 h9, s₂, s₁, h11],
      fun arr ha1 ha2 => by simp [s₄, harrs₃ arr ha1 ha2, s₂, s₁, ha1, ha2]⟩
  · have hcond : (Expr.reg 6).eval w s₂ = some 1 := by
      simp [Expr.eval, checkWord, s₂, s₁, hr6, h1_w]
    rcases write4SeqCmd_exec a b p₀ p₁ p₂ p₃ eX0 eY0 eX1 eY1 eX2 eY2 eX3 eY3 (s := s₂)
        hw4 hmode_w h2h'5_w hp₀_w hp₁_w hp₂_w hp₃_w
        heX0 heY0 heX1 heY1 heX2 heY2 heX3 heY3
        (by simp [s₂, s₁, hr15]) (by simp [s₂, s₁, hr22])
        (by simp [s₂, s₁, hr18]) (by simp [s₂, s₁, hr19])
        (by simp [s₂, s₁, hr20]) (by simp [s₂, s₁, hr21])
        hcx₂ hcy₂ with
      ⟨s₃, t₃, hex₃, ht₃, hcx₃, hcy₃, hregs₃, harrs₃⟩
    let s₄ := s₃.setReg 11 4
    have hex₄ : Exec w (.assign 11 (.const 4)) s₃ s₄ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw4])
    refine ⟨s₄, _,
      .seq hex₁ (.seq hex₂ (.seq (.ite_true hcond (by omega) hex₃) hex₄)),
      by simp [Expr.cost]; omega,
      by simpa [s₄, L, L_dir] using hcx₃,
      by simpa [s₄, L, L_dir] using hcy₃,
      by dsimp [s₄, L, L_dir]; split_ifs <;> rfl,
      fun r h8 h9 h11 => by simp [s₄, hregs₃ r h8 h9, s₂, s₁, h11],
      fun arr ha1 ha2 => by simp [s₄, harrs₃ arr ha1 ha2, s₂, s₁, ha1, ha2]⟩

theorem ite_inner_exec {w : ℕ} {cond : Expr} (P : Prop) [Decidable P]
    {c₁ c₂ : Cmd} {s : State} {B₁ B₂ : ℕ} {L₁ L₂ : List (ℕ × ℕ)}
    (hcond : cond.eval w s = some (if P then 1 else 0))
    (h₁ : ∃ s' t, Exec w c₁ s s' t ∧ t ≤ B₁ ∧ InnerCoordsPost s L₁ s')
    (h₂ : ∃ s' t, Exec w c₂ s s' t ∧ t ≤ B₂ ∧ InnerCoordsPost s L₂ s') :
    ∃ s' t,
      Exec w (.ite cond c₁ c₂) s s' t ∧
      t ≤ cond.cost + 1 + max B₁ B₂ ∧
      InnerCoordsPost s (if P then L₁ else L₂) s' := by
  by_cases hP : P
  · rw [if_pos hP] at hcond ⊢
    rcases h₁ with ⟨s', t, hex, ht, hpost⟩
    exact ⟨s', _, .ite_true hcond (by omega) hex, by omega, hpost⟩
  · rw [if_neg hP] at hcond ⊢
    rcases h₂ with ⟨s', t, hex, ht, hpost⟩
    exact ⟨s', _, .ite_false hcond hex, by omega, hpost⟩

/-- Evaluate `natHoleInnerO Y0 c0 a b` (forward if `r_6 != 0`, reversed if `r_6 == 0`, rotated by
`rotV (h' + 2)` if `r_15 == 3`) into `(coordXArr, coordYArr)` from `a = (r_18, r_19)` and
`b = (r_20, r_21)`. -/
def loadHoleInnerOCmd : Cmd :=
  let rowEq := exprEq (.reg 19) (.reg 21)
  let condHoriz := exprAnd (.op .lt (.reg 19) (.reg 16)) (exprEq (.reg 20) (.reg 17))
  let condVert := exprEq (.reg 21) (.reg 16)
  let condLeft := Expr.op .lt (.reg 18) (.reg 17)
  .ite rowEq
    (.ite condHoriz
      (write4InnerCoordsCmd
        (.reg 20) (.reg 19)
        (.op .add (.reg 20) (.const 1)) (.reg 19)
        (.op .add (.reg 20) (.const 2)) (.reg 19)
        (.op .add (.reg 20) (.const 3)) (.reg 19))
      write0InnerCoordsCmd)
    (.ite condVert
      (.ite condLeft
        (write4InnerCoordsCmd
          (.reg 18) (.reg 21)
          (.op .add (.reg 18) (.const 1)) (.reg 21)
          (.op .add (.reg 18) (.const 1)) (.op .add (.reg 21) (.const 1))
          (.op .add (.reg 18) (.const 2)) (.op .add (.reg 21) (.const 1)))
        (write4InnerCoordsCmd
          (.op .add (.reg 18) (.const 4)) (.reg 21)
          (.op .add (.reg 18) (.const 3)) (.reg 21)
          (.op .add (.reg 18) (.const 3)) (.op .add (.reg 21) (.const 1))
          (.op .add (.reg 18) (.const 2)) (.op .add (.reg 21) (.const 1))))
      write0InnerCoordsCmd)

/-- Populate `(coordXArr, coordYArr)` with `innerOfCode h' code p q` and set `r_10 := 0` and
`r_11 := (innerOfCode h' code p q).length`, given `p = (r_18, r_19)` and `q = (r_20, r_21)`. -/
def loadInnerOfCodeCmd : Cmd :=
  .seq (.assign 10 (.const 0))
    (.ite (.op .lt (.reg 15) (.const 2))
      write0InnerCoordsCmd
      (.seq (.ite (exprEq (.reg 15) (.const 3))
          (.seq (rotVCmd (.reg 22) 18 19)
            (rotVCmd (.reg 22) 20 21))
          .skip)
        (.seq (.ite (.op .lt (.op .add (.reg 18) (.reg 19)) (.op .add (.reg 20) (.reg 21)))
            (.assign 6 (.const 1))
            (.seq (.assign 6 (.const 0))
              (.seq (.assign 8 (.reg 18))
                (.seq (.assign 9 (.reg 19))
                  (.seq (.assign 18 (.reg 20))
                    (.seq (.assign 19 (.reg 21))
                      (.seq (.assign 20 (.reg 8))
                        (.assign 21 (.reg 9)))))))))
          loadHoleInnerOCmd)))

theorem loadHoleInnerOCmd_exec {w h' : ℕ} (code : RealizationCode) (b_lt : Bool) (a b : ℕ × ℕ)
    {s : State}
    (hw4 : 4 < 2 ^ w)
    (hmode_w : code.mode < 2 ^ w)
    (hY0_w : code.Y0 < 2 ^ w)
    (hc0_w : code.c0 < 2 ^ w)
    (h2h'5_w : 2 * h' + 5 < 2 ^ w)
    (ha1_w : a.1 + 4 < 2 ^ w)
    (ha2_w : a.2 + 1 < 2 ^ w)
    (hb1_w : b.1 + 3 < 2 ^ w)
    (hb2_w : b.2 + 1 < 2 ^ w)
    (hr6 : s.regs 6 = if b_lt then 1 else 0)
    (hr15 : s.regs 15 = code.mode)
    (hr16 : s.regs 16 = code.Y0)
    (hr17 : s.regs 17 = code.c0)
    (hr22 : s.regs 22 = h')
    (hr18 : s.regs 18 = a.1)
    (hr19 : s.regs 19 = a.2)
    (hr20 : s.regs 20 = b.1)
    (hr21 : s.regs 21 = b.2) :
    let L0 := natHoleInnerO code.Y0 code.c0 a b
    let L_dir := if b_lt then L0 else L0.reverse
    let L := if code.mode = 3 then L_dir.map (GM13.rotV (h' + 2)) else L_dir
    ∃ s' t,
      Exec w loadHoleInnerOCmd s s' t ∧
      t ≤ 260 ∧
      InnerCoordsPost s L s' := by
  intro L0 L_dir L
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have ha1_0_w : a.1 < 2 ^ w := by omega
  have ha2_0_w : a.2 < 2 ^ w := by omega
  have hb1_0_w : b.1 < 2 ^ w := by omega
  have hb2_0_w : b.2 < 2 ^ w := by omega
  have he18 : EvalAB w a b (.reg 18) a.1 :=
    fun _ h18 _ _ _ => by simp [Expr.eval, checkWord, h18, ha1_0_w]
  have he18_1 : EvalAB w a b (.op .add (.reg 18) (.const 1)) (a.1 + 1) :=
    fun _ h18 _ _ _ => by
      have : a.1 + 1 < 2 ^ w := by omega
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, h18, ha1_0_w, h1_w, this]
  have he18_2 : EvalAB w a b (.op .add (.reg 18) (.const 2)) (a.1 + 2) :=
    fun _ h18 _ _ _ => by
      have : a.1 + 2 < 2 ^ w := by omega
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, h18, ha1_0_w, h2_w, this]
  have he18_3 : EvalAB w a b (.op .add (.reg 18) (.const 3)) (a.1 + 3) :=
    fun _ h18 _ _ _ => by
      have : a.1 + 3 < 2 ^ w := by omega
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, h18, ha1_0_w, h3_w, this]
  have he18_4 : EvalAB w a b (.op .add (.reg 18) (.const 4)) (a.1 + 4) :=
    fun _ h18 _ _ _ => by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, h18, ha1_0_w, hw4, ha1_w]
  have he19 : EvalAB w a b (.reg 19) a.2 :=
    fun _ _ h19 _ _ => by simp [Expr.eval, checkWord, h19, ha2_0_w]
  have he20 : EvalAB w a b (.reg 20) b.1 :=
    fun _ _ _ h20 _ => by simp [Expr.eval, checkWord, h20, hb1_0_w]
  have he20_1 : EvalAB w a b (.op .add (.reg 20) (.const 1)) (b.1 + 1) :=
    fun _ _ _ h20 _ => by
      have : b.1 + 1 < 2 ^ w := by omega
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, h20, hb1_0_w, h1_w, this]
  have he20_2 : EvalAB w a b (.op .add (.reg 20) (.const 2)) (b.1 + 2) :=
    fun _ _ _ h20 _ => by
      have : b.1 + 2 < 2 ^ w := by omega
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, h20, hb1_0_w, h2_w, this]
  have he20_3 : EvalAB w a b (.op .add (.reg 20) (.const 3)) (b.1 + 3) :=
    fun _ _ _ h20 _ => by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, h20, hb1_0_w, h3_w, hb1_w]
  have he21 : EvalAB w a b (.reg 21) b.2 :=
    fun _ _ _ _ h21 => by simp [Expr.eval, checkWord, h21, hb2_0_w]
  have he21_1 : EvalAB w a b (.op .add (.reg 21) (.const 1)) (b.2 + 1) :=
    fun _ _ _ _ h21 => by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, h21, hb2_0_w, h1_w, hb2_w]
  have hrow_eval : (exprEq (.reg 19) (.reg 21)).eval w s = some (if a.2 = b.2 then 1 else 0) :=
    eval_exprEq h1_w (he19 s hr18 hr19 hr20 hr21) (he21 s hr18 hr19 hr20 hr21)
  have hcondH_eval :
      (exprAnd (.op .lt (.reg 19) (.reg 16)) (exprEq (.reg 20) (.reg 17))).eval w s =
      some (if (a.2 < code.Y0 ∧ b.1 = code.c0) then 1 else 0) := by
    have h1 : (Expr.op .lt (.reg 19) (.reg 16)).eval w s =
        some (if decide (a.2 < code.Y0) then 1 else 0) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr19, hr16, ha2_0_w, hY0_w]
      split_ifs <;> simp [h1_w, show 0 < 2 ^ w by omega]
    have h2 : (exprEq (.reg 20) (.reg 17)).eval w s =
        some (if decide (b.1 = code.c0) then 1 else 0) := by
      simpa using eval_exprEq h1_w (he20 s hr18 hr19 hr20 hr21)
        (by simp [Expr.eval, checkWord, hr17, hc0_w])
    simpa [Bool.decide_and] using eval_exprAnd_bool h1_w h1 h2
  have hcondV_eval : (exprEq (.reg 21) (.reg 16)).eval w s =
      some (if b.2 = code.Y0 then 1 else 0) :=
    eval_exprEq h1_w (he21 s hr18 hr19 hr20 hr21) (by simp [Expr.eval, checkWord, hr16, hY0_w])
  have hcondL_eval : (Expr.op .lt (.reg 18) (.reg 17)).eval w s =
      some (if a.1 < code.c0 then 1 else 0) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr18, hr17, ha1_0_w, hc0_w]
    split_ifs <;> simp [h1_w, show 0 < 2 ^ w by omega]
  have hnil_eq : (if code.mode = 3 then (if b_lt then ([] : List (ℕ × ℕ)) else [].reverse).map
      (GM13.rotV (h' + 2)) else (if b_lt then [] else [].reverse)) = [] := by
    split_ifs <;> rfl
  have h0_exec :
      ∃ s' t, Exec w write0InnerCoordsCmd s s' t ∧ t ≤ 6 ∧
        InnerCoordsPost s
          (if code.mode = 3 then (if b_lt then ([] : List (ℕ × ℕ)) else [].reverse).map
            (GM13.rotV (h' + 2)) else (if b_lt then [] else [].reverse)) s' := by
    rw [hnil_eq]
    exact write0InnerCoordsCmd_exec h1_w
  unfold loadHoleInnerOCmd
  rcases ite_inner_exec (a.2 = b.2) hrow_eval
    (ite_inner_exec (a.2 < code.Y0 ∧ b.1 = code.c0) hcondH_eval
      (write4InnerCoordsCmd_exec b_lt a b (b.1, a.2) (b.1 + 1, a.2) (b.1 + 2, a.2) (b.1 + 3, a.2)
        (.reg 20) (.reg 19) (.op .add (.reg 20) (.const 1)) (.reg 19)
        (.op .add (.reg 20) (.const 2)) (.reg 19) (.op .add (.reg 20) (.const 3)) (.reg 19)
        hw4 hmode_w h2h'5_w (by omega) (by omega) (by omega) (by omega)
        he20 he19 he20_1 he19 he20_2 he19 he20_3 he19
        hr6 hr15 hr22 hr18 hr19 hr20 hr21)
      h0_exec)
    (ite_inner_exec (b.2 = code.Y0) hcondV_eval
      (ite_inner_exec (a.1 < code.c0) hcondL_eval
        (write4InnerCoordsCmd_exec b_lt a b (a.1, b.2) (a.1 + 1, b.2) (a.1 + 1, b.2 + 1) (a.1 + 2, b.2 + 1)
          (.reg 18) (.reg 21) (.op .add (.reg 18) (.const 1)) (.reg 21)
          (.op .add (.reg 18) (.const 1)) (.op .add (.reg 21) (.const 1))
          (.op .add (.reg 18) (.const 2)) (.op .add (.reg 21) (.const 1))
          hw4 hmode_w h2h'5_w (by omega) (by omega) (by omega) (by omega)
          he18 he21 he18_1 he21 he18_1 he21_1 he18_2 he21_1
          hr6 hr15 hr22 hr18 hr19 hr20 hr21)
        (write4InnerCoordsCmd_exec b_lt a b (a.1 + 4, b.2) (a.1 + 3, b.2) (a.1 + 3, b.2 + 1) (a.1 + 2, b.2 + 1)
          (.op .add (.reg 18) (.const 4)) (.reg 21) (.op .add (.reg 18) (.const 3)) (.reg 21)
          (.op .add (.reg 18) (.const 3)) (.op .add (.reg 21) (.const 1))
          (.op .add (.reg 18) (.const 2)) (.op .add (.reg 21) (.const 1))
          hw4 hmode_w h2h'5_w (by omega) (by omega) (by omega) (by omega)
          he18_4 he21 he18_3 he21 he18_3 he21_1 he18_2 he21_1
          hr6 hr15 hr22 hr18 hr19 hr20 hr21))
      h0_exec) with
    ⟨s', t_tree, hex_tree, ht_tree, hpost⟩
  have hL_eq :
      (if a.2 = b.2 then
        if a.2 < code.Y0 ∧ b.1 = code.c0 then
          if code.mode = 3 then
            (if b_lt then [(b.1, a.2), (b.1 + 1, a.2), (b.1 + 2, a.2), (b.1 + 3, a.2)]
             else [(b.1, a.2), (b.1 + 1, a.2), (b.1 + 2, a.2), (b.1 + 3, a.2)].reverse).map
              (GM13.rotV (h' + 2))
          else
            if b_lt then [(b.1, a.2), (b.1 + 1, a.2), (b.1 + 2, a.2), (b.1 + 3, a.2)]
            else [(b.1, a.2), (b.1 + 1, a.2), (b.1 + 2, a.2), (b.1 + 3, a.2)].reverse
        else
          if code.mode = 3 then
            (if b_lt then ([] : List (ℕ × ℕ)) else [].reverse).map (GM13.rotV (h' + 2))
          else
            if b_lt then [] else [].reverse
      else if b.2 = code.Y0 then
        if a.1 < code.c0 then
          if code.mode = 3 then
            (if b_lt then [(a.1, b.2), (a.1 + 1, b.2), (a.1 + 1, b.2 + 1), (a.1 + 2, b.2 + 1)]
             else [(a.1, b.2), (a.1 + 1, b.2), (a.1 + 1, b.2 + 1), (a.1 + 2, b.2 + 1)].reverse).map
              (GM13.rotV (h' + 2))
          else
            if b_lt then [(a.1, b.2), (a.1 + 1, b.2), (a.1 + 1, b.2 + 1), (a.1 + 2, b.2 + 1)]
            else [(a.1, b.2), (a.1 + 1, b.2), (a.1 + 1, b.2 + 1), (a.1 + 2, b.2 + 1)].reverse
        else
          if code.mode = 3 then
            (if b_lt then [(a.1 + 4, b.2), (a.1 + 3, b.2), (a.1 + 3, b.2 + 1), (a.1 + 2, b.2 + 1)]
             else [(a.1 + 4, b.2), (a.1 + 3, b.2), (a.1 + 3, b.2 + 1), (a.1 + 2, b.2 + 1)].reverse).map
              (GM13.rotV (h' + 2))
          else
            if b_lt then [(a.1 + 4, b.2), (a.1 + 3, b.2), (a.1 + 3, b.2 + 1), (a.1 + 2, b.2 + 1)]
            else [(a.1 + 4, b.2), (a.1 + 3, b.2), (a.1 + 3, b.2 + 1), (a.1 + 2, b.2 + 1)].reverse
      else
        if code.mode = 3 then
          (if b_lt then ([] : List (ℕ × ℕ)) else [].reverse).map (GM13.rotV (h' + 2))
        else
          if b_lt then [] else [].reverse) = L := by
    dsimp [L, L_dir, L0, natHoleInnerO]
    split_ifs <;> rfl
  rw [hL_eq] at hpost
  refine ⟨s', t_tree, hex_tree,
    by simp [exprAnd, exprEq, Expr.cost] at ht_tree; omega,
    hpost⟩

theorem loadInnerOfCodeCmd_exec {w h' : ℕ} (code : RealizationCode) (p q : ℕ × ℕ)
    {s : State}
    (hw4 : 4 < 2 ^ w)
    (hmode_le : code.mode ≤ 3)
    (hY0_w : code.Y0 < 2 ^ w)
    (hc0_w : code.c0 < 2 ^ w)
    (h3h'9_w : 3 * h' + 9 < 2 ^ w)
    (hp1_le : p.1 ≤ 2 * h' + 1) (hp2_le : p.2 ≤ h')
    (hq1_le : q.1 ≤ 2 * h' + 1) (hq2_le : q.2 ≤ h')
    (hr15 : s.regs 15 = code.mode)
    (hr16 : s.regs 16 = code.Y0)
    (hr17 : s.regs 17 = code.c0)
    (hr22 : s.regs 22 = h')
    (hr18 : s.regs 18 = p.1)
    (hr19 : s.regs 19 = p.2)
    (hr20 : s.regs 20 = q.1)
    (hr21 : s.regs 21 = q.2) :
    ∃ s' t,
      Exec w loadInnerOfCodeCmd s s' t ∧
      t ≤ 340 ∧
      s'.arrs coordXArr = (innerOfCode h' code p q).map Prod.fst ∧
      s'.arrs coordYArr = (innerOfCode h' code p q).map Prod.snd ∧
      s'.regs 10 = 0 ∧
      s'.regs 11 = (innerOfCode h' code p q).length ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ coordXArr → a ≠ coordYArr → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have hmode_w : code.mode < 2 ^ w := by omega
  have hh'_w : h' < 2 ^ w := by omega
  let s₁ := s.setReg 10 0
  have hex₁ : Exec w (.assign 10 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  by_cases hm_lt2 : code.mode < 2
  · have hcond_lt2 : (Expr.op .lt (.reg 15) (.const 2)).eval w s₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hr15, hmode_w, h2_w, hm_lt2, h1_w]
    rcases write0InnerCoordsCmd_exec (s := s₁) h1_w with
      ⟨s₂, t₂, hex₂, ht₂, hcx₂, hcy₂, hr11_2, hregs₂, harrs₂⟩
    have hinner_nil : innerOfCode h' code p q = [] := by
      rcases (show code.mode = 0 ∨ code.mode = 1 by omega) with hm | hm <;>
        simp [innerOfCode, hm]
    rw [hinner_nil]
    refine ⟨s₂, _, .seq hex₁ (.ite_true hcond_lt2 (by omega) hex₂),
      by simp [Expr.cost]; omega, hcx₂, hcy₂,
      by rw [hregs₂ 10 (by decide) (by decide) (by decide)]; simp [s₁],
      hr11_2,
      fun r _ h8 h9 h10 h11 _ _ _ _ => by
        rw [hregs₂ r h8 h9 h11]; simp [s₁, h10],
      harrs₂⟩
  · have hcond_lt2 : (Expr.op .lt (.reg 15) (.const 2)).eval w s₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hr15, hmode_w, h2_w, hm_lt2, h0_w]
    let p' := if code.mode = 3 then GM13.rotV h' p else p
    let q' := if code.mode = 3 then GM13.rotV h' q else q
    have he15 : (Expr.reg 15).eval w s₁ = some code.mode := by
      simp [Expr.eval, checkWord, s₁, hr15, hmode_w]
    have hcond3 : (exprEq (.reg 15) (.const 3)).eval w s₁ = some (if code.mode = 3 then 1 else 0) :=
      eval_exprEq h1_w he15 (by simp [Expr.eval, checkWord, h3_w])
    have hrot_pq :
        ∃ s₂ t_rot,
          Exec w (.ite (exprEq (.reg 15) (.const 3))
            (.seq (rotVCmd (.reg 22) 18 19) (rotVCmd (.reg 22) 20 21)) .skip) s₁ s₂ t_rot ∧
          t_rot ≤ 35 ∧
          s₂.regs 18 = p'.1 ∧ s₂.regs 19 = p'.2 ∧
          s₂.regs 20 = q'.1 ∧ s₂.regs 21 = q'.2 ∧
          (∀ r : Reg, r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → s₂.regs r = s₁.regs r) ∧
          s₂.arrs = s.arrs := by
      by_cases hm3 : code.mode = 3
      · rw [if_pos hm3] at hcond3
        rcases rotVCmd_exec (h := h') (eH := .reg 22) 18 19 (by decide) p (s := s₁)
            h2_w (by omega) (by omega) (by omega)
            (fun s' hs' => by simp [Expr.eval, checkWord, hs' 22 (by decide), s₁, hr22, hh'_w])
            (by simp [s₁, hr18]) (by simp [s₁, hr19]) with
          ⟨s₁a, t₁a, hex₁a, ht₁a, h18a, h19a, hregs₁a, harrs₁a⟩
        rcases rotVCmd_exec (h := h') (eH := .reg 22) 20 21 (by decide) q (s := s₁a)
            h2_w (by omega) (by omega) (by omega)
            (fun s' hs' => by
              have hr22' : s'.regs 22 = h' := by
                rw [hs' 22 (by decide), hregs₁a 22 (by decide) (by decide)]
                simp [s₁, hr22]
              simp [Expr.eval, checkWord, hr22', hh'_w])
            (by rw [hregs₁a 20 (by decide) (by decide)]; simp [s₁, hr20])
            (by rw [hregs₁a 21 (by decide) (by decide)]; simp [s₁, hr21]) with
          ⟨s₂, t₁b, hex₁b, ht₁b, h20b, h21b, hregs₂, harrs₂⟩
        refine ⟨s₂, _, .ite_true hcond3 (by omega) (.seq hex₁a hex₁b),
          by simp [exprEq, Expr.cost] at ht₁a ht₁b ⊢; omega,
          by rw [hregs₂ 18 (by decide) (by decide)]; simpa [p', hm3] using h18a,
          by rw [hregs₂ 19 (by decide) (by decide)]; simpa [p', hm3] using h19a,
          by simpa [q', hm3] using h20b,
          by simpa [q', hm3] using h21b,
          fun r h18 h19 h20 h21 => by rw [hregs₂ r h20 h21, hregs₁a r h18 h19],
          harrs₂.trans harrs₁a⟩
      · rw [if_neg hm3] at hcond3
        refine ⟨s₁, _, .ite_false hcond3 (.skip s₁),
          by simp [exprEq, Expr.cost],
          by simp [s₁, p', hm3, hr18],
          by simp [s₁, p', hm3, hr19],
          by simp [s₁, q', hm3, hr20],
          by simp [s₁, q', hm3, hr21],
          fun _ _ _ _ _ => rfl, rfl⟩
    rcases hrot_pq with ⟨s₂, t_rot, hex_rot, ht_rot, hp'1, hp'2, hq'1, hq'2, hregs₂, harrs₂⟩
    have hp'1_le : p'.1 ≤ 2 * h' + 1 := by dsimp [p', GM13.rotV]; split_ifs <;> omega
    have hp'2_le : p'.2 ≤ h' := by dsimp [p', GM13.rotV]; split_ifs <;> omega
    have hq'1_le : q'.1 ≤ 2 * h' + 1 := by dsimp [q', GM13.rotV]; split_ifs <;> omega
    have hq'2_le : q'.2 ≤ h' := by dsimp [q', GM13.rotV]; split_ifs <;> omega
    have hp'1_w : p'.1 < 2 ^ w := by omega
    have hp'2_w : p'.2 < 2 ^ w := by omega
    have hq'1_w : q'.1 < 2 ^ w := by omega
    have hq'2_w : q'.2 < 2 ^ w := by omega
    have hpsum_w : p'.1 + p'.2 < 2 ^ w := by omega
    have hqsum_w : q'.1 + q'.2 < 2 ^ w := by omega
    let b_lt : Bool := decide (p'.1 + p'.2 < q'.1 + q'.2)
    let a := if p'.1 + p'.2 < q'.1 + q'.2 then p' else q'
    let b := if p'.1 + p'.2 < q'.1 + q'.2 then q' else p'
    have hswap :
        ∃ s₃ t_sw,
          Exec w (.ite (.op .lt (.op .add (.reg 18) (.reg 19)) (.op .add (.reg 20) (.reg 21)))
            (.assign 6 (.const 1))
            (.seq (.assign 6 (.const 0))
              (.seq (.assign 8 (.reg 18))
                (.seq (.assign 9 (.reg 19))
                  (.seq (.assign 18 (.reg 20))
                    (.seq (.assign 19 (.reg 21))
                      (.seq (.assign 20 (.reg 8))
                        (.assign 21 (.reg 9))))))))) s₂ s₃ t_sw ∧
          t_sw ≤ 25 ∧
          s₃.regs 6 = (if b_lt then 1 else 0) ∧
          s₃.regs 18 = a.1 ∧ s₃.regs 19 = a.2 ∧
          s₃.regs 20 = b.1 ∧ s₃.regs 21 = b.2 ∧
          (∀ r : Reg, r ≠ 6 → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 →
            s₃.regs r = s₂.regs r) ∧
          s₃.arrs = s₂.arrs := by
      by_cases hlt : p'.1 + p'.2 < q'.1 + q'.2
      · have hcond_lt :
            (Expr.op .lt (.op .add (.reg 18) (.reg 19)) (.op .add (.reg 20) (.reg 21))).eval w s₂ =
              some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hp'1, hp'2, hq'1, hq'2,
            hp'1_w, hp'2_w, hq'1_w, hq'2_w, hpsum_w, hqsum_w, hlt, h1_w]
        let s₃ := s₂.setReg 6 1
        have hex_t : Exec w (.assign 6 (.const 1)) s₂ s₃ 2 :=
          .assign (by simp [Expr.eval, checkWord, h1_w])
        refine ⟨s₃, _, .ite_true hcond_lt (by omega) hex_t, by simp [Expr.cost],
          by simp [s₃, b_lt, hlt],
          by simp [s₃, a, hlt, hp'1], by simp [s₃, a, hlt, hp'2],
          by simp [s₃, b, hlt, hq'1], by simp [s₃, b, hlt, hq'2],
          fun r h6 _ _ _ _ _ _ => by simp [s₃, h6], rfl⟩
      · have hcond_lt :
            (Expr.op .lt (.op .add (.reg 18) (.reg 19)) (.op .add (.reg 20) (.reg 21))).eval w s₂ =
              some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hp'1, hp'2, hq'1, hq'2,
            hp'1_w, hp'2_w, hq'1_w, hq'2_w, hpsum_w, hqsum_w, hlt, h0_w]
        let s₃a := s₂.setReg 6 0
        have hex_a : Exec w (.assign 6 (.const 0)) s₂ s₃a 2 :=
          .assign (by simp [Expr.eval, checkWord, h0_w])
        let s₃b := s₃a.setReg 8 p'.1
        have hex_b : Exec w (.assign 8 (.reg 18)) s₃a s₃b 2 :=
          .assign (by simp [Expr.eval, checkWord, s₃a, hp'1, hp'1_w])
        let s₃c := s₃b.setReg 9 p'.2
        have hex_c : Exec w (.assign 9 (.reg 19)) s₃b s₃c 2 :=
          .assign (by simp [Expr.eval, checkWord, s₃b, s₃a, hp'2, hp'2_w])
        let s₃d := s₃c.setReg 18 q'.1
        have hex_d : Exec w (.assign 18 (.reg 20)) s₃c s₃d 2 :=
          .assign (by simp [Expr.eval, checkWord, s₃c, s₃b, s₃a, hq'1, hq'1_w])
        let s₃e := s₃d.setReg 19 q'.2
        have hex_e : Exec w (.assign 19 (.reg 21)) s₃d s₃e 2 :=
          .assign (by simp [Expr.eval, checkWord, s₃d, s₃c, s₃b, s₃a, hq'2, hq'2_w])
        let s₃f := s₃e.setReg 20 p'.1
        have hex_f : Exec w (.assign 20 (.reg 8)) s₃e s₃f 2 :=
          .assign (by simp [Expr.eval, checkWord, s₃e, s₃d, s₃c, s₃b, hp'1_w])
        let s₃ := s₃f.setReg 21 p'.2
        have hex_g : Exec w (.assign 21 (.reg 9)) s₃f s₃ 2 :=
          .assign (by simp [Expr.eval, checkWord, s₃f, s₃e, s₃d, s₃c, hp'2_w])
        refine ⟨s₃, _,
          .ite_false hcond_lt (.seq hex_a (.seq hex_b (.seq hex_c (.seq hex_d (.seq hex_e (.seq hex_f hex_g)))))),
          by simp [Expr.cost],
          by simp [s₃, s₃f, s₃e, s₃d, s₃c, s₃b, s₃a, b_lt, hlt],
          by simp [s₃, s₃f, s₃e, s₃d, a, hlt],
          by simp [s₃, s₃f, s₃e, a, hlt],
          by simp [s₃, s₃f, b, hlt],
          by simp [s₃, b, hlt],
          fun r h6 h8 h9 h18 h19 h20 h21 => by
            simp [s₃, s₃f, s₃e, s₃d, s₃c, s₃b, s₃a, h6, h8, h9, h18, h19, h20, h21],
          rfl⟩
    rcases hswap with ⟨s₃, t_sw, hex_sw, ht_sw, hr6_3, ha1_3, ha2_3, hb1_3, hb2_3, hregs₃, harrs₃⟩
    have ha1_le : a.1 ≤ 2 * h' + 1 := by dsimp [a]; split_ifs <;> omega
    have ha2_le : a.2 ≤ h' := by dsimp [a]; split_ifs <;> omega
    have hb1_le : b.1 ≤ 2 * h' + 1 := by dsimp [b]; split_ifs <;> omega
    have hb2_le : b.2 ≤ h' := by dsimp [b]; split_ifs <;> omega
    rcases loadHoleInnerOCmd_exec (h' := h') code b_lt a b (s := s₃)
        hw4 hmode_w hY0_w hc0_w (by omega) (by omega) (by omega) (by omega) (by omega)
        hr6_3
        (by rw [hregs₃ 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hregs₂ 15 (by decide) (by decide) (by decide) (by decide)]; simp [s₁, hr15])
        (by rw [hregs₃ 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hregs₂ 16 (by decide) (by decide) (by decide) (by decide)]; simp [s₁, hr16])
        (by rw [hregs₃ 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hregs₂ 17 (by decide) (by decide) (by decide) (by decide)]; simp [s₁, hr17])
        (by rw [hregs₃ 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hregs₂ 22 (by decide) (by decide) (by decide) (by decide)]; simp [s₁, hr22])
        ha1_3 ha2_3 hb1_3 hb2_3 with
      ⟨s₄, t₄, hex₄, ht₄, hcx₄, hcy₄, hr11_4, hregs₄, harrs₄⟩
    have hdir_eq :
        (if b_lt then natHoleInnerO code.Y0 code.c0 a b
         else (natHoleInnerO code.Y0 code.c0 a b).reverse) =
        natHoleInner code.Y0 code.c0 p' q' := by
      by_cases hlt : p'.1 + p'.2 < q'.1 + q'.2 <;>
        simp [natHoleInner, b_lt, a, b, hlt]
    have hinner_eq :
        (if code.mode = 3 then
          (if b_lt then natHoleInnerO code.Y0 code.c0 a b
           else (natHoleInnerO code.Y0 code.c0 a b).reverse).map (GM13.rotV (h' + 2))
        else
          if b_lt then natHoleInnerO code.Y0 code.c0 a b
          else (natHoleInnerO code.Y0 code.c0 a b).reverse) =
        innerOfCode h' code p q := by
      rw [hdir_eq]
      rcases (show code.mode = 2 ∨ code.mode = 3 by omega) with hm | hm <;>
        simp [innerOfCode, p', q', hm]
    rw [hinner_eq] at hcx₄ hcy₄ hr11_4
    refine ⟨s₄, _,
      .seq hex₁ (.ite_false hcond_lt2 (.seq hex_rot (.seq hex_sw hex₄))),
      by simp [Expr.cost]; omega, hcx₄, hcy₄,
      by
        rw [hregs₄ 10 (by decide) (by decide) (by decide),
          hregs₃ 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hregs₂ 10 (by decide) (by decide) (by decide) (by decide)]
        simp [s₁],
      hr11_4,
      fun r h6 h8 h9 h10 h11 h18 h19 h20 h21 => by
        rw [hregs₄ r h8 h9 h11, hregs₃ r h6 h8 h9 h18 h19 h20 h21,
          hregs₂ r h18 h19 h20 h21]
        simp [s₁, h10],
      fun arr ha1 ha2 => by
        rw [harrs₄ arr ha1 ha2, harrs₃, harrs₂]⟩

end GraphMinor.Compute
