module

public import GraphMinor.Compute.Algorithm74Scan

/-!
# Terminal Routing on the Word RAM for Graph Minors XIII, (7.4)

This file implements Section 4 of the height-independent Word RAM program for Graph Minors XIII,
(7.4): computing the terminal coarse cells `termGridCell`, choosing the box margin `B`, computing
the perimeter terminal info `perimTermInfo` and color permutation `colorPerm`, sorting the
terminals by `termSortKey` via insertion sort, and computing the greedy safe columns `safeCol` in
$O(1)$ time (for fixed `p`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical
open scoped BigOperators

set_option linter.deprecated false

attribute [local irreducible] elemWallCoords elemWallNumVerts elemWallEdges coordOf alg74LiftRadius

/-- Compatibility alias for reading register `r` in state `s`. -/
abbrev State.readReg (s : State) (r : Reg) : ℕ := s.regs r

/-- Compatibility alias for writing value `v` to register `r` in state `s`. -/
abbrev State.writeReg (s : State) (r : Reg) (v : ℕ) : State := s.setReg r v

/-- Compatibility alias for reading array `a` in state `s`. -/
abbrev State.readArr (s : State) (a : Arr) : List ℕ := s.arrs a

/-- Compatibility alias for the array map of state `s`. -/
abbrev State.arr (s : State) : Arr → List ℕ := s.arrs

theorem State.readReg_writeReg_self (s : State) (r : Reg) (v : ℕ) :
    (s.writeReg r v).readReg r = v := by
  simp [State.readReg, State.writeReg]

theorem State.readReg_writeReg_ne (s : State) {r r' : Reg} (hne : r' ≠ r) (v : ℕ) :
    (s.writeReg r v).readReg r' = s.readReg r' := by
  simp [State.readReg, State.writeReg, hne]

theorem eval_lt_two_pow {w : ℕ} {s : State} {e : Expr} {v : ℕ}
    (h : e.eval w s = some v) : v < 2 ^ w :=
  Expr.eval_lt h

theorem eval_reg {w : ℕ} {s : State} {r : Reg} {v : ℕ}
    (h : s.readReg r = v) (hlt : v < 2 ^ w) :
    (Expr.reg r).eval w s = some v := by
  simp only [Expr.eval, checkWord_eq_some]
  have hr : s.regs r = v := h
  exact ⟨by omega, hr⟩

theorem eval_read {w : ℕ} {s : State} {a : Arr} {idx : Expr} {i v : ℕ}
    (hidx : idx.eval w s = some i)
    (hb : i < (s.readArr a).length)
    (hval : (s.readArr a)[i]'hb = v)
    (hlt : v < 2 ^ w) :
    (Expr.read a idx).eval w s = some v := by
  change i < (s.arrs a).length at hb
  simp only [Expr.eval, hidx, hb, ↓reduceDIte, checkWord_eq_some]
  have hv : (s.arrs a)[i]'hb = v := hval
  exact ⟨by omega, hv⟩

theorem eval_op {w : ℕ} {s : State} {op : BinOp} {e₁ e₂ : Expr} {v₁ v₂ v : ℕ}
    (h₁ : e₁.eval w s = some v₁)
    (h₂ : e₂.eval w s = some v₂)
    (hop : op.eval w v₁ v₂ = some v) :
    (Expr.op op e₁ e₂).eval w s = some v := by
  simp [Expr.eval, h₁, h₂, hop]

/-- Syntactic upper bound on the execution time of a loop-free, allocation-free command. -/
def Cmd.maxTime : Cmd → ℕ
  | .skip => 1
  | .assign _ e => e.cost + 1
  | .write _ idx val => idx.cost + val.cost + 1
  | .alloc _ len => len.cost
  | .seq c₁ c₂ => c₁.maxTime + c₂.maxTime
  | .ite cond c₁ c₂ => cond.cost + max c₁.maxTime c₂.maxTime
  | .while cond _ => cond.cost

/-- Predicate that a command contains no `.while` or `.alloc` subcommands. -/
def Cmd.IsLoopAllocFree : Cmd → Prop
  | .skip => True
  | .assign _ _ => True
  | .write _ _ _ => True
  | .alloc _ _ => False
  | .seq c₁ c₂ => c₁.IsLoopAllocFree ∧ c₂.IsLoopAllocFree
  | .ite _ c₁ c₂ => c₁.IsLoopAllocFree ∧ c₂.IsLoopAllocFree
  | .while _ _ => False

theorem Exec.time_le_maxTime {w : ℕ} {c : Cmd} {s s' : State} {t : ℕ}
    (h : Exec w c s s' t) (hfree : c.IsLoopAllocFree) : t ≤ c.maxTime := by
  induction h with
  | skip => simp [Cmd.maxTime]
  | assign => simp [Cmd.maxTime]
  | write => simp [Cmd.maxTime]
  | alloc => exact False.elim hfree
  | seq _ _ ih₁ ih₂ =>
    rcases hfree with ⟨hf₁, hf₂⟩
    simp only [Cmd.maxTime]
    have := ih₁ hf₁
    have := ih₂ hf₂
    omega
  | ite_true _ _ _ ih =>
    rcases hfree with ⟨hf₁, _⟩
    simp only [Cmd.maxTime]
    have := ih hf₁
    omega
  | ite_false _ _ ih =>
    rcases hfree with ⟨_, hf₂⟩
    simp only [Cmd.maxTime]
    have := ih hf₂
    omega
  | while_false => exact False.elim hfree
  | while_true => exact False.elim hfree

/-! ### Section 4: Word RAM Program, Terminal Routing (`routeTerminalsCmd`) -/

attribute [local simp] checkWord_of_lt

/-- Number of path endpoints `m = 2 * |E(K_p)|`. -/
def alg74NumTerms (p : ℕ) : ℕ := 2 * (completeGraphEdges p).length

/-- Coarse grid cell `termGridCell x.W (alg74TermVert x a)` of terminal `a`. -/
abbrev alg74Term {p r : ℕ} (x : Alg74Input p r) (a : Fin (alg74NumTerms p)) : ℕ × ℕ :=
  termGridCell x.W (alg74TermVert x a)

theorem alg74Term_bounds {p r : ℕ} (x : Alg74Input p r) (hh1 : 1 ≤ x.h)
    (a : Fin (alg74NumTerms p)) :
    1 ≤ (alg74Term x a).1 ∧ (alg74Term x a).1 ≤ x.h ∧ (alg74Term x a).2 ≤ x.h :=
  termGridCell_bounds hh1 (alg74TermVert_mem_vertexFinset x a)

/-- Register holding `(alg74TermVert x a).1` (`20 + a`). -/
def regTermVert (a : ℕ) : Reg := 20 + a

/-- Register holding `(termGridCell x.W (alg74TermVert x a)).1` (`20 + m + 2 * a`). -/
def regTermC (p a : ℕ) : Reg := 20 + alg74NumTerms p + 2 * a

/-- Register holding `(termGridCell x.W (alg74TermVert x a)).2` (`20 + m + 2 * a + 1`). -/
def regTermY (p a : ℕ) : Reg := 20 + alg74NumTerms p + 2 * a + 1

/-- Register holding `(colorPerm ... g).1` for color `g < p` (`20 + 3 * m + g`). -/
def regPermColor (p g : ℕ) : Reg := 20 + 3 * alg74NumTerms p + g

/-- Base register for the sorted terminal table (`20 + 3 * m + p`). -/
def regSortBase (p : ℕ) : Reg := 20 + 3 * alg74NumTerms p + p

/-- Register holding `termSortKey` of the `j`-th sorted terminal (`regSortBase p + 4 * j`). -/
def regSortKey (p j : ℕ) : Reg := regSortBase p + 4 * j

/-- Register holding coarse column `c` of the `j`-th sorted terminal (`regSortBase p + 4 * j + 1`). -/
def regSortC (p j : ℕ) : Reg := regSortBase p + 4 * j + 1

/-- Register holding row `y` of the `j`-th sorted terminal (`regSortBase p + 4 * j + 2`). -/
def regSortY (p j : ℕ) : Reg := regSortBase p + 4 * j + 2

/-- Register holding permuted color `g` of the `j`-th sorted terminal (`regSortBase p + 4 * j + 3`). -/
def regSortG (p j : ℕ) : Reg := regSortBase p + 4 * j + 3

/-- Register holding `safeCol` of the `j`-th sorted terminal (`regSortBase p + 4 * m + j`). -/
def regSafeC (p j : ℕ) : Reg := regSortBase p + 4 * alg74NumTerms p + j

/-- Box margin constant `B₂(p) = m * (4p + 2) + 2p + 3`. -/
def alg74BoxMarginConst (p : ℕ) : ℕ :=
  alg74NumTerms p * (4 * p + 2) + 2 * p + 3

theorem alg74TermVert_val_eq_reg {p r : ℕ} (x : Alg74Input p r) (s : State)
    (hterm_edges : ∀ e : Fin (completeGraphEdges p).length,
      s.regs (20 + 2 * e.1) = (alg74TermVert x (edgeStartTerm e)).1 ∧
      s.regs (20 + 2 * e.1 + 1) = (alg74TermVert x (edgeEndTerm e)).1)
    (a : Fin (alg74NumTerms p)) :
    s.readReg (regTermVert a.1) = (alg74TermVert x a).1 := by
  let e : Fin (completeGraphEdges p).length :=
    ⟨a.1 / 2, by have ha := a.2; dsimp [alg74NumTerms] at ha; omega⟩
  have he := hterm_edges e
  by_cases hmod : a.1 % 2 = 0
  · have ha_eq : a = edgeStartTerm e := by
      apply Fin.ext
      dsimp [edgeStartTerm, e]
      omega
    have hreg_eq : regTermVert a.1 = 20 + 2 * e.1 := by
      dsimp [regTermVert, Reg, e]
      omega
    rw [State.readReg, hreg_eq, ha_eq, he.1]
  · have ha_eq : a = edgeEndTerm e := by
      apply Fin.ext
      dsimp [edgeEndTerm, e]
      omega
    have hreg_eq : regTermVert a.1 = 20 + 2 * e.1 + 1 := by
      dsimp [regTermVert, Reg, e]
      omega
    rw [State.readReg, hreg_eq, ha_eq, he.2]

/-! #### Sub-step 4a: Computing Terminal Coarse Cells (`computeTermCellsCmd`) -/

/-- Compute `(regTermC p a, regTermY p a) = termGridCell x.W (alg74TermVert x a)` for terminal `a`,
using `r_3 = x.h`, `r_12 = elemWallNumVerts x.h`, `r_14 = 2 * x.h + 2`, `locArr` (`Arr 2`),
`edgeU1Arr` (`Arr 3`), and scratch registers `r_6 .. r_9`. -/
def computeOneTermCellCmd (p a : ℕ) : Cmd :=
  .seq (.assign 6 (.read locArr (.reg (regTermVert a))))
  (.seq
    (.ite (.op .lt (.reg 6) (.reg 12))
      (.assign 7 (.reg 6))
      (.seq (.assign 7 (.op .sub (.reg 6) (.reg 12)))
        (.assign 7 (.read edgeU1Arr (.reg 7)))))
  (.seq (.assign 7 (.op .add (.reg 7) (.const 1)))
  (.seq (.assign 8 (.op .mod (.reg 7) (.reg 14)))
  (.seq (.assign 9 (.op .div (.reg 7) (.reg 14)))
  (.seq (.assign (regTermY p a) (.reg 9))
  (.seq (.assign 8 (.op .div (.op .add (.reg 8) (.const 1)) (.const 2)))
  (.seq
    (.ite (.op .lt (.reg 8) (.const 1))
      (.assign 8 (.const 1))
      .skip)
    (.ite (.op .lt (.reg 3) (.reg 8))
      (.assign (regTermC p a) (.reg 3))
      (.assign (regTermC p a) (.reg 8))))))))))

theorem computeOneTermCellCmd_free (p a : ℕ) :
    (computeOneTermCellCmd p a).IsLoopAllocFree := by
  dsimp [computeOneTermCellCmd, Cmd.IsLoopAllocFree]
  trivial

theorem computeOneTermCellCmd_exec {w p r : ℕ} (x : Alg74Input p r)
    (hh1 : 1 ≤ x.h)
    (hw_n : x.n < 2 ^ w)
    (hw_h : 2 * x.h + 2 < 2 ^ w)
    (hw_wall : elemWallNumVerts x.h + (elemWallEdges x.h).length < 2 ^ w)
    (s : State)
    (hr3 : s.readReg 3 = x.h)
    (hr12 : s.readReg 12 = elemWallNumVerts x.h)
    (hr14 : s.readReg 14 = 2 * x.h + 2)
    (harr2_len : (s.readArr locArr).length = x.n)
    (harr2 : ∀ v ∈ x.W.vertexFinset,
      (s.readArr locArr)[v.1]'(by rw [harr2_len]; exact v.2) = termLocCode x.W v)
    (harr3_len : (s.readArr edgeU1Arr).length = (elemWallEdges x.h).length)
    (harr3 : ∀ k : Fin (elemWallEdges x.h).length,
      (s.readArr edgeU1Arr)[k.1]'(by rw [harr3_len]; exact k.2) =
        ((elemWallEdges x.h)[k.1]'k.2).1.1)
    (a : Fin (alg74NumTerms p))
    (hreg_a : s.readReg (regTermVert a.1) = (alg74TermVert x a).1) :
    ∃ s' t, Exec w (computeOneTermCellCmd p a.1) s s' t ∧
      s'.arr = s.arr ∧
      s'.readReg (regTermC p a.1) = (alg74Term x a).1 ∧
      s'.readReg (regTermY p a.1) = (alg74Term x a).2 ∧
      (∀ reg : Reg, reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 9 →
        reg ≠ regTermC p a.1 → reg ≠ regTermY p a.1 →
        s'.readReg reg = s.readReg reg) := by
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  let v := alg74TermVert x a
  have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hw_n
  have hv_mem : v ∈ x.W.vertexFinset := alg74TermVert_mem_vertexFinset x a
  have hloc_lt : termLocCode x.W v < elemWallNumVerts x.h + (elemWallEdges x.h).length :=
    termLocCode_lt_of_mem_vertexFinset x.hW_valid.2.2 hv_mem
  have hloc_w : termLocCode x.W v < 2 ^ w := by omega
  have h1 : Exec w (.assign 6 (.read locArr (.reg (regTermVert a.1)))) s
      (s.writeReg 6 (termLocCode x.W v))
      ((Expr.read locArr (.reg (regTermVert a.1))).cost + 1) := by
    have hev : (Expr.read locArr (.reg (regTermVert a.1))).eval w s =
        some (termLocCode x.W v) :=
      eval_read (eval_reg hreg_a hv_w) (by rw [harr2_len]; exact v.2) (harr2 v hv_mem) hloc_w
    exact Exec.assign hev
  let s₁ := s.writeReg 6 (termLocCode x.W v)
  have hs₁_6 : s₁.readReg 6 = termLocCode x.W v := State.readReg_writeReg_self s 6 _
  have hs₁_12 : s₁.readReg 12 = elemWallNumVerts x.h := by
    rw [State.readReg_writeReg_ne s (by decide), hr12]
  let u_rep := repVertOfLoc x.h (termLocCode x.W v) hloc_lt
  have hbranch2 : ∃ s₂ t₂,
      Exec w
        (.ite (.op .lt (.reg 6) (.reg 12))
          (.assign 7 (.reg 6))
          (.seq (.assign 7 (.op .sub (.reg 6) (.reg 12)))
            (.assign 7 (.read edgeU1Arr (.reg 7)))))
        s₁ s₂ t₂ ∧
      s₂.arr = s₁.arr ∧
      s₂.readReg 7 = u_rep.1 ∧
      (∀ reg : Reg, reg ≠ 7 → s₂.readReg reg = s₁.readReg reg) := by
    have h12_w : elemWallNumVerts x.h < 2 ^ w := by omega
    by_cases hlt : termLocCode x.W v < elemWallNumVerts x.h
    · have hu_val : u_rep.1 = termLocCode x.W v := by
        dsimp [u_rep, repVertOfLoc]
        simp [hlt]
      have hcond : (Expr.op .lt (.reg 6) (.reg 12)).eval w s₁ = some 1 := by
        simp [Expr.eval, State.readReg] at hs₁_6 hs₁_12 ⊢
        simp [hs₁_6, hs₁_12, hloc_w, h12_w, BinOp.eval, BinOp.raw, hlt, hw1]
      have htr : Exec w (.assign 7 (.reg 6)) s₁ (s₁.writeReg 7 (termLocCode x.W v))
          ((Expr.reg 6).cost + 1) :=
        Exec.assign (eval_reg hs₁_6 hloc_w)
      refine ⟨s₁.writeReg 7 (termLocCode x.W v), _,
        Exec.ite_true hcond (by omega) htr, rfl, ?_, ?_⟩
      · rw [State.readReg_writeReg_self, hu_val]
      · intro reg hne; exact State.readReg_writeReg_ne s₁ hne _
    · have hcond : (Expr.op .lt (.reg 6) (.reg 12)).eval w s₁ = some 0 := by
        simp [Expr.eval, State.readReg] at hs₁_6 hs₁_12 ⊢
        simp [hs₁_6, hs₁_12, hloc_w, h12_w, BinOp.eval, BinOp.raw, hlt, hw0]
      let k_idx := termLocCode x.W v - elemWallNumVerts x.h
      have hk_lt : k_idx < (elemWallEdges x.h).length := by omega
      have hk_w : k_idx < 2 ^ w := by omega
      have hu_val : u_rep.1 = ((elemWallEdges x.h)[k_idx]'hk_lt).1.1 := by
        dsimp [u_rep, repVertOfLoc, k_idx]
        simp [hlt]
      have hsub : Exec w (.assign 7 (.op .sub (.reg 6) (.reg 12))) s₁
          (s₁.writeReg 7 k_idx) ((Expr.op .sub (.reg 6) (.reg 12)).cost + 1) :=
        Exec.assign (eval_op (eval_reg hs₁_6 hloc_w) (eval_reg hs₁_12 h12_w)
          (by simp [BinOp.eval, BinOp.raw, k_idx, hk_w]))
      let s₁' := s₁.writeReg 7 k_idx
      have hs₁'_7 : s₁'.readReg 7 = k_idx := State.readReg_writeReg_self s₁ 7 k_idx
      have hu_w : u_rep.1 < 2 ^ w := by have := u_rep.2; omega
      have hrd3 : Exec w (.assign 7 (.read edgeU1Arr (.reg 7))) s₁'
          (s₁'.writeReg 7 u_rep.1) ((Expr.read edgeU1Arr (.reg 7)).cost + 1) := by
        apply Exec.assign
        exact eval_read (eval_reg hs₁'_7 hk_w)
          (by change k_idx < (s.readArr edgeU1Arr).length; rw [harr3_len]; exact hk_lt)
          (by rw [hu_val]; exact harr3 ⟨k_idx, hk_lt⟩)
          hu_w
      refine ⟨s₁'.writeReg 7 u_rep.1, _,
        Exec.ite_false hcond (Exec.seq hsub hrd3), rfl,
        State.readReg_writeReg_self _ _ _, ?_⟩
      intro reg hne
      rw [State.readReg_writeReg_ne _ hne, State.readReg_writeReg_ne _ hne]
  rcases hbranch2 with ⟨s₂, t₂, h2, harr₂, hs₂_7, hs₂_other⟩
  have hs₂_3 : s₂.readReg 3 = x.h := by
    rw [hs₂_other 3 (by decide), State.readReg_writeReg_ne s (by decide), hr3]
  have hs₂_14 : s₂.readReg 14 = 2 * x.h + 2 := by
    rw [hs₂_other 14 (by decide), State.readReg_writeReg_ne s (by decide), hr14]
  have hu_lt : u_rep.1 < elemWallNumVerts x.h := u_rep.2
  have hu1_w : u_rep.1 + 1 < 2 ^ w := by omega
  have hu_w : u_rep.1 < 2 ^ w := by omega
  have h3 : Exec w (.assign 7 (.op .add (.reg 7) (.const 1))) s₂
      (s₂.writeReg 7 (u_rep.1 + 1)) ((Expr.op .add (.reg 7) (.const 1)).cost + 1) := by
    apply Exec.assign
    simp [Expr.eval, State.readReg] at hs₂_7 ⊢
    simp [hs₂_7, hu_w, hw1, BinOp.eval, BinOp.raw, hu1_w]
  let s₄ := s₂.writeReg 7 (u_rep.1 + 1)
  have hs₄_7 : s₄.readReg 7 = u_rep.1 + 1 := State.readReg_writeReg_self _ _ _
  have hs₄_14 : s₄.readReg 14 = 2 * x.h + 2 := by
    rw [State.readReg_writeReg_ne s₂ (by decide), hs₂_14]
  let q := repCoord x.W v
  have hcoord : coordOf x.h u_rep = q :=
    coordOf_repVertOfLoc_termLocCode x.hW_valid.2.2 hv_mem
  have hqx : (u_rep.1 + 1) % (2 * x.h + 2) = q.1 :=
    congrArg Prod.fst ((coordOf_eq x.h u_rep).symm.trans hcoord)
  have hqy : (u_rep.1 + 1) / (2 * x.h + 2) = q.2 :=
    congrArg Prod.snd ((coordOf_eq x.h u_rep).symm.trans hcoord)
  have hqx_lt : q.1 < 2 * x.h + 2 := by
    rw [← hqx]
    exact Nat.mod_lt _ (by omega)
  have hqx_w : q.1 < 2 ^ w := by omega
  have hqy_w : q.2 < 2 ^ w := by
    have : (u_rep.1 + 1) / (2 * x.h + 2) ≤ u_rep.1 + 1 := Nat.div_le_self _ _
    omega
  have h5 : Exec w (.assign 8 (.op .mod (.reg 7) (.reg 14))) s₄
      (s₄.writeReg 8 q.1) ((Expr.op .mod (.reg 7) (.reg 14)).cost + 1) := by
    apply Exec.assign
    simp [Expr.eval, State.readReg] at hs₄_7 hs₄_14 ⊢
    simp [hs₄_7, hs₄_14, hu1_w, hw_h, BinOp.eval, BinOp.raw, hqx, hqx_w]
  let s₅ := s₄.writeReg 8 q.1
  have hs₅_7 : s₅.readReg 7 = u_rep.1 + 1 := by
    rw [State.readReg_writeReg_ne s₄ (by decide), hs₄_7]
  have hs₅_14 : s₅.readReg 14 = 2 * x.h + 2 := by
    rw [State.readReg_writeReg_ne s₄ (by decide), hs₄_14]
  have h6 : Exec w (.assign 9 (.op .div (.reg 7) (.reg 14))) s₅
      (s₅.writeReg 9 q.2) ((Expr.op .div (.reg 7) (.reg 14)).cost + 1) := by
    apply Exec.assign
    simp [Expr.eval, State.readReg] at hs₅_7 hs₅_14 ⊢
    simp [hs₅_7, hs₅_14, hu1_w, hw_h, BinOp.eval, BinOp.raw, hqy, hqy_w]
  let s₆ := s₅.writeReg 9 q.2
  have hs₆_9 : s₆.readReg 9 = q.2 := State.readReg_writeReg_self _ _ _
  have h7 : Exec w (.assign (regTermY p a.1) (.reg 9)) s₆
      (s₆.writeReg (regTermY p a.1) q.2) ((Expr.reg 9).cost + 1) := by
    apply Exec.assign
    simp [Expr.eval, State.readReg] at hs₆_9 ⊢
    simp [hs₆_9, hqy_w]
  let s₇ := s₆.writeReg (regTermY p a.1) q.2
  have hs₇_8 : s₇.readReg 8 = q.1 := by
    have hne1 : (8 : Reg) ≠ regTermY p a.1 := by dsimp [regTermY, Reg]; omega
    rw [State.readReg_writeReg_ne s₆ hne1, State.readReg_writeReg_ne s₅ (by decide),
      State.readReg_writeReg_self]
  have hqx1_w : q.1 + 1 < 2 ^ w := by omega
  have hdiv2_w : (q.1 + 1) / 2 < 2 ^ w := by omega
  have h8 : Exec w (.assign 8 (.op .div (.op .add (.reg 8) (.const 1)) (.const 2))) s₇
      (s₇.writeReg 8 ((q.1 + 1) / 2))
      ((Expr.op .div (.op .add (.reg 8) (.const 1)) (.const 2)).cost + 1) := by
    apply Exec.assign
    simp [Expr.eval, State.readReg] at hs₇_8 ⊢
    simp [hs₇_8, hqx_w, hw1, hw2, BinOp.eval, BinOp.raw, hqx1_w, hdiv2_w]
  let s₈ := s₇.writeReg 8 ((q.1 + 1) / 2)
  have hs₈_8 : s₈.readReg 8 = (q.1 + 1) / 2 := State.readReg_writeReg_self _ _ _
  let c₁ := max ((q.1 + 1) / 2) 1
  have hc₁_w : c₁ < 2 ^ w := by dsimp [c₁]; omega
  have h9 : ∃ s₉ t₉,
      Exec w (.ite (.op .lt (.reg 8) (.const 1)) (.assign 8 (.const 1)) .skip) s₈ s₉ t₉ ∧
      s₉.arr = s₈.arr ∧
      s₉.readReg 8 = c₁ ∧
      (∀ reg : Reg, reg ≠ 8 → s₉.readReg reg = s₈.readReg reg) := by
    by_cases hlt1 : (q.1 + 1) / 2 < 1
    · have hcond : (Expr.op .lt (.reg 8) (.const 1)).eval w s₈ = some 1 := by
        simp [Expr.eval, State.readReg] at hs₈_8 ⊢
        simp [hs₈_8, hdiv2_w, hw1, BinOp.eval, BinOp.raw, hlt1]
      have htr : Exec w (.assign 8 (.const 1)) s₈ (s₈.writeReg 8 1) ((Expr.const 1).cost + 1) :=
        Exec.assign (by simp [Expr.eval, hw1])
      refine ⟨s₈.writeReg 8 1, _, Exec.ite_true hcond (by omega) htr, rfl, ?_, ?_⟩
      · rw [State.readReg_writeReg_self]
        dsimp [c₁]; omega
      · intro reg hne; exact State.readReg_writeReg_ne s₈ hne 1
    · have hcond : (Expr.op .lt (.reg 8) (.const 1)).eval w s₈ = some 0 := by
        simp [Expr.eval, State.readReg] at hs₈_8 ⊢
        simp [hs₈_8, hdiv2_w, hw1, BinOp.eval, BinOp.raw, hlt1, hw0]
      refine ⟨s₈, _, Exec.ite_false hcond (Exec.skip s₈), rfl, ?_, fun _ _ => rfl⟩
      rw [hs₈_8]
      dsimp [c₁]; omega
  rcases h9 with ⟨s₉, t₉, h9_exec, harr₉, hs₉_8, hs₉_other⟩
  have hs₉_3 : s₉.readReg 3 = x.h := by
    have hne3 : (3 : Reg) ≠ regTermY p a.1 := by dsimp [regTermY, Reg]; omega
    rw [hs₉_other 3 (by decide), State.readReg_writeReg_ne s₇ (by decide),
      State.readReg_writeReg_ne s₆ hne3, State.readReg_writeReg_ne s₅ (by decide),
      State.readReg_writeReg_ne s₄ (by decide), State.readReg_writeReg_ne s₂ (by decide), hs₂_3]
  have hh_w : x.h < 2 ^ w := by omega
  let c₂ := min c₁ x.h
  have h10 : ∃ s₁₀ t₁₀,
      Exec w
        (.ite (.op .lt (.reg 3) (.reg 8))
          (.assign (regTermC p a.1) (.reg 3))
          (.assign (regTermC p a.1) (.reg 8)))
        s₉ s₁₀ t₁₀ ∧
      s₁₀.arr = s₉.arr ∧
      s₁₀.readReg (regTermC p a.1) = c₂ ∧
      (∀ reg : Reg, reg ≠ regTermC p a.1 → s₁₀.readReg reg = s₉.readReg reg) := by
    by_cases hlt2 : x.h < c₁
    · have hcond : (Expr.op .lt (.reg 3) (.reg 8)).eval w s₉ = some 1 := by
        simp [Expr.eval, State.readReg] at hs₉_3 hs₉_8 ⊢
        simp [hs₉_3, hs₉_8, hh_w, hc₁_w, BinOp.eval, BinOp.raw, hlt2, hw1]
      have htr : Exec w (.assign (regTermC p a.1) (.reg 3)) s₉
          (s₉.writeReg (regTermC p a.1) x.h) ((Expr.reg 3).cost + 1) := by
        apply Exec.assign
        simp [Expr.eval, State.readReg] at hs₉_3 ⊢
        simp [hs₉_3, hh_w]
      refine ⟨s₉.writeReg (regTermC p a.1) x.h, _, Exec.ite_true hcond (by omega) htr,
        rfl, ?_, ?_⟩
      · rw [State.readReg_writeReg_self]
        dsimp [c₂]; omega
      · intro reg hne; exact State.readReg_writeReg_ne s₉ hne _
    · have hcond : (Expr.op .lt (.reg 3) (.reg 8)).eval w s₉ = some 0 := by
        simp [Expr.eval, State.readReg] at hs₉_3 hs₉_8 ⊢
        simp [hs₉_3, hs₉_8, hh_w, hc₁_w, BinOp.eval, BinOp.raw, hlt2, hw0]
      have hfl : Exec w (.assign (regTermC p a.1) (.reg 8)) s₉
          (s₉.writeReg (regTermC p a.1) c₁) ((Expr.reg 8).cost + 1) := by
        apply Exec.assign
        simp [Expr.eval, State.readReg] at hs₉_8 ⊢
        simp [hs₉_8, hc₁_w]
      refine ⟨s₉.writeReg (regTermC p a.1) c₁, _, Exec.ite_false hcond hfl, rfl, ?_, ?_⟩
      · rw [State.readReg_writeReg_self]
        dsimp [c₂]; omega
      · intro reg hne; exact State.readReg_writeReg_ne s₉ hne _
  rcases h10 with ⟨s₁₀, t₁₀, h10_exec, harr₁₀, hs₁₀_c, hs₁₀_other⟩
  refine ⟨s₁₀, _,
    Exec.seq h1 (Exec.seq h2 (Exec.seq h3 (Exec.seq h5
      (Exec.seq h6 (Exec.seq h7 (Exec.seq h8 (Exec.seq h9_exec h10_exec))))))),
    ?_, ?_, ?_, ?_⟩
  · rw [harr₁₀, harr₉]
    exact harr₂
  · rw [hs₁₀_c]
    rfl
  · have hne_cy : regTermY p a.1 ≠ regTermC p a.1 := by dsimp [regTermY, regTermC, Reg]; omega
    have hne_y8 : regTermY p a.1 ≠ 8 := by dsimp [regTermY, Reg]; omega
    rw [hs₁₀_other (regTermY p a.1) hne_cy, hs₉_other (regTermY p a.1) hne_y8,
      State.readReg_writeReg_ne s₇ hne_y8, State.readReg_writeReg_self]
    rfl
  · intro reg h6' h7' h8' h9' hc' hy'
    rw [hs₁₀_other reg hc', hs₉_other reg h8', State.readReg_writeReg_ne s₇ h8',
      State.readReg_writeReg_ne s₆ hy', State.readReg_writeReg_ne s₅ h9',
      State.readReg_writeReg_ne s₄ h8', State.readReg_writeReg_ne s₂ h7',
      hs₂_other reg h7', State.readReg_writeReg_ne s h6']

/-- Unrolled loop computing `(regTermC p a.1, regTermY p a.1)` for all `a ∈ xs`. -/
def computeTermCellsLoop (p : ℕ) : List (Fin (alg74NumTerms p)) → Cmd
  | [] => .skip
  | a :: rest => .seq (computeOneTermCellCmd p a.1) (computeTermCellsLoop p rest)

theorem computeTermCellsLoop_free (p : ℕ) :
    ∀ xs : List (Fin (alg74NumTerms p)), (computeTermCellsLoop p xs).IsLoopAllocFree
  | [] => trivial
  | a :: rest => ⟨computeOneTermCellCmd_free p a.1, computeTermCellsLoop_free p rest⟩

theorem computeTermCellsLoop_exec {w p r : ℕ} (x : Alg74Input p r)
    (hh1 : 1 ≤ x.h)
    (hw_n : x.n < 2 ^ w)
    (hw_h : 2 * x.h + 2 < 2 ^ w)
    (hw_wall : elemWallNumVerts x.h + (elemWallEdges x.h).length < 2 ^ w) :
    ∀ (xs : List (Fin (alg74NumTerms p))) (s : State),
      xs.Nodup →
      s.readReg 3 = x.h →
      s.readReg 12 = elemWallNumVerts x.h →
      s.readReg 14 = 2 * x.h + 2 →
      (harr2_len : (s.readArr locArr).length = x.n) →
      (∀ v ∈ x.W.vertexFinset,
        (s.readArr locArr)[v.1]'(by rw [harr2_len]; exact v.2) = termLocCode x.W v) →
      (harr3_len : (s.readArr edgeU1Arr).length = (elemWallEdges x.h).length) →
      (∀ k : Fin (elemWallEdges x.h).length,
        (s.readArr edgeU1Arr)[k.1]'(by rw [harr3_len]; exact k.2) = ((elemWallEdges x.h)[k.1]'k.2).1.1) →
      (∀ a ∈ xs, s.readReg (regTermVert a.1) = (alg74TermVert x a).1) →
      ∃ s' t, Exec w (computeTermCellsLoop p xs) s s' t ∧
        s'.arr = s.arr ∧
        (∀ a ∈ xs,
          s'.readReg (regTermC p a.1) = (alg74Term x a).1 ∧
          s'.readReg (regTermY p a.1) = (alg74Term x a).2) ∧
        (∀ reg : Reg, reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 9 →
          (∀ a ∈ xs, reg ≠ regTermC p a.1 ∧ reg ≠ regTermY p a.1) →
          s'.readReg reg = s.readReg reg)
  | [], s, _, _, _, _, _, _, _, _, _ => by
    refine ⟨s, 1, Exec.skip s, rfl, ?_, ?_⟩
    · intro a ha; nomatch ha
    · intro reg _ _ _ _ _; rfl
  | a :: rest, s, hnodup, hr3, hr12, hr14, harr2_len, harr2, harr3_len, harr3, hterm => by
    have ha_not_mem : a ∉ rest := (List.nodup_cons.mp hnodup).1
    have hnodup_rest : rest.Nodup := (List.nodup_cons.mp hnodup).2
    rcases computeOneTermCellCmd_exec x hh1 hw_n hw_h hw_wall s hr3 hr12 hr14 harr2_len harr2
        harr3_len harr3 a (hterm a List.mem_cons_self) with
      ⟨s₁, t₁, h1, harr₁, hc₁, hy₁, hother₁⟩
    have hr3_1 : s₁.readReg 3 = x.h := by
      rw [hother₁ 3 (by decide) (by decide) (by decide) (by decide)
        (by dsimp [regTermC, Reg]; omega) (by dsimp [regTermY, Reg]; omega), hr3]
    have hr12_1 : s₁.readReg 12 = elemWallNumVerts x.h := by
      rw [hother₁ 12 (by decide) (by decide) (by decide) (by decide)
        (by dsimp [regTermC, Reg]; omega) (by dsimp [regTermY, Reg]; omega), hr12]
    have hr14_1 : s₁.readReg 14 = 2 * x.h + 2 := by
      rw [hother₁ 14 (by decide) (by decide) (by decide) (by decide)
        (by dsimp [regTermC, Reg]; omega) (by dsimp [regTermY, Reg]; omega), hr14]
    have harr₁' : s₁.arrs = s.arrs := harr₁
    have harr2_len1 : (s₁.readArr locArr).length = x.n := by
      simp [State.readArr, harr₁', harr2_len]
    have harr2_1 : ∀ v ∈ x.W.vertexFinset,
        (s₁.readArr locArr)[v.1]'(by rw [harr2_len1]; exact v.2) = termLocCode x.W v := by
      intro v hv; simp [State.readArr, harr₁', harr2 v hv]
    have harr3_len1 : (s₁.readArr edgeU1Arr).length = (elemWallEdges x.h).length := by
      simp [State.readArr, harr₁', harr3_len]
    have harr3_1 : ∀ k : Fin (elemWallEdges x.h).length,
        (s₁.readArr edgeU1Arr)[k.1]'(by rw [harr3_len1]; exact k.2) = ((elemWallEdges x.h)[k.1]'k.2).1.1 := by
      intro k; simp [State.readArr, harr₁', harr3 k]
    have hterm_rest : ∀ b ∈ rest, s₁.readReg (regTermVert b.1) = (alg74TermVert x b).1 := by
      intro b hb
      have := b.2
      rw [hother₁ (regTermVert b.1)
        (by dsimp [regTermVert, Reg]; omega)
        (by dsimp [regTermVert, Reg]; omega)
        (by dsimp [regTermVert, Reg]; omega)
        (by dsimp [regTermVert, Reg]; omega)
        (by dsimp [regTermVert, regTermC, alg74NumTerms, Reg] at *; omega)
        (by dsimp [regTermVert, regTermY, alg74NumTerms, Reg] at *; omega)]
      exact hterm b (List.mem_cons_of_mem a hb)
    rcases computeTermCellsLoop_exec x hh1 hw_n hw_h hw_wall rest s₁ hnodup_rest
        hr3_1 hr12_1 hr14_1 harr2_len1 harr2_1 harr3_len1 harr3_1 hterm_rest with
      ⟨s₂, t₂, h2, harr₂, hdone_rest, hother₂⟩
    refine ⟨s₂, t₁ + t₂, Exec.seq h1 h2, harr₂.trans harr₁, ?_, ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb_rest
      · have hne_b : ∀ c ∈ rest,
            (regTermC p b.1 ≠ regTermC p c.1 ∧ regTermC p b.1 ≠ regTermY p c.1) ∧
            (regTermY p b.1 ≠ regTermC p c.1 ∧ regTermY p b.1 ≠ regTermY p c.1) := by
          intro c hc
          have hne_val : b.1 ≠ c.1 := fun h => ha_not_mem (Fin.ext h ▸ hc)
          refine ⟨⟨by dsimp [regTermC, Reg]; omega, by dsimp [regTermC, regTermY, Reg]; omega⟩,
            ⟨by dsimp [regTermC, regTermY, Reg]; omega, by dsimp [regTermY, Reg]; omega⟩⟩
        refine ⟨?_, ?_⟩
        · rw [hother₂ (regTermC p b.1)
            (by dsimp [regTermC, Reg]; omega)
            (by dsimp [regTermC, Reg]; omega)
            (by dsimp [regTermC, Reg]; omega)
            (by dsimp [regTermC, Reg]; omega)
            (fun c hc => (hne_b c hc).1), hc₁]
        · rw [hother₂ (regTermY p b.1)
            (by dsimp [regTermY, Reg]; omega)
            (by dsimp [regTermY, Reg]; omega)
            (by dsimp [regTermY, Reg]; omega)
            (by dsimp [regTermY, Reg]; omega)
            (fun c hc => (hne_b c hc).2), hy₁]
      · exact hdone_rest b hb_rest
    · intro reg h6 h7 h8 h9 hne_all
      have hne_a := hne_all a List.mem_cons_self
      have hne_rest : ∀ b ∈ rest, reg ≠ regTermC p b.1 ∧ reg ≠ regTermY p b.1 :=
        fun b hb => hne_all b (List.mem_cons_of_mem a hb)
      rw [hother₂ reg h6 h7 h8 h9 hne_rest,
        hother₁ reg h6 h7 h8 h9 hne_a.1 hne_a.2]

/-- Compute `(regTermC p a.1, regTermY p a.1)` for all `a : Fin (alg74NumTerms p)`. -/
def computeTermCellsCmd (p : ℕ) : Cmd :=
  computeTermCellsLoop p (List.finRange (alg74NumTerms p))

theorem computeTermCellsCmd_free (p : ℕ) :
    (computeTermCellsCmd p).IsLoopAllocFree :=
  computeTermCellsLoop_free p _

/-! #### Sub-step 4b: Choosing the Box Margin (`computeBoxMarginCmd`) -/

/-- Boolean expression testing `IsInInnerBox h B (c, y)`. -/
def inInnerBoxExpr (e_h e_B e_c e_y : Expr) : Expr :=
  exprAnd (exprLe e_B e_c)
    (exprAnd (exprLe e_c (.op .sub e_h e_B))
      (exprAnd (exprLe e_B e_y) (exprLe e_y (.op .sub e_h e_B))))

theorem eval_inInnerBoxExpr {w : ℕ} {s : State} {e_h e_B e_c e_y : Expr} {vh vB vc vy : ℕ}
    (hw1 : 1 < 2 ^ w)
    (hh : e_h.eval w s = some vh)
    (hB : e_B.eval w s = some vB)
    (hc : e_c.eval w s = some vc)
    (hy : e_y.eval w s = some vy) :
    (inInnerBoxExpr e_h e_B e_c e_y).eval w s =
      some (if IsInInnerBox vh vB (vc, vy) then 1 else 0) := by
  have hvh_lt : vh < 2 ^ w := eval_lt_two_pow hh
  have hsub : (Expr.op .sub e_h e_B).eval w s = some (vh - vB) := by
    simp [Expr.eval, hh, hB, BinOp.eval, BinOp.raw, checkWord]
    omega
  unfold inInnerBoxExpr IsInInnerBox
  dsimp only
  rw [eval_exprAnd hw1 (eval_exprLe hw1 hB hc)
    (eval_exprAnd hw1 (eval_exprLe hw1 hc hsub)
      (eval_exprAnd hw1 (eval_exprLe hw1 hB hy) (eval_exprLe hw1 hy hsub)))]

/-- Set `r_15 = chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x)`. -/
def computeBoxMarginCmd (p : ℕ) : Cmd :=
  let B₂ := alg74BoxMarginConst p
  .ite (exprAll (List.finRange (alg74NumTerms p)) (fun a =>
      inInnerBoxExpr (.reg 3) (.const B₂) (.reg (regTermC p a.1)) (.reg (regTermY p a.1))))
    (.assign 15 (.const 2))
    (.assign 15 (.const B₂))

theorem computeBoxMarginCmd_free (p : ℕ) :
    (computeBoxMarginCmd p).IsLoopAllocFree := by
  dsimp [computeBoxMarginCmd, Cmd.IsLoopAllocFree]
  trivial

theorem computeBoxMarginCmd_exec {w p r : ℕ} (x : Alg74Input p r)
    (hh1 : 1 ≤ x.h)
    (hw2 : 2 < 2 ^ w)
    (hw_h : x.h < 2 ^ w)
    (hw_B₂ : alg74BoxMarginConst p < 2 ^ w)
    (s : State)
    (hr3 : s.readReg 3 = x.h)
    (htermC : ∀ a : Fin (alg74NumTerms p),
      s.readReg (regTermC p a.1) = (alg74Term x a).1 ∧
      s.readReg (regTermY p a.1) = (alg74Term x a).2) :
    ∃ s' t, Exec w (computeBoxMarginCmd p) s s' t ∧
      s'.arr = s.arr ∧
      s'.readReg 15 = chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x) ∧
      (∀ reg : Reg, reg ≠ 15 → s'.readReg reg = s.readReg reg) := by
  have hw1 : 1 < 2 ^ w := by omega
  let B₂ := alg74BoxMarginConst p
  have hev_all := eval_exprAll (List.finRange (alg74NumTerms p))
    (fun a => inInnerBoxExpr (.reg 3) (.const B₂) (.reg (regTermC p a.1)) (.reg (regTermY p a.1)))
    (fun a => IsInInnerBox x.h B₂ (alg74Term x a)) hw1
    (by
      intro a _
      have ha := htermC a
      have hb := alg74Term_bounds x hh1 a
      have hc_w : (alg74Term x a).1 < 2 ^ w := by omega
      have hy_w : (alg74Term x a).2 < 2 ^ w := by omega
      exact eval_inInnerBoxExpr hw1
        (eval_reg hr3 hw_h)
        (by simp [Expr.eval, B₂, hw_B₂])
        (eval_reg ha.1 hc_w)
        (eval_reg ha.2 hy_w))
  have hmargin := chooseBoxMargin_eq_ite p x.h (alg74NumTerms p) (alg74Term x)
  change chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x) =
    if ∀ a ∈ List.finRange (alg74NumTerms p), IsInInnerBox x.h B₂ (alg74Term x a) then 2 else B₂ at hmargin
  split_ifs at hev_all hmargin with hall
  · have htr : Exec w (.assign 15 (.const 2)) s (s.writeReg 15 2) ((Expr.const 2).cost + 1) :=
      Exec.assign (by simp [Expr.eval, hw2])
    refine ⟨s.writeReg 15 2, _, Exec.ite_true hev_all (by omega) htr,
      rfl, ?_, fun reg hne => State.readReg_writeReg_ne s hne 2⟩
    rw [State.readReg_writeReg_self, hmargin]
  · have hfl : Exec w (.assign 15 (.const B₂)) s (s.writeReg 15 B₂) ((Expr.const B₂).cost + 1) :=
      Exec.assign (by simp [Expr.eval, B₂, hw_B₂])
    refine ⟨s.writeReg 15 B₂, _, Exec.ite_false hev_all hfl,
      rfl, ?_, fun reg hne => State.readReg_writeReg_ne s hne B₂⟩
    rw [State.readReg_writeReg_self, hmargin]

/-! #### Sub-step 4c: Perimeter Terminal Info and Color Permutation (`computePerimAndPermCmd`) -/

/-- Unrolled foldr computing `perimTermInfo` into `(r_16, r_17, r_18, r_19)`. -/
def computePerimLoop (p : ℕ) : List (Fin (alg74NumTerms p)) → Cmd
  | [] =>
    .seq (.assign 16 (.const 0))
      (.seq (.assign 17 (.const 0))
        (.seq (.assign 18 (.const 0))
          (.assign 19 (.const 0))))
  | a :: rest =>
    .seq (computePerimLoop p rest)
      (.ite (exprNot (inInnerBoxExpr (.reg 3) (.reg 15)
          (.reg (regTermC p a.1)) (.reg (regTermY p a.1))))
        (.seq (.assign 16 (.const 1))
          (.seq (.assign 17 (.reg (regTermC p a.1)))
            (.seq (.assign 18 (.reg (regTermY p a.1)))
              (.assign 19 (.const (alg74RawColor p a).1)))))
        .skip)

theorem computePerimLoop_free (p : ℕ) :
    ∀ xs : List (Fin (alg74NumTerms p)), (computePerimLoop p xs).IsLoopAllocFree
  | [] => by dsimp [computePerimLoop, Cmd.IsLoopAllocFree]; trivial
  | a :: rest => by
    dsimp [computePerimLoop, Cmd.IsLoopAllocFree]
    exact ⟨computePerimLoop_free p rest, ⟨trivial, trivial, trivial, trivial⟩, trivial⟩

/-- Step function for `perimTermInfo` foldr. -/
def perimFoldStep {p r : ℕ} (x : Alg74Input p r) (B : ℕ)
    (a : Fin (alg74NumTerms p)) (acc : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  if ¬ IsInInnerBox x.h B (alg74Term x a) then
    (1, (alg74Term x a).1, (alg74Term x a).2, (alg74RawColor p a).1)
  else acc

theorem perimTermInfo_bounds {p r : ℕ} (hp0 : 0 < p) (x : Alg74Input p r) (hh1 : 1 ≤ x.h)
    (B : ℕ) :
    let info := perimTermInfo x.h B (alg74NumTerms p) (alg74Term x) (alg74RawColor p)
    info.1 ≤ 1 ∧ info.2.1 ≤ x.h ∧ info.2.2.1 ≤ x.h ∧ info.2.2.2 < p := by
  unfold perimTermInfo
  suffices ∀ xs : List (Fin (alg74NumTerms p)),
      (xs.foldr (perimFoldStep x B) (0, 0, 0, 0)).1 ≤ 1 ∧
      (xs.foldr (perimFoldStep x B) (0, 0, 0, 0)).2.1 ≤ x.h ∧
      (xs.foldr (perimFoldStep x B) (0, 0, 0, 0)).2.2.1 ≤ x.h ∧
      (xs.foldr (perimFoldStep x B) (0, 0, 0, 0)).2.2.2 < p from
    this (List.finRange (alg74NumTerms p))
  intro xs
  induction xs with
  | nil =>
    simp [hp0]
  | cons a rest ih =>
    simp only [List.foldr_cons, perimFoldStep]
    by_cases hout : ¬ IsInInnerBox x.h B (alg74Term x a)
    · simp only [if_pos hout]
      have hb := alg74Term_bounds x hh1 a
      exact ⟨le_rfl, hb.2.1, hb.2.2, (alg74RawColor p a).2⟩
    · simp only [if_neg hout]
      exact ih

theorem computePerimLoop_exec {w p r : ℕ} (x : Alg74Input p r)
    (hh1 : 1 ≤ x.h)
    (hw1 : 1 < 2 ^ w)
    (hw_p : p < 2 ^ w)
    (hw_h : x.h < 2 ^ w)
    (B : ℕ)
    (hw_B : B < 2 ^ w) :
    ∀ (xs : List (Fin (alg74NumTerms p))) (s : State),
      s.readReg 3 = x.h →
      s.readReg 15 = B →
      (∀ a : Fin (alg74NumTerms p),
        s.readReg (regTermC p a.1) = (alg74Term x a).1 ∧
        s.readReg (regTermY p a.1) = (alg74Term x a).2) →
      ∃ s' t, Exec w (computePerimLoop p xs) s s' t ∧
        s'.arr = s.arr ∧
        s'.readReg 16 = (xs.foldr (perimFoldStep x B) (0, 0, 0, 0)).1 ∧
        s'.readReg 17 = (xs.foldr (perimFoldStep x B) (0, 0, 0, 0)).2.1 ∧
        s'.readReg 18 = (xs.foldr (perimFoldStep x B) (0, 0, 0, 0)).2.2.1 ∧
        s'.readReg 19 = (xs.foldr (perimFoldStep x B) (0, 0, 0, 0)).2.2.2 ∧
        (∀ reg : Reg, reg ≠ 16 → reg ≠ 17 → reg ≠ 18 → reg ≠ 19 →
          s'.readReg reg = s.readReg reg)
  | [], s, _, _, _ => by
    have hw0 : 0 < 2 ^ w := by omega
    have h1 : Exec w (.assign 16 (.const 0)) s (s.writeReg 16 0) ((Expr.const 0).cost + 1) :=
      Exec.assign (by simp [Expr.eval, hw0])
    let s₁ := s.writeReg 16 0
    have h2 : Exec w (.assign 17 (.const 0)) s₁ (s₁.writeReg 17 0) ((Expr.const 0).cost + 1) :=
      Exec.assign (by simp [Expr.eval, hw0])
    let s₂ := s₁.writeReg 17 0
    have h3 : Exec w (.assign 18 (.const 0)) s₂ (s₂.writeReg 18 0) ((Expr.const 0).cost + 1) :=
      Exec.assign (by simp [Expr.eval, hw0])
    let s₃ := s₂.writeReg 18 0
    have h4 : Exec w (.assign 19 (.const 0)) s₃ (s₃.writeReg 19 0) ((Expr.const 0).cost + 1) :=
      Exec.assign (by simp [Expr.eval, hw0])
    let s₄ := s₃.writeReg 19 0
    refine ⟨s₄, _, Exec.seq h1 (Exec.seq h2 (Exec.seq h3 h4)), rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [State.readReg_writeReg_ne s₃ (by decide), State.readReg_writeReg_ne s₂ (by decide),
        State.readReg_writeReg_ne s₁ (by decide), State.readReg_writeReg_self]; rfl
    · rw [State.readReg_writeReg_ne s₃ (by decide), State.readReg_writeReg_ne s₂ (by decide),
        State.readReg_writeReg_self]; rfl
    · rw [State.readReg_writeReg_ne s₃ (by decide), State.readReg_writeReg_self]; rfl
    · exact State.readReg_writeReg_self s₃ 19 0
    · intro reg h16 h17 h18 h19
      rw [State.readReg_writeReg_ne s₃ h19, State.readReg_writeReg_ne s₂ h18,
        State.readReg_writeReg_ne s₁ h17, State.readReg_writeReg_ne s h16]
  | a :: rest, s, hr3, hr15, htermC => by
    rcases computePerimLoop_exec x hh1 hw1 hw_p hw_h B hw_B rest s hr3 hr15 htermC with
      ⟨s₁, t₁, h1, harr₁, hr16_1, hr17_1, hr18_1, hr19_1, hother₁⟩
    have hs₁_3 : s₁.readReg 3 = x.h := by
      rw [hother₁ 3 (by decide) (by decide) (by decide) (by decide), hr3]
    have hs₁_15 : s₁.readReg 15 = B := by
      rw [hother₁ 15 (by decide) (by decide) (by decide) (by decide), hr15]
    have hs₁_c : s₁.readReg (regTermC p a.1) = (alg74Term x a).1 := by
      rw [hother₁ (regTermC p a.1)
        (by dsimp [regTermC, Reg]; omega)
        (by dsimp [regTermC, Reg]; omega)
        (by dsimp [regTermC, Reg]; omega)
        (by dsimp [regTermC, Reg]; omega), (htermC a).1]
    have hs₁_y : s₁.readReg (regTermY p a.1) = (alg74Term x a).2 := by
      rw [hother₁ (regTermY p a.1)
        (by dsimp [regTermY, Reg]; omega)
        (by dsimp [regTermY, Reg]; omega)
        (by dsimp [regTermY, Reg]; omega)
        (by dsimp [regTermY, Reg]; omega), (htermC a).2]
    have hb_a := alg74Term_bounds x hh1 a
    have hc_w : (alg74Term x a).1 < 2 ^ w := by omega
    have hy_w : (alg74Term x a).2 < 2 ^ w := by omega
    have hev_not :
        (exprNot (inInnerBoxExpr (.reg 3) (.reg 15)
          (.reg (regTermC p a.1)) (.reg (regTermY p a.1)))).eval w s₁ =
        some (if ¬ IsInInnerBox x.h B (alg74Term x a) then 1 else 0) :=
      eval_exprNot hw1 (eval_inInnerBoxExpr hw1
        (eval_reg hs₁_3 hw_h) (eval_reg hs₁_15 hw_B)
        (eval_reg hs₁_c hc_w) (eval_reg hs₁_y hy_w))
    by_cases hout : ¬ IsInInnerBox x.h B (alg74Term x a)
    · rw [if_pos hout] at hev_not
      have hw_col : (alg74RawColor p a).1 < 2 ^ w := by
        have := (alg74RawColor p a).2
        omega
      have ha16 : Exec w (.assign 16 (.const 1)) s₁ (s₁.writeReg 16 1) ((Expr.const 1).cost + 1) :=
        Exec.assign (by simp [Expr.eval, hw1])
      let s₂ := s₁.writeReg 16 1
      have hs₂_c : s₂.readReg (regTermC p a.1) = (alg74Term x a).1 := by
        rw [State.readReg_writeReg_ne s₁ (by dsimp [regTermC, Reg]; omega), hs₁_c]
      have ha17 : Exec w (.assign 17 (.reg (regTermC p a.1))) s₂
          (s₂.writeReg 17 (alg74Term x a).1) ((Expr.reg (regTermC p a.1)).cost + 1) :=
        Exec.assign (eval_reg hs₂_c hc_w)
      let s₃ := s₂.writeReg 17 (alg74Term x a).1
      have hs₃_y : s₃.readReg (regTermY p a.1) = (alg74Term x a).2 := by
        rw [State.readReg_writeReg_ne s₂ (by dsimp [regTermY, Reg]; omega),
          State.readReg_writeReg_ne s₁ (by dsimp [regTermY, Reg]; omega), hs₁_y]
      have ha18 : Exec w (.assign 18 (.reg (regTermY p a.1))) s₃
          (s₃.writeReg 18 (alg74Term x a).2) ((Expr.reg (regTermY p a.1)).cost + 1) :=
        Exec.assign (eval_reg hs₃_y hy_w)
      let s₄ := s₃.writeReg 18 (alg74Term x a).2
      have ha19 : Exec w (.assign 19 (.const (alg74RawColor p a).1)) s₄
          (s₄.writeReg 19 (alg74RawColor p a).1) ((Expr.const (alg74RawColor p a).1).cost + 1) :=
        Exec.assign (by simp [Expr.eval, hw_col])
      let s₅ := s₄.writeReg 19 (alg74RawColor p a).1
      refine ⟨s₅, _,
        Exec.seq h1 (Exec.ite_true hev_not (by omega)
          (Exec.seq ha16 (Exec.seq ha17 (Exec.seq ha18 ha19)))),
        harr₁, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.foldr_cons, perimFoldStep, if_pos hout]
        rw [State.readReg_writeReg_ne s₄ (by decide), State.readReg_writeReg_ne s₃ (by decide),
          State.readReg_writeReg_ne s₂ (by decide), State.readReg_writeReg_self]
      · simp only [List.foldr_cons, perimFoldStep, if_pos hout]
        rw [State.readReg_writeReg_ne s₄ (by decide), State.readReg_writeReg_ne s₃ (by decide),
          State.readReg_writeReg_self]
      · simp only [List.foldr_cons, perimFoldStep, if_pos hout]
        rw [State.readReg_writeReg_ne s₄ (by decide), State.readReg_writeReg_self]
      · simp only [List.foldr_cons, perimFoldStep, if_pos hout]
        exact State.readReg_writeReg_self s₄ 19 _
      · intro reg h16 h17 h18 h19
        rw [State.readReg_writeReg_ne s₄ h19, State.readReg_writeReg_ne s₃ h18,
          State.readReg_writeReg_ne s₂ h17, State.readReg_writeReg_ne s₁ h16,
          hother₁ reg h16 h17 h18 h19]
    · rw [if_neg hout] at hev_not
      refine ⟨s₁, _, Exec.seq h1 (Exec.ite_false hev_not (Exec.skip s₁)),
        harr₁, ?_, ?_, ?_, ?_, hother₁⟩
      · simp only [List.foldr_cons, perimFoldStep, if_neg hout]; exact hr16_1
      · simp only [List.foldr_cons, perimFoldStep, if_neg hout]; exact hr17_1
      · simp only [List.foldr_cons, perimFoldStep, if_neg hout]; exact hr18_1
      · simp only [List.foldr_cons, perimFoldStep, if_neg hout]; exact hr19_1

/-- Set `regPermColor p g.1 = (colorPerm ... g).1` using `r_19`. -/
def computeOnePermCmd (p : ℕ) (g : Fin p) : Cmd :=
  if g.1 = 0 then
    .assign (regPermColor p g.1) (.reg 19)
  else
    .ite (exprEq (.const g.1) (.reg 19))
      (.assign (regPermColor p g.1) (.const 0))
      (.assign (regPermColor p g.1) (.const g.1))

theorem computeOnePermCmd_free (p : ℕ) (g : Fin p) :
    (computeOnePermCmd p g).IsLoopAllocFree := by
  unfold computeOnePermCmd
  split_ifs <;> trivial

/-- Unrolled loop setting `regPermColor p g.1` for all `g ∈ gs`. -/
def computePermLoop (p : ℕ) : List (Fin p) → Cmd
  | [] => .skip
  | g :: rest => .seq (computeOnePermCmd p g) (computePermLoop p rest)

theorem computePermLoop_free (p : ℕ) :
    ∀ gs : List (Fin p), (computePermLoop p gs).IsLoopAllocFree
  | [] => trivial
  | g :: rest => ⟨computeOnePermCmd_free p g, computePermLoop_free p rest⟩

theorem computePermLoop_exec {w p r : ℕ} (hp0 : 0 < p) (x : Alg74Input p r)
    (hh1 : 1 ≤ x.h)
    (hw1 : 1 < 2 ^ w)
    (hw_p : p < 2 ^ w)
    (B : ℕ) :
    ∀ (gs : List (Fin p)) (s : State),
      gs.Nodup →
      s.readReg 19 = (perimTermInfo x.h B (alg74NumTerms p) (alg74Term x) (alg74RawColor p)).2.2.2 →
      ∃ s' t, Exec w (computePermLoop p gs) s s' t ∧
        s'.arr = s.arr ∧
        (∀ g ∈ gs,
          s'.readReg (regPermColor p g.1) =
            (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p) g).1) ∧
        (∀ reg : Reg, (∀ g ∈ gs, reg ≠ regPermColor p g.1) → s'.readReg reg = s.readReg reg)
  | [], s, _, _ => by
    refine ⟨s, 1, Exec.skip s, rfl, ?_, fun _ _ => rfl⟩
    intro g hg; nomatch hg
  | g :: rest, s, hnodup, hr19 => by
    have hw0 : 0 < 2 ^ w := by omega
    have hg_not_mem : g ∉ rest := (List.nodup_cons.mp hnodup).1
    have hnodup_rest : rest.Nodup := (List.nodup_cons.mp hnodup).2
    let pcol := (perimTermInfo x.h B (alg74NumTerms p) (alg74Term x) (alg74RawColor p)).2.2.2
    have hpcol_lt : pcol < p := (perimTermInfo_bounds hp0 x hh1 B).2.2.2
    have hpcol_w : pcol < 2 ^ w := by omega
    let target := (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p) g).1
    have htarget_eq : target = if g.1 = 0 then pcol else if g.1 = pcol then 0 else g.1 :=
      colorPerm_val_eq_perimTermInfo x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p) g
    have hstep1 : ∃ s₁ t₁,
        Exec w (computeOnePermCmd p g) s s₁ t₁ ∧
        s₁.arr = s.arr ∧
        s₁.readReg (regPermColor p g.1) = target ∧
        (∀ reg : Reg, reg ≠ regPermColor p g.1 → s₁.readReg reg = s.readReg reg) := by
      unfold computeOnePermCmd
      by_cases hg0 : g.1 = 0
      · rw [if_pos hg0]
        have htr : Exec w (.assign (regPermColor p g.1) (.reg 19)) s
            (s.writeReg (regPermColor p g.1) pcol) ((Expr.reg 19).cost + 1) :=
          Exec.assign (eval_reg hr19 hpcol_w)
        refine ⟨s.writeReg (regPermColor p g.1) pcol, _, htr, rfl, ?_,
          fun reg hne => State.readReg_writeReg_ne s hne pcol⟩
        rw [State.readReg_writeReg_self, htarget_eq]
        simp [hg0]
      · rw [if_neg hg0]
        have hg_lt : g.1 < 2 ^ w := by have := g.2; omega
        have hev_eq : (exprEq (.const g.1) (.reg 19)).eval w s =
            some (if g.1 = pcol then 1 else 0) :=
          eval_exprEq hw1 (by simp [Expr.eval, hg_lt]) (eval_reg hr19 hpcol_w)
        by_cases hgp : g.1 = pcol
        · rw [if_pos hgp] at hev_eq
          have htr : Exec w (.assign (regPermColor p g.1) (.const 0)) s
              (s.writeReg (regPermColor p g.1) 0) ((Expr.const 0).cost + 1) :=
            Exec.assign (by simp [Expr.eval, hw0])
          refine ⟨s.writeReg (regPermColor p g.1) 0, _, Exec.ite_true hev_eq (by omega) htr,
            rfl, ?_, fun reg hne => State.readReg_writeReg_ne s hne 0⟩
          rw [State.readReg_writeReg_self, htarget_eq, if_neg hg0, if_pos hgp]
        · rw [if_neg hgp] at hev_eq
          have hfl : Exec w (.assign (regPermColor p g.1) (.const g.1)) s
              (s.writeReg (regPermColor p g.1) g.1) ((Expr.const g.1).cost + 1) :=
            Exec.assign (by simp [Expr.eval, hg_lt])
          refine ⟨s.writeReg (regPermColor p g.1) g.1, _, Exec.ite_false hev_eq hfl,
            rfl, ?_, fun reg hne => State.readReg_writeReg_ne s hne g.1⟩
          rw [State.readReg_writeReg_self, htarget_eq, if_neg hg0, if_neg hgp]
    rcases hstep1 with ⟨s₁, t₁, h1, harr₁, hg₁, hother₁⟩
    have hr19_1 : s₁.readReg 19 = pcol := by
      rw [hother₁ 19 (by dsimp [regPermColor, Reg]; omega), hr19]
    rcases computePermLoop_exec hp0 x hh1 hw1 hw_p B rest s₁ hnodup_rest hr19_1 with
      ⟨s₂, t₂, h2, harr₂, hdone_rest, hother₂⟩
    refine ⟨s₂, t₁ + t₂, Exec.seq h1 h2, harr₂.trans harr₁, ?_, ?_⟩
    · intro g' hg'
      rcases List.mem_cons.mp hg' with rfl | hg'_rest
      · have hne_rest : ∀ g'' ∈ rest, regPermColor p g'.1 ≠ regPermColor p g''.1 := by
          intro g'' hg'' heq
          have hval : g'.1 = g''.1 := by dsimp [regPermColor, Reg] at heq; omega
          exact hg_not_mem (Fin.ext hval ▸ hg'')
        rw [hother₂ (regPermColor p g'.1) hne_rest, hg₁]
      · exact hdone_rest g' hg'_rest
    · intro reg hne_all
      have hne_g := hne_all g List.mem_cons_self
      have hne_rest : ∀ g' ∈ rest, reg ≠ regPermColor p g'.1 :=
        fun g' hg' => hne_all g' (List.mem_cons_of_mem g hg')
      rw [hother₂ reg hne_rest, hother₁ reg hne_g]

/-- Compute `perimTermInfo` into `r_16..r_19` and `colorPerm` into `regPermColor p 0 .. p - 1`. -/
def computePerimAndPermCmd (p : ℕ) : Cmd :=
  .seq (computePerimLoop p (List.finRange (alg74NumTerms p)))
    (computePermLoop p (List.finRange p))

theorem computePerimAndPermCmd_free (p : ℕ) :
    (computePerimAndPermCmd p).IsLoopAllocFree :=
  ⟨computePerimLoop_free p _, computePermLoop_free p _⟩

/-! #### Sub-step 4d: Insertion Sort of Terminals (`insertionSortTermsCmd`) -/

/-- Predicate stating that sort slot `idx` holds the 4-tuple `(key, c, y, g)` for terminal
`a : Fin (alg74NumTerms p)`. -/
def SortSlotHolds {p r : ℕ} (hp0 : 0 < p) (x : Alg74Input p r) (B : ℕ)
    (s : State) (idx : ℕ) (a : Fin (alg74NumTerms p)) : Prop :=
  let q := alg74Term x a
  let perm := colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p)
  s.readReg (regSortKey p idx) = termSortKey x.h B q ∧
  s.readReg (regSortC p idx) = q.1 ∧
  s.readReg (regSortY p idx) = q.2 ∧
  s.readReg (regSortG p idx) = (perm (alg74RawColor p a)).1

theorem sortSlotHolds_congr {p r : ℕ} {hp0 : 0 < p} {x : Alg74Input p r} {B : ℕ}
    {s₁ s₂ : State} {idx : ℕ} {a : Fin (alg74NumTerms p)}
    (h : SortSlotHolds hp0 x B s₁ idx a)
    (hk : s₂.readReg (regSortKey p idx) = s₁.readReg (regSortKey p idx))
    (hc : s₂.readReg (regSortC p idx) = s₁.readReg (regSortC p idx))
    (hy : s₂.readReg (regSortY p idx) = s₁.readReg (regSortY p idx))
    (hg : s₂.readReg (regSortG p idx) = s₁.readReg (regSortG p idx)) :
    SortSlotHolds hp0 x B s₂ idx a :=
  ⟨hk.trans h.1, hc.trans h.2.1, hy.trans h.2.2.1, hg.trans h.2.2.2⟩

theorem termSortKey_le {p r : ℕ} (x : Alg74Input p r) (hh1 : 1 ≤ x.h)
    (B : ℕ) (a : Fin (alg74NumTerms p)) :
    termSortKey x.h B (alg74Term x a) ≤ x.h + 1 := by
  have hb := alg74Term_bounds x hh1 a
  unfold termSortKey
  split_ifs <;> omega

/-- Copy the 4-tuple in sort slot `src` to sort slot `dst`. -/
def copySortSlotCmd (p src dst : ℕ) : Cmd :=
  .seq (.assign (regSortKey p dst) (.reg (regSortKey p src)))
    (.seq (.assign (regSortC p dst) (.reg (regSortC p src)))
      (.seq (.assign (regSortY p dst) (.reg (regSortY p src)))
        (.assign (regSortG p dst) (.reg (regSortG p src)))))

theorem copySortSlotCmd_free (p src dst : ℕ) :
    (copySortSlotCmd p src dst).IsLoopAllocFree := by
  dsimp [copySortSlotCmd, Cmd.IsLoopAllocFree]
  trivial

theorem copySortSlotCmd_exec {w p r : ℕ} (hp0 : 0 < p) (x : Alg74Input p r)
    (hh1 : 1 ≤ x.h) (hw_h : x.h + 1 < 2 ^ w) (hw_p : p < 2 ^ w) (B : ℕ)
    (src dst : ℕ) (_hne_sd : src ≠ dst) (a : Fin (alg74NumTerms p)) (s : State)
    (hsrc : SortSlotHolds hp0 x B s src a) :
    ∃ s' t, Exec w (copySortSlotCmd p src dst) s s' t ∧
      s'.arr = s.arr ∧
      SortSlotHolds hp0 x B s' dst a ∧
      (∀ reg : Reg,
        reg ≠ regSortKey p dst → reg ≠ regSortC p dst →
        reg ≠ regSortY p dst → reg ≠ regSortG p dst →
        s'.readReg reg = s.readReg reg) := by
  have hkey_le := termSortKey_le x hh1 B a
  have hb := alg74Term_bounds x hh1 a
  have hk_w : s.readReg (regSortKey p src) < 2 ^ w := by rw [hsrc.1]; omega
  have hc_w : s.readReg (regSortC p src) < 2 ^ w := by rw [hsrc.2.1]; omega
  have hy_w : s.readReg (regSortY p src) < 2 ^ w := by rw [hsrc.2.2.1]; omega
  have hg_w : s.readReg (regSortG p src) < 2 ^ w := by
    rw [hsrc.2.2.2]
    have := (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p)
      (alg74RawColor p a)).2
    omega
  have h1 : Exec w (.assign (regSortKey p dst) (.reg (regSortKey p src))) s
      (s.writeReg (regSortKey p dst) (s.readReg (regSortKey p src)))
      ((Expr.reg (regSortKey p src)).cost + 1) :=
    Exec.assign (by simp [Expr.eval, State.readReg] at hk_w ⊢; exact hk_w)
  let s₁ := s.writeReg (regSortKey p dst) (s.readReg (regSortKey p src))
  have hs₁_c : s₁.readReg (regSortC p src) = s.readReg (regSortC p src) :=
    State.readReg_writeReg_ne s (by dsimp [regSortC, regSortKey, Reg]; omega) _
  have h2 : Exec w (.assign (regSortC p dst) (.reg (regSortC p src))) s₁
      (s₁.writeReg (regSortC p dst) (s.readReg (regSortC p src)))
      ((Expr.reg (regSortC p src)).cost + 1) := by
    apply Exec.assign
    simp [Expr.eval, State.readReg] at hs₁_c hc_w ⊢
    simp [hs₁_c, hc_w]
  let s₂ := s₁.writeReg (regSortC p dst) (s.readReg (regSortC p src))
  have hs₂_y : s₂.readReg (regSortY p src) = s.readReg (regSortY p src) := by
    rw [State.readReg_writeReg_ne s₁ (by dsimp [regSortY, regSortC, Reg]; omega),
      State.readReg_writeReg_ne s (by dsimp [regSortY, regSortKey, Reg]; omega)]
  have h3 : Exec w (.assign (regSortY p dst) (.reg (regSortY p src))) s₂
      (s₂.writeReg (regSortY p dst) (s.readReg (regSortY p src)))
      ((Expr.reg (regSortY p src)).cost + 1) := by
    apply Exec.assign
    simp [Expr.eval, State.readReg] at hs₂_y hy_w ⊢
    simp [hs₂_y, hy_w]
  let s₃ := s₂.writeReg (regSortY p dst) (s.readReg (regSortY p src))
  have hs₃_g : s₃.readReg (regSortG p src) = s.readReg (regSortG p src) := by
    rw [State.readReg_writeReg_ne s₂ (by dsimp [regSortG, regSortY, Reg]; omega),
      State.readReg_writeReg_ne s₁ (by dsimp [regSortG, regSortC, Reg]; omega),
      State.readReg_writeReg_ne s (by dsimp [regSortG, regSortKey, Reg]; omega)]
  have h4 : Exec w (.assign (regSortG p dst) (.reg (regSortG p src))) s₃
      (s₃.writeReg (regSortG p dst) (s.readReg (regSortG p src)))
      ((Expr.reg (regSortG p src)).cost + 1) := by
    apply Exec.assign
    simp [Expr.eval, State.readReg] at hs₃_g hg_w ⊢
    simp [hs₃_g, hg_w]
  let s₄ := s₃.writeReg (regSortG p dst) (s.readReg (regSortG p src))
  refine ⟨s₄, _, Exec.seq h1 (Exec.seq h2 (Exec.seq h3 h4)), rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [State.readReg_writeReg_ne s₃ (by dsimp [regSortKey, regSortG, Reg]; omega),
        State.readReg_writeReg_ne s₂ (by dsimp [regSortKey, regSortY, Reg]; omega),
        State.readReg_writeReg_ne s₁ (by dsimp [regSortKey, regSortC, Reg]; omega),
        State.readReg_writeReg_self, hsrc.1]
    · rw [State.readReg_writeReg_ne s₃ (by dsimp [regSortC, regSortG, Reg]; omega),
        State.readReg_writeReg_ne s₂ (by dsimp [regSortC, regSortY, Reg]; omega),
        State.readReg_writeReg_self, hsrc.2.1]
    · rw [State.readReg_writeReg_ne s₃ (by dsimp [regSortY, regSortG, Reg]; omega),
        State.readReg_writeReg_self, hsrc.2.2.1]
    · rw [State.readReg_writeReg_self, hsrc.2.2.2]
  · intro reg hk hc hy hg
    rw [State.readReg_writeReg_ne s₃ hg, State.readReg_writeReg_ne s₂ hy,
      State.readReg_writeReg_ne s₁ hc, State.readReg_writeReg_ne s hk]

/-- Write `(r_6, r_7, r_8, r_9)` into sort slot `dst`. -/
def writeScratchToSlotCmd (p dst : ℕ) : Cmd :=
  .seq (.assign (regSortKey p dst) (.reg 6))
    (.seq (.assign (regSortC p dst) (.reg 7))
      (.seq (.assign (regSortY p dst) (.reg 8))
        (.assign (regSortG p dst) (.reg 9))))

theorem writeScratchToSlotCmd_free (p dst : ℕ) :
    (writeScratchToSlotCmd p dst).IsLoopAllocFree := by
  dsimp [writeScratchToSlotCmd, Cmd.IsLoopAllocFree]
  trivial

theorem writeScratchToSlotCmd_exec {w p r : ℕ} (hp0 : 0 < p) (x : Alg74Input p r)
    (hh1 : 1 ≤ x.h) (hw_h : x.h + 1 < 2 ^ w) (hw_p : p < 2 ^ w) (B : ℕ)
    (dst : ℕ) (a : Fin (alg74NumTerms p)) (s : State)
    (hr6 : s.readReg 6 = termSortKey x.h B (alg74Term x a))
    (hr7 : s.readReg 7 = (alg74Term x a).1)
    (hr8 : s.readReg 8 = (alg74Term x a).2)
    (hr9 : s.readReg 9 =
      (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p)
        (alg74RawColor p a)).1) :
    ∃ s' t, Exec w (writeScratchToSlotCmd p dst) s s' t ∧
      s'.arr = s.arr ∧
      SortSlotHolds hp0 x B s' dst a ∧
      (∀ reg : Reg,
        reg ≠ regSortKey p dst → reg ≠ regSortC p dst →
        reg ≠ regSortY p dst → reg ≠ regSortG p dst →
        s'.readReg reg = s.readReg reg) := by
  have hkey_le := termSortKey_le x hh1 B a
  have hb := alg74Term_bounds x hh1 a
  have h6_w : s.readReg 6 < 2 ^ w := by rw [hr6]; omega
  have h7_w : s.readReg 7 < 2 ^ w := by rw [hr7]; omega
  have h8_w : s.readReg 8 < 2 ^ w := by rw [hr8]; omega
  have h9_w : s.readReg 9 < 2 ^ w := by
    rw [hr9]
    have := (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p)
      (alg74RawColor p a)).2
    omega
  have h1 : Exec w (.assign (regSortKey p dst) (.reg 6)) s
      (s.writeReg (regSortKey p dst) (s.readReg 6)) ((Expr.reg 6).cost + 1) :=
    Exec.assign (by simp [Expr.eval, State.readReg] at h6_w ⊢; exact h6_w)
  let s₁ := s.writeReg (regSortKey p dst) (s.readReg 6)
  have hs₁_7 : s₁.readReg 7 = s.readReg 7 :=
    State.readReg_writeReg_ne s (by dsimp [regSortKey, regSortBase, Reg]; omega) _
  have h2 : Exec w (.assign (regSortC p dst) (.reg 7)) s₁
      (s₁.writeReg (regSortC p dst) (s.readReg 7)) ((Expr.reg 7).cost + 1) := by
    apply Exec.assign
    simp [Expr.eval, State.readReg] at hs₁_7 h7_w ⊢
    simp [hs₁_7, h7_w]
  let s₂ := s₁.writeReg (regSortC p dst) (s.readReg 7)
  have hs₂_8 : s₂.readReg 8 = s.readReg 8 := by
    rw [State.readReg_writeReg_ne s₁ (by dsimp [regSortC, regSortBase, Reg]; omega),
      State.readReg_writeReg_ne s (by dsimp [regSortKey, regSortBase, Reg]; omega)]
  have h3 : Exec w (.assign (regSortY p dst) (.reg 8)) s₂
      (s₂.writeReg (regSortY p dst) (s.readReg 8)) ((Expr.reg 8).cost + 1) := by
    apply Exec.assign
    simp [Expr.eval, State.readReg] at hs₂_8 h8_w ⊢
    simp [hs₂_8, h8_w]
  let s₃ := s₂.writeReg (regSortY p dst) (s.readReg 8)
  have hs₃_9 : s₃.readReg 9 = s.readReg 9 := by
    rw [State.readReg_writeReg_ne s₂ (by dsimp [regSortY, regSortBase, Reg]; omega),
      State.readReg_writeReg_ne s₁ (by dsimp [regSortC, regSortBase, Reg]; omega),
      State.readReg_writeReg_ne s (by dsimp [regSortKey, regSortBase, Reg]; omega)]
  have h4 : Exec w (.assign (regSortG p dst) (.reg 9)) s₃
      (s₃.writeReg (regSortG p dst) (s.readReg 9)) ((Expr.reg 9).cost + 1) := by
    apply Exec.assign
    simp [Expr.eval, State.readReg] at hs₃_9 h9_w ⊢
    simp [hs₃_9, h9_w]
  let s₄ := s₃.writeReg (regSortG p dst) (s.readReg 9)
  refine ⟨s₄, _, Exec.seq h1 (Exec.seq h2 (Exec.seq h3 h4)), rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [State.readReg_writeReg_ne s₃ (by dsimp [regSortKey, regSortG, Reg]; omega),
        State.readReg_writeReg_ne s₂ (by dsimp [regSortKey, regSortY, Reg]; omega),
        State.readReg_writeReg_ne s₁ (by dsimp [regSortKey, regSortC, Reg]; omega),
        State.readReg_writeReg_self, hr6]
    · rw [State.readReg_writeReg_ne s₃ (by dsimp [regSortC, regSortG, Reg]; omega),
        State.readReg_writeReg_ne s₂ (by dsimp [regSortC, regSortY, Reg]; omega),
        State.readReg_writeReg_self, hr7]
    · rw [State.readReg_writeReg_ne s₃ (by dsimp [regSortY, regSortG, Reg]; omega),
        State.readReg_writeReg_self, hr8]
    · rw [State.readReg_writeReg_self, hr9]
  · intro reg hk hc hy hg
    rw [State.readReg_writeReg_ne s₃ hg, State.readReg_writeReg_ne s₂ hy,
      State.readReg_writeReg_ne s₁ hc, State.readReg_writeReg_ne s hk]

/-- Shift `k` sort slots `idx, ..., idx + k - 1` right by 1 to `idx + 1, ..., idx + k`. -/
def shiftRightSlotsCmd (p idx : ℕ) : ℕ → Cmd
  | 0 => .skip
  | k + 1 =>
    .seq (shiftRightSlotsCmd p (idx + 1) k)
      (copySortSlotCmd p idx (idx + 1))

theorem shiftRightSlotsCmd_free (p : ℕ) :
    ∀ k idx : ℕ, (shiftRightSlotsCmd p idx k).IsLoopAllocFree
  | 0, _ => trivial
  | k + 1, idx => ⟨shiftRightSlotsCmd_free p k (idx + 1), copySortSlotCmd_free p idx (idx + 1)⟩

theorem shiftRightSlotsCmd_exec {w p r : ℕ} (hp0 : 0 < p) (x : Alg74Input p r)
    (hh1 : 1 ≤ x.h) (hw_h : x.h + 1 < 2 ^ w) (hw_p : p < 2 ^ w) (B : ℕ) :
    ∀ (L : List (Fin (alg74NumTerms p))) (idx : ℕ) (s : State),
      (∀ j : Fin L.length, SortSlotHolds hp0 x B s (idx + j.1) (L[j.1]'j.2)) →
      ∃ s' t, Exec w (shiftRightSlotsCmd p idx L.length) s s' t ∧
        s'.arr = s.arr ∧
        (∀ j : Fin L.length, SortSlotHolds hp0 x B s' (idx + 1 + j.1) (L[j.1]'j.2)) ∧
        (∀ reg : Reg, reg < regSortBase p + 4 * (idx + 1) → s'.readReg reg = s.readReg reg)
  | [], idx, s, _ => by
    refine ⟨s, 1, Exec.skip s, rfl, ?_, fun _ _ => rfl⟩
    intro j; exact Fin.elim0 j
  | b :: bs, idx, s, hslots => by
    have hbs : ∀ j : Fin bs.length, SortSlotHolds hp0 x B s (idx + 1 + j.1) (bs[j.1]'j.2) := by
      intro j
      have h := hslots ⟨j.1 + 1, by simp [j.2]⟩
      have hidx : idx + (j.1 + 1) = idx + 1 + j.1 := by omega
      simpa [hidx] using h
    rcases shiftRightSlotsCmd_exec hp0 x hh1 hw_h hw_p B bs (idx + 1) s hbs with
      ⟨s₁, t₁, h1, harr₁, hbs₁, hpres₁⟩
    have hb_s : SortSlotHolds hp0 x B s idx b := by
      simpa using hslots ⟨0, by simp⟩
    have hb_s₁ : SortSlotHolds hp0 x B s₁ idx b :=
      sortSlotHolds_congr hb_s
        (hpres₁ _ (by dsimp [regSortKey, regSortBase, Reg]; omega))
        (hpres₁ _ (by dsimp [regSortC, regSortBase, Reg]; omega))
        (hpres₁ _ (by dsimp [regSortY, regSortBase, Reg]; omega))
        (hpres₁ _ (by dsimp [regSortG, regSortBase, Reg]; omega))
    rcases copySortSlotCmd_exec hp0 x hh1 hw_h hw_p B idx (idx + 1) (by omega) b s₁ hb_s₁ with
      ⟨s₂, t₂, h2, harr₂, hb₂, hother₂⟩
    refine ⟨s₂, t₁ + t₂, Exec.seq h1 h2, harr₂.trans harr₁, ?_, ?_⟩
    · intro j
      rcases j with ⟨j, hj⟩
      cases j with
      | zero =>
        simpa using hb₂
      | succ j' =>
        have hj' : j' < bs.length := by simp at hj; omega
        have hprev := hbs₁ ⟨j', hj'⟩
        have hidx : idx + 1 + (j' + 1) = idx + 1 + 1 + j' := by omega
        rw [hidx]
        refine sortSlotHolds_congr hprev
          (hother₂ _
            (by dsimp [regSortKey, regSortBase, Reg]; omega)
            (by dsimp [regSortKey, regSortC, regSortBase, Reg]; omega)
            (by dsimp [regSortKey, regSortY, regSortBase, Reg]; omega)
            (by dsimp [regSortKey, regSortG, regSortBase, Reg]; omega))
          (hother₂ _
            (by dsimp [regSortC, regSortKey, regSortBase, Reg]; omega)
            (by dsimp [regSortC, regSortBase, Reg]; omega)
            (by dsimp [regSortC, regSortY, regSortBase, Reg]; omega)
            (by dsimp [regSortC, regSortG, regSortBase, Reg]; omega))
          (hother₂ _
            (by dsimp [regSortY, regSortKey, regSortBase, Reg]; omega)
            (by dsimp [regSortY, regSortC, regSortBase, Reg]; omega)
            (by dsimp [regSortY, regSortBase, Reg]; omega)
            (by dsimp [regSortY, regSortG, regSortBase, Reg]; omega))
          (hother₂ _
            (by dsimp [regSortG, regSortKey, regSortBase, Reg]; omega)
            (by dsimp [regSortG, regSortC, regSortBase, Reg]; omega)
            (by dsimp [regSortG, regSortY, regSortBase, Reg]; omega)
            (by dsimp [regSortG, regSortBase, Reg]; omega))
    · intro reg hlt
      rw [hother₂ reg
        (by dsimp [regSortKey, regSortBase, Reg] at *; omega)
        (by dsimp [regSortC, regSortBase, Reg] at *; omega)
        (by dsimp [regSortY, regSortBase, Reg] at *; omega)
        (by dsimp [regSortG, regSortBase, Reg] at *; omega),
        hpres₁ reg (by dsimp [regSortBase, Reg] at *; omega)]

/-- Insert the element `(r_6, r_7, r_8, r_9)` into the `len` slots starting at `idx`. -/
def orderedInsertCmd (p idx : ℕ) : ℕ → Cmd
  | 0 => writeScratchToSlotCmd p idx
  | len + 1 =>
    .ite (exprLe (.reg (regSortKey p idx)) (.reg 6))
      (.seq (shiftRightSlotsCmd p idx (len + 1))
        (writeScratchToSlotCmd p idx))
      (orderedInsertCmd p (idx + 1) len)

theorem orderedInsertCmd_free (p : ℕ) :
    ∀ len idx : ℕ, (orderedInsertCmd p idx len).IsLoopAllocFree
  | 0, idx => writeScratchToSlotCmd_free p idx
  | len + 1, idx =>
    ⟨⟨shiftRightSlotsCmd_free p (len + 1) idx, writeScratchToSlotCmd_free p idx⟩,
     orderedInsertCmd_free p len (idx + 1)⟩

/-- Decreasing sort key relation on terminals. -/
abbrev termOrderRel {p r : ℕ} (x : Alg74Input p r) (B : ℕ)
    (u v : Fin (alg74NumTerms p)) : Prop :=
  termSortKey x.h B (alg74Term x v) ≤ termSortKey x.h B (alg74Term x u)

theorem orderedInsertCmd_exec {w p r : ℕ} (hp0 : 0 < p) (x : Alg74Input p r)
    (hh1 : 1 ≤ x.h) (hw1 : 1 < 2 ^ w) (hw_h : x.h + 1 < 2 ^ w) (hw_p : p < 2 ^ w)
    (B : ℕ) (a : Fin (alg74NumTerms p)) :
    ∀ (L : List (Fin (alg74NumTerms p))) (idx : ℕ) (s : State),
      s.readReg 6 = termSortKey x.h B (alg74Term x a) →
      s.readReg 7 = (alg74Term x a).1 →
      s.readReg 8 = (alg74Term x a).2 →
      s.readReg 9 =
        (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p)
          (alg74RawColor p a)).1 →
      (∀ j : Fin L.length, SortSlotHolds hp0 x B s (idx + j.1) (L[j.1]'j.2)) →
      ∃ s' t, Exec w (orderedInsertCmd p idx L.length) s s' t ∧
        s'.arr = s.arr ∧
        (∀ j : Fin (List.orderedInsert (termOrderRel x B) a L).length,
          SortSlotHolds hp0 x B s' (idx + j.1)
            ((List.orderedInsert (termOrderRel x B) a L)[j.1]'j.2)) ∧
        (∀ reg : Reg, reg < regSortBase p + 4 * idx → s'.readReg reg = s.readReg reg)
  | [], idx, s, hr6, hr7, hr8, hr9, _ => by
    rcases writeScratchToSlotCmd_exec hp0 x hh1 hw_h hw_p B idx a s hr6 hr7 hr8 hr9 with
      ⟨s', t, h, harr, hslot, hother⟩
    refine ⟨s', t, h, harr, ?_, ?_⟩
    · intro j
      rcases j with ⟨j, hj⟩
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      simpa using hslot
    · intro reg hlt
      exact hother reg
        (by dsimp [regSortKey, regSortBase, Reg] at *; omega)
        (by dsimp [regSortC, regSortBase, Reg] at *; omega)
        (by dsimp [regSortY, regSortBase, Reg] at *; omega)
        (by dsimp [regSortG, regSortBase, Reg] at *; omega)
  | b :: bs, idx, s, hr6, hr7, hr8, hr9, hslots => by
    have hb_slot : SortSlotHolds hp0 x B s idx b := by
      simpa using hslots ⟨0, by simp⟩
    have hkb_le := termSortKey_le x hh1 B b
    have hka_le := termSortKey_le x hh1 B a
    have hkb_w : termSortKey x.h B (alg74Term x b) < 2 ^ w := by omega
    have hka_w : termSortKey x.h B (alg74Term x a) < 2 ^ w := by omega
    have hev_le :
        (exprLe (.reg (regSortKey p idx)) (.reg 6)).eval w s =
        some (if termOrderRel x B a b then 1 else 0) :=
      eval_exprLe hw1 (eval_reg hb_slot.1 hkb_w) (eval_reg hr6 hka_w)
    by_cases hle : termOrderRel x B a b
    · simp only [hle, ↓reduceIte] at hev_le
      rcases shiftRightSlotsCmd_exec hp0 x hh1 hw_h hw_p B (b :: bs) idx s hslots with
        ⟨s₁, t₁, h1, harr₁, hshift, hpres₁⟩
      have hr6_1 : s₁.readReg 6 = termSortKey x.h B (alg74Term x a) := by
        rw [hpres₁ 6 (by dsimp [regSortBase, Reg]; omega), hr6]
      have hr7_1 : s₁.readReg 7 = (alg74Term x a).1 := by
        rw [hpres₁ 7 (by dsimp [regSortBase, Reg]; omega), hr7]
      have hr8_1 : s₁.readReg 8 = (alg74Term x a).2 := by
        rw [hpres₁ 8 (by dsimp [regSortBase, Reg]; omega), hr8]
      have hr9_1 : s₁.readReg 9 =
          (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p)
            (alg74RawColor p a)).1 := by
        rw [hpres₁ 9 (by dsimp [regSortBase, Reg]; omega), hr9]
      rcases writeScratchToSlotCmd_exec hp0 x hh1 hw_h hw_p B idx a s₁ hr6_1 hr7_1 hr8_1 hr9_1 with
        ⟨s₂, t₂, h2, harr₂, ha_slot, hother₂⟩
      refine ⟨s₂, _, Exec.ite_true hev_le (by omega) (Exec.seq h1 h2), harr₂.trans harr₁, ?_, ?_⟩
      · have hins : List.orderedInsert (termOrderRel x B) a (b :: bs) = a :: b :: bs := by
          rw [List.orderedInsert_cons, if_pos hle]
        simp only [hins]
        intro j
        rcases j with ⟨j, hj⟩
        cases j with
        | zero =>
          simpa using ha_slot
        | succ j' =>
          have hlen : (List.orderedInsert (termOrderRel x B) a (b :: bs)).length =
              (b :: bs).length + 1 := by
            rw [hins, List.length_cons]
          have hj' : j' < (b :: bs).length := by omega
          have hprev := hshift ⟨j', hj'⟩
          have hidx : idx + (j' + 1) = idx + 1 + j' := by omega
          simp only [List.getElem_cons_succ, hidx]
          refine sortSlotHolds_congr hprev
            (hother₂ _
              (by dsimp [regSortKey, regSortBase, Reg]; omega)
              (by dsimp [regSortKey, regSortC, regSortBase, Reg]; omega)
              (by dsimp [regSortKey, regSortY, regSortBase, Reg]; omega)
              (by dsimp [regSortKey, regSortG, regSortBase, Reg]; omega))
            (hother₂ _
              (by dsimp [regSortC, regSortKey, regSortBase, Reg]; omega)
              (by dsimp [regSortC, regSortBase, Reg]; omega)
              (by dsimp [regSortC, regSortY, regSortBase, Reg]; omega)
              (by dsimp [regSortC, regSortG, regSortBase, Reg]; omega))
            (hother₂ _
              (by dsimp [regSortY, regSortKey, regSortBase, Reg]; omega)
              (by dsimp [regSortY, regSortC, regSortBase, Reg]; omega)
              (by dsimp [regSortY, regSortBase, Reg]; omega)
              (by dsimp [regSortY, regSortG, regSortBase, Reg]; omega))
            (hother₂ _
              (by dsimp [regSortG, regSortKey, regSortBase, Reg]; omega)
              (by dsimp [regSortG, regSortC, regSortBase, Reg]; omega)
              (by dsimp [regSortG, regSortY, regSortBase, Reg]; omega)
              (by dsimp [regSortG, regSortBase, Reg]; omega))
      · intro reg hlt
        rw [hother₂ reg
          (by dsimp [regSortKey, regSortBase, Reg] at *; omega)
          (by dsimp [regSortC, regSortBase, Reg] at *; omega)
          (by dsimp [regSortY, regSortBase, Reg] at *; omega)
          (by dsimp [regSortG, regSortBase, Reg] at *; omega),
          hpres₁ reg (by dsimp [regSortBase, Reg] at *; omega)]
    · simp only [hle, ↓reduceIte] at hev_le
      have hbs : ∀ j : Fin bs.length, SortSlotHolds hp0 x B s (idx + 1 + j.1) (bs[j.1]'j.2) := by
        intro j
        have h := hslots ⟨j.1 + 1, by simp [j.2]⟩
        have hidx : idx + (j.1 + 1) = idx + 1 + j.1 := by omega
        simpa [hidx] using h
      rcases orderedInsertCmd_exec hp0 x hh1 hw1 hw_h hw_p B a bs (idx + 1) s
          hr6 hr7 hr8 hr9 hbs with
        ⟨s₁, t₁, h1, harr₁, hbs', hpres₁⟩
      refine ⟨s₁, _, Exec.ite_false hev_le h1, harr₁, ?_, ?_⟩
      · have hins : List.orderedInsert (termOrderRel x B) a (b :: bs) =
            b :: List.orderedInsert (termOrderRel x B) a bs := by
          rw [List.orderedInsert_cons, if_neg hle]
        simp only [hins]
        intro j
        rcases j with ⟨j, hj⟩
        cases j with
        | zero =>
          simp only [Nat.add_zero, List.getElem_cons_zero]
          exact sortSlotHolds_congr hb_slot
            (hpres₁ _ (by dsimp [regSortKey, regSortBase, Reg]; omega))
            (hpres₁ _ (by dsimp [regSortC, regSortBase, Reg]; omega))
            (hpres₁ _ (by dsimp [regSortY, regSortBase, Reg]; omega))
            (hpres₁ _ (by dsimp [regSortG, regSortBase, Reg]; omega))
        | succ j' =>
          have hlen : (List.orderedInsert (termOrderRel x B) a (b :: bs)).length =
              (List.orderedInsert (termOrderRel x B) a bs).length + 1 := by
            rw [hins, List.length_cons]
          have hj' : j' < (List.orderedInsert (termOrderRel x B) a bs).length := by omega
          have hprev := hbs' ⟨j', hj'⟩
          have hidx : idx + (j' + 1) = idx + 1 + j' := by omega
          simpa [hidx] using hprev
      · intro reg hlt
        exact hpres₁ reg (by dsimp [regSortBase, Reg] at *; omega)

/-- Load terminal `a`'s 4-tuple `(key, c, y, g)` into `(r_6, r_7, r_8, r_9)`. -/
def loadTermToScratchCmd (p : ℕ) (a : Fin (alg74NumTerms p)) : Cmd :=
  .seq (.assign 7 (.reg (regTermC p a.1)))
    (.seq (.assign 8 (.reg (regTermY p a.1)))
      (.seq (.assign 9 (.reg (regPermColor p (alg74RawColor p a).1)))
        (.ite (inInnerBoxExpr (.reg 3) (.reg 15) (.reg 7) (.reg 8))
          (.assign 6 (.op .add (.reg 8) (.const 1)))
          (.assign 6 (.const 0)))))

theorem loadTermToScratchCmd_free (p : ℕ) (a : Fin (alg74NumTerms p)) :
    (loadTermToScratchCmd p a).IsLoopAllocFree := by
  dsimp [loadTermToScratchCmd, Cmd.IsLoopAllocFree]
  trivial

theorem loadTermToScratchCmd_exec {w p r : ℕ} (hp0 : 0 < p) (x : Alg74Input p r)
    (hh1 : 1 ≤ x.h)
    (hw1 : 1 < 2 ^ w)
    (hw_h : x.h + 1 < 2 ^ w)
    (hw_p : p < 2 ^ w)
    (B : ℕ) (hw_B : B < 2 ^ w)
    (a : Fin (alg74NumTerms p)) (s : State)
    (hr3 : s.readReg 3 = x.h)
    (hr15 : s.readReg 15 = B)
    (hc : s.readReg (regTermC p a.1) = (alg74Term x a).1)
    (hy : s.readReg (regTermY p a.1) = (alg74Term x a).2)
    (hg : s.readReg (regPermColor p (alg74RawColor p a).1) =
      (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p)
        (alg74RawColor p a)).1) :
    ∃ s' t, Exec w (loadTermToScratchCmd p a) s s' t ∧
      s'.arr = s.arr ∧
      s'.readReg 6 = termSortKey x.h B (alg74Term x a) ∧
      s'.readReg 7 = (alg74Term x a).1 ∧
      s'.readReg 8 = (alg74Term x a).2 ∧
      s'.readReg 9 =
        (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p)
          (alg74RawColor p a)).1 ∧
      (∀ reg : Reg, reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 9 →
        s'.readReg reg = s.readReg reg) := by
  have hw0 : 0 < 2 ^ w := by omega
  have hb := alg74Term_bounds x hh1 a
  have hc_w : (alg74Term x a).1 < 2 ^ w := by omega
  have hy_w : (alg74Term x a).2 < 2 ^ w := by omega
  have hperm_w : (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p)
      (alg74RawColor p a)).1 < 2 ^ w := by
    have := (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p)
      (alg74RawColor p a)).2
    omega
  have h1 : Exec w (.assign 7 (.reg (regTermC p a.1))) s
      (s.writeReg 7 (alg74Term x a).1) ((Expr.reg (regTermC p a.1)).cost + 1) := by
    apply Exec.assign
    simp [Expr.eval, State.readReg] at hc ⊢
    simp [hc, hc_w]
  let s₁ := s.writeReg 7 (alg74Term x a).1
  have hs₁_y : s₁.readReg (regTermY p a.1) = (alg74Term x a).2 := by
    rw [State.readReg_writeReg_ne s (by dsimp [regTermY, Reg]; omega), hy]
  have h2 : Exec w (.assign 8 (.reg (regTermY p a.1))) s₁
      (s₁.writeReg 8 (alg74Term x a).2) ((Expr.reg (regTermY p a.1)).cost + 1) := by
    apply Exec.assign
    simp [Expr.eval, State.readReg] at hs₁_y ⊢
    simp [hs₁_y, hy_w]
  let s₂ := s₁.writeReg 8 (alg74Term x a).2
  have hs₂_g : s₂.readReg (regPermColor p (alg74RawColor p a).1) =
      (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p)
        (alg74RawColor p a)).1 := by
    rw [State.readReg_writeReg_ne s₁ (by dsimp [regPermColor, Reg]; omega),
      State.readReg_writeReg_ne s (by dsimp [regPermColor, Reg]; omega), hg]
  have h3 : Exec w (.assign 9 (.reg (regPermColor p (alg74RawColor p a).1))) s₂
      (s₂.writeReg 9 (s₂.readReg (regPermColor p (alg74RawColor p a).1)))
      ((Expr.reg (regPermColor p (alg74RawColor p a).1)).cost + 1) := by
    apply Exec.assign
    have hgw : s₂.readReg (regPermColor p (alg74RawColor p a).1) < 2 ^ w := by
      rw [hs₂_g]; exact hperm_w
    simp [Expr.eval, State.readReg] at hgw ⊢
    exact hgw
  let s₃ := s₂.writeReg 9 (s₂.readReg (regPermColor p (alg74RawColor p a).1))
  have hs₃_3 : s₃.readReg 3 = x.h := by
    rw [State.readReg_writeReg_ne s₂ (by decide), State.readReg_writeReg_ne s₁ (by decide),
      State.readReg_writeReg_ne s (by decide), hr3]
  have hs₃_15 : s₃.readReg 15 = B := by
    rw [State.readReg_writeReg_ne s₂ (by decide), State.readReg_writeReg_ne s₁ (by decide),
      State.readReg_writeReg_ne s (by decide), hr15]
  have hs₃_7 : s₃.readReg 7 = (alg74Term x a).1 := by
    rw [State.readReg_writeReg_ne s₂ (by decide), State.readReg_writeReg_ne s₁ (by decide),
      State.readReg_writeReg_self]
  have hs₃_8 : s₃.readReg 8 = (alg74Term x a).2 := by
    rw [State.readReg_writeReg_ne s₂ (by decide), State.readReg_writeReg_self]
  have hh_w : x.h < 2 ^ w := by omega
  have hev_box :
      (inInnerBoxExpr (.reg 3) (.reg 15) (.reg 7) (.reg 8)).eval w s₃ =
      some (if IsInInnerBox x.h B (alg74Term x a) then 1 else 0) :=
    eval_inInnerBoxExpr hw1
      (eval_reg hs₃_3 hh_w)
      (eval_reg hs₃_15 hw_B)
      (eval_reg hs₃_7 hc_w)
      (eval_reg hs₃_8 hy_w)
  by_cases hbox : IsInInnerBox x.h B (alg74Term x a)
  · simp only [hbox, ↓reduceIte] at hev_box
    have hy1_w : (alg74Term x a).2 + 1 < 2 ^ w := by omega
    have htr : Exec w (.assign 6 (.op .add (.reg 8) (.const 1))) s₃
        (s₃.writeReg 6 ((alg74Term x a).2 + 1))
        ((Expr.op .add (.reg 8) (.const 1)).cost + 1) := by
      apply Exec.assign
      simp [Expr.eval, State.readReg] at hs₃_8 ⊢
      simp [hs₃_8, hy_w, hw1, BinOp.eval, BinOp.raw, hy1_w]
    let s₄ := s₃.writeReg 6 ((alg74Term x a).2 + 1)
    refine ⟨s₄, _, Exec.seq h1 (Exec.seq h2 (Exec.seq h3 (Exec.ite_true hev_box (by omega) htr))),
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [State.readReg_writeReg_self]; unfold termSortKey; simp [hbox]
    · rw [State.readReg_writeReg_ne s₃ (by decide), hs₃_7]
    · rw [State.readReg_writeReg_ne s₃ (by decide), hs₃_8]
    · rw [State.readReg_writeReg_ne s₃ (by decide), State.readReg_writeReg_self, hs₂_g]
    · intro reg h6 h7 h8 h9
      rw [State.readReg_writeReg_ne s₃ h6, State.readReg_writeReg_ne s₂ h9,
        State.readReg_writeReg_ne s₁ h8, State.readReg_writeReg_ne s h7]
  · simp only [hbox, ↓reduceIte] at hev_box
    have hfl : Exec w (.assign 6 (.const 0)) s₃ (s₃.writeReg 6 0) ((Expr.const 0).cost + 1) :=
      Exec.assign (by simp [Expr.eval, hw0])
    let s₄ := s₃.writeReg 6 0
    refine ⟨s₄, _, Exec.seq h1 (Exec.seq h2 (Exec.seq h3 (Exec.ite_false hev_box hfl))),
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [State.readReg_writeReg_self]; unfold termSortKey; simp [hbox]
    · rw [State.readReg_writeReg_ne s₃ (by decide), hs₃_7]
    · rw [State.readReg_writeReg_ne s₃ (by decide), hs₃_8]
    · rw [State.readReg_writeReg_ne s₃ (by decide), State.readReg_writeReg_self, hs₂_g]
    · intro reg h6 h7 h8 h9
      rw [State.readReg_writeReg_ne s₃ h6, State.readReg_writeReg_ne s₂ h9,
        State.readReg_writeReg_ne s₁ h8, State.readReg_writeReg_ne s h7]

/-- Unrolled insertion sort of `xs : List (Fin (alg74NumTerms p))` into slots `0 .. xs.length - 1`. -/
def insertionSortLoop (p : ℕ) : List (Fin (alg74NumTerms p)) → Cmd
  | [] => .skip
  | a :: rest =>
    .seq (insertionSortLoop p rest)
      (.seq (loadTermToScratchCmd p a)
        (orderedInsertCmd p 0 rest.length))

theorem insertionSortLoop_free (p : ℕ) :
    ∀ xs : List (Fin (alg74NumTerms p)), (insertionSortLoop p xs).IsLoopAllocFree
  | [] => trivial
  | a :: rest =>
    ⟨insertionSortLoop_free p rest,
     loadTermToScratchCmd_free p a,
     orderedInsertCmd_free p rest.length 0⟩

theorem insertionSortLoop_exec {w p r : ℕ} (hp0 : 0 < p) (x : Alg74Input p r)
    (hh1 : 1 ≤ x.h)
    (hw1 : 1 < 2 ^ w)
    (hw_h : x.h + 1 < 2 ^ w)
    (hw_p : p < 2 ^ w)
    (B : ℕ) (hw_B : B < 2 ^ w) :
    ∀ (xs : List (Fin (alg74NumTerms p))) (s : State),
      s.readReg 3 = x.h →
      s.readReg 15 = B →
      (∀ a : Fin (alg74NumTerms p),
        s.readReg (regTermC p a.1) = (alg74Term x a).1 ∧
        s.readReg (regTermY p a.1) = (alg74Term x a).2) →
      (∀ g : Fin p,
        s.readReg (regPermColor p g.1) =
          (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p) g).1) →
      ∃ s' t, Exec w (insertionSortLoop p xs) s s' t ∧
        s'.arr = s.arr ∧
        (∀ j : Fin (xs.insertionSort (termOrderRel x B)).length,
          SortSlotHolds hp0 x B s' j.1
            ((xs.insertionSort (termOrderRel x B))[j.1]'j.2)) ∧
        (∀ reg : Reg, reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 9 →
          reg < regSortBase p → s'.readReg reg = s.readReg reg)
  | [], s, _, _, _, _ => by
    refine ⟨s, 1, Exec.skip s, rfl, ?_, fun _ _ _ _ _ _ => rfl⟩
    intro j
    have hj0 := j.2
    simp at hj0
  | a :: rest, s, hr3, hr15, htermC, hperm => by
    rcases insertionSortLoop_exec hp0 x hh1 hw1 hw_h hw_p B hw_B rest s hr3 hr15 htermC hperm with
      ⟨s₁, t₁, h1, harr₁, hslots₁, hpres₁⟩
    have hr3_1 : s₁.readReg 3 = x.h := by
      rw [hpres₁ 3 (by decide) (by decide) (by decide) (by decide)
        (by dsimp [regSortBase, Reg]; omega), hr3]
    have hr15_1 : s₁.readReg 15 = B := by
      rw [hpres₁ 15 (by decide) (by decide) (by decide) (by decide)
        (by dsimp [regSortBase, Reg]; omega), hr15]
    have ha_lt : a.1 < alg74NumTerms p := a.2
    have hc_1 : s₁.readReg (regTermC p a.1) = (alg74Term x a).1 := by
      rw [hpres₁ (regTermC p a.1)
        (by dsimp [regTermC, Reg]; omega)
        (by dsimp [regTermC, Reg]; omega)
        (by dsimp [regTermC, Reg]; omega)
        (by dsimp [regTermC, Reg]; omega)
        (by dsimp [regTermC, regSortBase, Reg]; omega), (htermC a).1]
    have hy_1 : s₁.readReg (regTermY p a.1) = (alg74Term x a).2 := by
      rw [hpres₁ (regTermY p a.1)
        (by dsimp [regTermY, Reg]; omega)
        (by dsimp [regTermY, Reg]; omega)
        (by dsimp [regTermY, Reg]; omega)
        (by dsimp [regTermY, Reg]; omega)
        (by dsimp [regTermY, regSortBase, Reg]; omega), (htermC a).2]
    let g_a := alg74RawColor p a
    have hg_lt : g_a.1 < p := g_a.2
    have hg_1 : s₁.readReg (regPermColor p g_a.1) =
        (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p) g_a).1 := by
      rw [hpres₁ (regPermColor p g_a.1)
        (by dsimp [regPermColor, Reg]; omega)
        (by dsimp [regPermColor, Reg]; omega)
        (by dsimp [regPermColor, Reg]; omega)
        (by dsimp [regPermColor, Reg]; omega)
        (by dsimp [regPermColor, regSortBase, Reg]; omega), hperm g_a]
    rcases loadTermToScratchCmd_exec hp0 x hh1 hw1 hw_h hw_p B hw_B a s₁
        hr3_1 hr15_1 hc_1 hy_1 hg_1 with
      ⟨s₂, t₂, h2, harr₂, hr6_2, hr7_2, hr8_2, hr9_2, hother₂⟩
    let L_rest := rest.insertionSort (termOrderRel x B)
    have hlen_rest : L_rest.length = rest.length := List.length_insertionSort _ rest
    have hslots₂ : ∀ j : Fin L_rest.length, SortSlotHolds hp0 x B s₂ (0 + j.1) (L_rest[j.1]'j.2) := by
      intro j
      simp only [Nat.zero_add]
      refine sortSlotHolds_congr (hslots₁ j)
        (hother₂ _ (by dsimp [regSortKey, regSortBase, Reg]; omega)
          (by dsimp [regSortKey, regSortBase, Reg]; omega)
          (by dsimp [regSortKey, regSortBase, Reg]; omega)
          (by dsimp [regSortKey, regSortBase, Reg]; omega))
        (hother₂ _ (by dsimp [regSortC, regSortBase, Reg]; omega)
          (by dsimp [regSortC, regSortBase, Reg]; omega)
          (by dsimp [regSortC, regSortBase, Reg]; omega)
          (by dsimp [regSortC, regSortBase, Reg]; omega))
        (hother₂ _ (by dsimp [regSortY, regSortBase, Reg]; omega)
          (by dsimp [regSortY, regSortBase, Reg]; omega)
          (by dsimp [regSortY, regSortBase, Reg]; omega)
          (by dsimp [regSortY, regSortBase, Reg]; omega))
        (hother₂ _ (by dsimp [regSortG, regSortBase, Reg]; omega)
          (by dsimp [regSortG, regSortBase, Reg]; omega)
          (by dsimp [regSortG, regSortBase, Reg]; omega)
          (by dsimp [regSortG, regSortBase, Reg]; omega))
    rcases orderedInsertCmd_exec hp0 x hh1 hw1 hw_h hw_p B a L_rest 0 s₂
        hr6_2 hr7_2 hr8_2 hr9_2 hslots₂ with
      ⟨s₃, t₃, h3, harr₃, hslots₃, hpres₃⟩
    rw [hlen_rest] at h3
    refine ⟨s₃, t₁ + (t₂ + t₃), Exec.seq h1 (Exec.seq h2 h3),
      harr₃.trans (harr₂.trans harr₁), ?_, ?_⟩
    · intro j
      have hj := hslots₃ ⟨j.1, by simpa [List.insertionSort_cons, L_rest] using j.2⟩
      simpa [List.insertionSort_cons, L_rest] using hj
    · intro reg h6 h7 h8 h9 hlt
      rw [hpres₃ reg (by dsimp [regSortBase, Reg] at *; omega),
        hother₂ reg h6 h7 h8 h9, hpres₁ reg h6 h7 h8 h9 hlt]

/-- Sort all `m = alg74NumTerms p` terminals in decreasing order of `termSortKey`. -/
def insertionSortTermsCmd (p : ℕ) : Cmd :=
  insertionSortLoop p (List.finRange (alg74NumTerms p))

theorem insertionSortTermsCmd_free (p : ℕ) :
    (insertionSortTermsCmd p).IsLoopAllocFree :=
  insertionSortLoop_free p _

/-! #### Sub-step 4e: Computing Greedy Safe Columns (`computeSafeColsCmd`) -/

/-- Expression testing `x ∈ endpointWindow p c cStar`. -/
def inEndpointWindowExpr (p : ℕ) (e_c e_cStar e_x : Expr) : Expr :=
  exprOr
    (exprAnd (exprLe e_c (.op .add e_x (.const (2 * p)))) (exprLe e_x e_c))
    (exprAnd (exprLe e_cStar e_x) (exprLe e_x (.op .add e_cStar (.const (2 * p)))))

theorem eval_inEndpointWindowExpr {w p : ℕ} {s : State} {e_c e_cStar e_x : Expr} {vc vcStar vx : ℕ}
    (hw2 : 2 < 2 ^ w)
    (hw_2p : 2 * p < 2 ^ w)
    (hw_add1 : vx + 2 * p < 2 ^ w)
    (hw_add2 : vcStar + 2 * p < 2 ^ w)
    (hc : e_c.eval w s = some vc)
    (hcStar : e_cStar.eval w s = some vcStar)
    (hx : e_x.eval w s = some vx) :
    (inEndpointWindowExpr p e_c e_cStar e_x).eval w s =
      some (if vx ∈ endpointWindow p vc vcStar then 1 else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hadd1 : (Expr.op .add e_x (.const (2 * p))).eval w s = some (vx + 2 * p) := by
    simp [Expr.eval, hx, BinOp.eval, BinOp.raw, checkWord, hw_2p, hw_add1]
  have hadd2 : (Expr.op .add e_cStar (.const (2 * p))).eval w s = some (vcStar + 2 * p) := by
    simp [Expr.eval, hcStar, BinOp.eval, BinOp.raw, checkWord, hw_2p, hw_add2]
  unfold inEndpointWindowExpr
  rw [eval_exprOr hw2
    (eval_exprAnd hw1 (eval_exprLe hw1 hc hadd1) (eval_exprLe hw1 hx hc))
    (eval_exprAnd hw1 (eval_exprLe hw1 hcStar hx) (eval_exprLe hw1 hx hadd2))]
  congr 1
  exact if_congr (mem_endpointWindow_iff p vc vcStar vx).symm rfl rfl

/-- Expression testing `x ∈ forbidAfter p c k` using `regSortC p j` and `regSafeC p j` for `j ≤ k`. -/
def inForbidAfterExpr (p k : ℕ) (e_x : Expr) : Expr :=
  exprAny (List.range (k + 1)) (fun j =>
    inEndpointWindowExpr p (.reg (regSortC p j)) (.reg (regSafeC p j)) e_x)

theorem eval_inForbidAfterExpr {w p : ℕ} {s : State} {c : ℕ → ℕ} {k vx : ℕ} {e_x : Expr}
    (hw2 : 2 < 2 ^ w)
    (hw_2p : 2 * p < 2 ^ w)
    (hw_vx : vx + 2 * p < 2 ^ w)
    (hw_c : ∀ j ≤ k, c j < 2 ^ w)
    (hw_cStar : ∀ j ≤ k, safeCol p c j + 2 * p < 2 ^ w)
    (hsortC : ∀ j ≤ k, s.readReg (regSortC p j) = c j)
    (hsafeC : ∀ j ≤ k, s.readReg (regSafeC p j) = safeCol p c j)
    (hx : e_x.eval w s = some vx) :
    (inForbidAfterExpr p k e_x).eval w s =
      some (if vx ∈ forbidAfter p c k then 1 else 0) := by
  unfold inForbidAfterExpr
  rw [eval_exprAny (List.range (k + 1)) _
    (fun j => vx ∈ endpointWindow p (c j) (safeCol p c j)) hw2]
  · congr 1
    apply if_congr _ rfl rfl
    rw [mem_forbidAfter_iff]
    simp only [List.mem_range, Nat.lt_succ_iff]
  · intro j hj
    have hj_le : j ≤ k := by simp only [List.mem_range] at hj; omega
    have hcj_w := hw_c j hj_le
    have hcs_w : safeCol p c j < 2 ^ w := by have := hw_cStar j hj_le; omega
    have hsc := hsortC j hj_le
    have hsf := hsafeC j hj_le
    exact eval_inEndpointWindowExpr hw2 hw_2p hw_vx (hw_cStar j hj_le)
      (by simp [Expr.eval, State.readReg] at hsc ⊢; simp [hsc, hcj_w])
      (by simp [Expr.eval, State.readReg] at hsf ⊢; simp [hsf, hcs_w])
      hx

/-- Single step of incrementing `regSafeC p (k + 1)` if it lies in `forbidAfter p c k`. -/
def bumpSafeColStepCmd (p k : ℕ) : Cmd :=
  .ite (inForbidAfterExpr p k (.reg (regSafeC p (k + 1))))
    (.assign (regSafeC p (k + 1)) (.op .add (.reg (regSafeC p (k + 1))) (.const 1)))
    .skip

theorem bumpSafeColStepCmd_free (p k : ℕ) :
    (bumpSafeColStepCmd p k).IsLoopAllocFree :=
  ⟨trivial, trivial⟩

/-- Repeat `bumpSafeColStepCmd p k` `t` times. -/
def repeatBumpCmd (p k : ℕ) : ℕ → Cmd
  | 0 => .skip
  | t + 1 => .seq (repeatBumpCmd p k t) (bumpSafeColStepCmd p k)

theorem repeatBumpCmd_free (p k : ℕ) :
    ∀ t : ℕ, (repeatBumpCmd p k t).IsLoopAllocFree
  | 0 => trivial
  | t + 1 => ⟨repeatBumpCmd_free p k t, bumpSafeColStepCmd_free p k⟩

theorem repeatBumpCmd_exec {w p : ℕ} {c : ℕ → ℕ} {k : ℕ}
    (hk_lt : k < alg74NumTerms p)
    (hw2 : 2 < 2 ^ w)
    (hw_2p : 2 * p < 2 ^ w)
    (hw_c : ∀ j ≤ k, c j < 2 ^ w)
    (hw_cStar : ∀ j ≤ k, safeCol p c j + 2 * p < 2 ^ w)
    (x₀ : ℕ) :
    ∀ (t : ℕ) (s : State),
      x₀ + t + 2 * p < 2 ^ w →
      s.readReg (regSafeC p (k + 1)) = x₀ →
      (∀ j ≤ k, s.readReg (regSortC p j) = c j) →
      (∀ j ≤ k, s.readReg (regSafeC p j) = safeCol p c j) →
      ∃ s' time, Exec w (repeatBumpCmd p k t) s s' time ∧
        s'.arr = s.arr ∧
        s'.readReg (regSafeC p (k + 1)) = (bumpForb (forbidAfter p c k))^[t] x₀ ∧
        (∀ reg : Reg, reg ≠ regSafeC p (k + 1) → s'.readReg reg = s.readReg reg)
  | 0, s, _, hx₀, _, _ => by
    refine ⟨s, 1, Exec.skip s, rfl, hx₀, fun _ _ => rfl⟩
  | t + 1, s, hw_xt, hx₀, hsortC, hsafeC => by
    have hw1 : 1 < 2 ^ w := by omega
    rcases repeatBumpCmd_exec hk_lt hw2 hw_2p hw_c hw_cStar x₀ t s (by omega) hx₀ hsortC hsafeC with
      ⟨s₁, time₁, h1, harr₁, hval₁, hother₁⟩
    let vt := (bumpForb (forbidAfter p c k))^[t] x₀
    change s₁.readReg (regSafeC p (k + 1)) = vt at hval₁
    have hvt_le_gen : ∀ m : ℕ, (bumpForb (forbidAfter p c k))^[m] x₀ ≤ x₀ + m := by
      intro m
      induction m with
      | zero => simp
      | succ m' ih =>
        rw [Function.iterate_succ_apply']
        dsimp only [bumpForb]
        split_ifs <;> omega
    have hvt_le : vt ≤ x₀ + t := hvt_le_gen t
    have hvt_w : vt < 2 ^ w := by omega
    have hvt1_w : vt + 1 < 2 ^ w := by omega
    have hsortC₁ : ∀ j ≤ k, s₁.readReg (regSortC p j) = c j := by
      intro j hj
      rw [hother₁ (regSortC p j) (by dsimp [regSortC, regSafeC, regSortBase, Reg]; omega),
        hsortC j hj]
    have hsafeC₁ : ∀ j ≤ k, s₁.readReg (regSafeC p j) = safeCol p c j := by
      intro j hj
      rw [hother₁ (regSafeC p j) (by dsimp [regSafeC, Reg]; omega), hsafeC j hj]
    have hev_forb :
        (inForbidAfterExpr p k (.reg (regSafeC p (k + 1)))).eval w s₁ =
        some (if vt ∈ forbidAfter p c k then 1 else 0) :=
      eval_inForbidAfterExpr hw2 hw_2p (by omega) hw_c hw_cStar hsortC₁ hsafeC₁
        (by simp [Expr.eval, State.readReg] at hval₁ ⊢; simp [hval₁, hvt_w])
    rw [Function.iterate_succ_apply']
    change ∃ s' time,
      Exec w (repeatBumpCmd p k (t + 1)) s s' time ∧
      s'.arr = s.arr ∧
      s'.readReg (regSafeC p (k + 1)) = (if vt ∈ forbidAfter p c k then vt + 1 else vt) ∧
      (∀ reg : Reg, reg ≠ regSafeC p (k + 1) → s'.readReg reg = s.readReg reg)
    by_cases hmem : vt ∈ forbidAfter p c k
    · simp only [hmem, ↓reduceIte] at hev_forb ⊢
      have htr : Exec w
          (.assign (regSafeC p (k + 1)) (.op .add (.reg (regSafeC p (k + 1))) (.const 1)))
          s₁ (s₁.writeReg (regSafeC p (k + 1)) (vt + 1))
          ((Expr.op .add (.reg (regSafeC p (k + 1))) (.const 1)).cost + 1) := by
        apply Exec.assign
        simp [Expr.eval, State.readReg] at hval₁ ⊢
        simp [hval₁, hvt_w, hw1, BinOp.eval, BinOp.raw, hvt1_w]
      refine ⟨s₁.writeReg (regSafeC p (k + 1)) (vt + 1), _,
        Exec.seq h1 (Exec.ite_true hev_forb (by omega) htr),
        harr₁, State.readReg_writeReg_self _ _ _, ?_⟩
      intro reg hne
      rw [State.readReg_writeReg_ne s₁ hne, hother₁ reg hne]
    · simp only [hmem, ↓reduceIte] at hev_forb ⊢
      refine ⟨s₁, _, Exec.seq h1 (Exec.ite_false hev_forb (Exec.skip s₁)),
        harr₁, hval₁, hother₁⟩

/-- Compute `regSafeC p i = safeCol p c i` for index `i`. -/
def computeOneSafeColCmd (p : ℕ) : ℕ → Cmd
  | 0 => .assign (regSafeC p 0) (.op .add (.reg (regSortC p 0)) (.const 1))
  | k + 1 =>
    .seq (.assign (regSafeC p (k + 1)) (.op .add (.reg (regSortC p (k + 1))) (.const 1)))
      (repeatBumpCmd p k ((k + 1) * (4 * p + 2)))

theorem computeOneSafeColCmd_free (p : ℕ) :
    ∀ i : ℕ, (computeOneSafeColCmd p i).IsLoopAllocFree
  | 0 => trivial
  | k + 1 => ⟨trivial, repeatBumpCmd_free p k _⟩

/-- Unrolled loop computing `regSafeC p 0, ..., regSafeC p (n - 1)`. -/
def computeSafeColsLoop (p : ℕ) : ℕ → Cmd
  | 0 => .skip
  | i + 1 => .seq (computeSafeColsLoop p i) (computeOneSafeColCmd p i)

theorem computeSafeColsLoop_free (p : ℕ) :
    ∀ n : ℕ, (computeSafeColsLoop p n).IsLoopAllocFree
  | 0 => trivial
  | i + 1 => ⟨computeSafeColsLoop_free p i, computeOneSafeColCmd_free p i⟩

theorem computeSafeColsLoop_exec {w p : ℕ} {c : ℕ → ℕ} {h : ℕ}
    (hw2 : 2 < 2 ^ w)
    (hc_le : ∀ j < alg74NumTerms p, c j ≤ h)
    (hw_bound : h + alg74BoxMarginConst p < 2 ^ w) :
    ∀ (n : ℕ), n ≤ alg74NumTerms p →
      ∀ (s : State),
        (∀ j < n, s.readReg (regSortC p j) = c j) →
        ∃ s' t, Exec w (computeSafeColsLoop p n) s s' t ∧
          s'.arr = s.arr ∧
          (∀ j < n, s'.readReg (regSafeC p j) = safeCol p c j) ∧
          (∀ reg : Reg, (∀ j < n, reg ≠ regSafeC p j) → s'.readReg reg = s.readReg reg)
  | 0, _, s, _ => by
    refine ⟨s, 1, Exec.skip s, rfl, ?_, fun _ _ => rfl⟩
    intro j hj; omega
  | i + 1, hi_le, s, hsortC => by
    have hw1 : 1 < 2 ^ w := by omega
    have hw_2p : 2 * p < 2 ^ w := by unfold alg74BoxMarginConst at hw_bound; omega
    rcases computeSafeColsLoop_exec hw2 hc_le hw_bound i (by omega) s
        (fun j hj => hsortC j (by omega)) with
      ⟨s₁, t₁, h1, harr₁, hsafe₁, hother₁⟩
    have hsortC₁ : ∀ j < i + 1, s₁.readReg (regSortC p j) = c j := by
      intro j hj
      rw [hother₁ (regSortC p j) (fun j' _ => by dsimp [regSortC, regSafeC, regSortBase, Reg]; omega),
        hsortC j hj]
    cases i with
    | zero =>
      have hc0 : c 0 ≤ h := hc_le 0 (by omega)
      have hc0_w : c 0 < 2 ^ w := by unfold alg74BoxMarginConst at hw_bound; omega
      have hc01_w : c 0 + 1 < 2 ^ w := by unfold alg74BoxMarginConst at hw_bound; omega
      have h2 : Exec w (.assign (regSafeC p 0) (.op .add (.reg (regSortC p 0)) (.const 1))) s₁
          (s₁.writeReg (regSafeC p 0) (c 0 + 1))
          ((Expr.op .add (.reg (regSortC p 0)) (.const 1)).cost + 1) := by
        apply Exec.assign
        have hs0 := hsortC₁ 0 (by omega)
        simp [Expr.eval, State.readReg] at hs0 ⊢
        simp [hs0, hc0_w, hw1, BinOp.eval, BinOp.raw, hc01_w]
      refine ⟨s₁.writeReg (regSafeC p 0) (c 0 + 1), _, Exec.seq h1 h2, harr₁, ?_, ?_⟩
      · intro j hj
        have hj0 : j = 0 := by omega
        subst hj0
        rw [State.readReg_writeReg_self, safeCol_zero]
      · intro reg hne
        rw [State.readReg_writeReg_ne s₁ (hne 0 (by omega)), hother₁ reg (fun j hj => by omega)]
    | succ k =>
      have hck : c (k + 1) ≤ h := hc_le (k + 1) (by omega)
      have hck_w : c (k + 1) < 2 ^ w := by unfold alg74BoxMarginConst at hw_bound; omega
      have hck1_w : c (k + 1) + 1 < 2 ^ w := by unfold alg74BoxMarginConst at hw_bound; omega
      have hinit : Exec w
          (.assign (regSafeC p (k + 1)) (.op .add (.reg (regSortC p (k + 1))) (.const 1))) s₁
          (s₁.writeReg (regSafeC p (k + 1)) (c (k + 1) + 1))
          ((Expr.op .add (.reg (regSortC p (k + 1))) (.const 1)).cost + 1) := by
        apply Exec.assign
        have hsk := hsortC₁ (k + 1) (by omega)
        simp [Expr.eval, State.readReg] at hsk ⊢
        simp [hsk, hck_w, hw1, BinOp.eval, BinOp.raw, hck1_w]
      let s₂ := s₁.writeReg (regSafeC p (k + 1)) (c (k + 1) + 1)
      have hsortC₂ : ∀ j ≤ k, s₂.readReg (regSortC p j) = c j := by
        intro j hj
        rw [State.readReg_writeReg_ne s₁ (by dsimp [regSortC, regSafeC, regSortBase, Reg]; omega),
          hsortC₁ j (by omega)]
      have hsafeC₂ : ∀ j ≤ k, s₂.readReg (regSafeC p j) = safeCol p c j := by
        intro j hj
        rw [State.readReg_writeReg_ne s₁ (by dsimp [regSafeC, Reg]; omega),
          hsafe₁ j (by omega)]
      have hw_c : ∀ j ≤ k, c j < 2 ^ w := by
        intro j hj
        have hcj := hc_le j (by omega)
        unfold alg74BoxMarginConst at hw_bound
        omega
      have hw_cStar : ∀ j ≤ k, safeCol p c j + 2 * p < 2 ^ w := by
        intro j hj
        have hb := (safeCol_bounds p c j).2
        have hcj := hc_le j (by omega)
        have hmul : j * (4 * p + 2) ≤ alg74NumTerms p * (4 * p + 2) :=
          Nat.mul_le_mul_right _ (by omega)
        unfold alg74BoxMarginConst at hw_bound
        omega
      have hw_xt : (c (k + 1) + 1) + (k + 1) * (4 * p + 2) + 2 * p < 2 ^ w := by
        have hmul : (k + 1) * (4 * p + 2) ≤ alg74NumTerms p * (4 * p + 2) :=
          Nat.mul_le_mul_right _ (by omega)
        unfold alg74BoxMarginConst at hw_bound
        omega
      rcases repeatBumpCmd_exec (by omega) hw2 hw_2p hw_c hw_cStar (c (k + 1) + 1)
          ((k + 1) * (4 * p + 2)) s₂ hw_xt (State.readReg_writeReg_self _ _ _) hsortC₂ hsafeC₂ with
        ⟨s₃, t₃, h3, harr₃, hval₃, hother₃⟩
      rw [iterate_bumpForb_eq_safeCol] at hval₃
      refine ⟨s₃, _, Exec.seq h1 (Exec.seq hinit h3), harr₃.trans harr₁, ?_, ?_⟩
      · intro j hj
        by_cases hlt : j < k + 1
        · rw [hother₃ (regSafeC p j) (by dsimp [regSafeC, Reg]; omega), hsafeC₂ j (by omega)]
        · have hj_eq : j = k + 1 := by omega
          subst hj_eq
          exact hval₃
      · intro reg hne
        rw [hother₃ reg (hne (k + 1) (by omega)),
          State.readReg_writeReg_ne s₁ (hne (k + 1) (by omega)),
          hother₁ reg (fun j hj => hne j (by omega))]

/-- Compute `regSafeC p i = safeCol p (fullColSeq ...) i` for all `i < alg74NumTerms p`. -/
def computeSafeColsCmd (p : ℕ) : Cmd :=
  computeSafeColsLoop p (alg74NumTerms p)

theorem computeSafeColsCmd_free (p : ℕ) :
    (computeSafeColsCmd p).IsLoopAllocFree :=
  computeSafeColsLoop_free p _

/-- Full Section 4 command: compute terminal coarse cells, box margin, perimeter info, color
permutation, sorted terminal table, and greedy safe columns in $O(1)$ time (for fixed `p`). -/
def routeTerminalsCmd (p : ℕ) : Cmd :=
  .seq (computeTermCellsCmd p)
    (.seq (computeBoxMarginCmd p)
      (.seq (computePerimAndPermCmd p)
        (.seq (insertionSortTermsCmd p)
          (computeSafeColsCmd p))))

theorem routeTerminalsCmd_free (p : ℕ) :
    (routeTerminalsCmd p).IsLoopAllocFree :=
  ⟨computeTermCellsCmd_free p,
   computeBoxMarginCmd_free p,
   computePerimAndPermCmd_free p,
   insertionSortTermsCmd_free p,
   computeSafeColsCmd_free p⟩

theorem routeTerminalsCmd_exec {w p r : ℕ} (hp0 : 0 < p) (x : Alg74Input p r)
    (hh1 : 1 ≤ x.h)
    (hw_n : x.n < 2 ^ w)
    (hw_wall : elemWallNumVerts x.h + (elemWallEdges x.h).length < 2 ^ w)
    (hw_bound : 2 * x.h + 2 + alg74BoxMarginConst p < 2 ^ w)
    (s : State)
    (hr3 : s.regs 3 = x.h)
    (hr12 : s.regs 12 = elemWallNumVerts x.h)
    (hr14 : s.regs 14 = 2 * x.h + 2)
    (harr2_len : (s.arrs locArr).length = x.n)
    (harr2 : ∀ v ∈ x.W.vertexFinset,
      (s.arrs locArr)[v.1]'(by rw [harr2_len]; exact v.2) = termLocCode x.W v)
    (harr3_len : (s.arrs edgeU1Arr).length = (elemWallEdges x.h).length)
    (harr3 : ∀ k : Fin (elemWallEdges x.h).length,
      (s.arrs edgeU1Arr)[k.1]'(by rw [harr3_len]; exact k.2) =
        ((elemWallEdges x.h)[k.1]'k.2).1.1)
    (hterm_edges : ∀ e : Fin (completeGraphEdges p).length,
      s.regs (20 + 2 * e.1) = (alg74TermVert x (edgeStartTerm e)).1 ∧
      s.regs (20 + 2 * e.1 + 1) = (alg74TermVert x (edgeEndTerm e)).1) :
    let B := chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x)
    let pinfo := perimTermInfo x.h B (alg74NumTerms p) (alg74Term x) (alg74RawColor p)
    ∃ s' t, Exec w (routeTerminalsCmd p) s s' t ∧
      t ≤ (routeTerminalsCmd p).maxTime ∧
      s'.arrs = s.arrs ∧
      (∀ reg : Reg, reg < 6 ∨ reg = 12 ∨ reg = 13 ∨ reg = 14 ∨
        (20 ≤ reg ∧ reg < 20 + alg74NumTerms p) → s'.regs reg = s.regs reg) ∧
      s'.regs 15 = B ∧
      s'.regs 16 = pinfo.1 ∧
      s'.regs 17 = pinfo.2.1 ∧
      s'.regs 18 = pinfo.2.2.1 ∧
      s'.regs 19 = pinfo.2.2.2 ∧
      (∀ a : Fin (alg74NumTerms p),
        s'.regs (regTermC p a.1) = (alg74Term x a).1 ∧
        s'.regs (regTermY p a.1) = (alg74Term x a).2) ∧
      (∀ g : Fin p,
        s'.regs (regPermColor p g.1) =
          (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p) g).1) ∧
      (∀ j : Fin (alg74NumTerms p),
        SortSlotHolds hp0 x B s' j.1 (fullSortedGet x.h B (alg74NumTerms p) (alg74Term x) j)) ∧
      (∀ j < alg74NumTerms p,
        s'.regs (regSafeC p j) =
          safeCol p (fullColSeq x.h B (alg74NumTerms p) (alg74Term x)) j) := by
  intro B pinfo
  have hw2 : 2 < 2 ^ w := by unfold alg74BoxMarginConst at hw_bound; omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw_p : p < 2 ^ w := by unfold alg74BoxMarginConst at hw_bound; omega
  have hw_h2 : 2 * x.h + 2 < 2 ^ w := by omega
  have hw_h1 : x.h + 1 < 2 ^ w := by omega
  have hw_h : x.h < 2 ^ w := by omega
  have hw_B₂ : alg74BoxMarginConst p < 2 ^ w := by omega
  have hterm_all : ∀ a ∈ List.finRange (alg74NumTerms p),
      s.readReg (regTermVert a.1) = (alg74TermVert x a).1 :=
    fun a _ => alg74TermVert_val_eq_reg x s hterm_edges a
  rcases computeTermCellsLoop_exec x hh1 hw_n hw_h2 hw_wall
      (List.finRange (alg74NumTerms p)) s (List.nodup_finRange _)
      hr3 hr12 hr14 harr2_len harr2 harr3_len harr3 hterm_all with
    ⟨s₁, t₁, h1, harr₁, htermC₁_mem, hother₁⟩
  have htermC₁ : ∀ a : Fin (alg74NumTerms p),
      s₁.readReg (regTermC p a.1) = (alg74Term x a).1 ∧
      s₁.readReg (regTermY p a.1) = (alg74Term x a).2 :=
    fun a => htermC₁_mem a (List.mem_finRange a)
  have hr3_1 : s₁.readReg 3 = x.h := by
    rw [hother₁ 3 (by decide) (by decide) (by decide) (by decide)
      (fun a _ => ⟨by dsimp [regTermC, Reg]; omega, by dsimp [regTermY, Reg]; omega⟩)]
    exact hr3
  rcases computeBoxMarginCmd_exec x hh1 hw2 hw_h hw_B₂ s₁ hr3_1 htermC₁ with
    ⟨s₂, t₂, h2, harr₂, hr15_2, hother₂⟩
  have hw_B : B < 2 ^ w := by
    dsimp [B]
    rw [chooseBoxMargin_eq_ite]
    split_ifs <;> [exact hw2; exact hw_B₂]
  have hr3_2 : s₂.readReg 3 = x.h := by
    rw [hother₂ 3 (by decide), hr3_1]
  have htermC₂ : ∀ a : Fin (alg74NumTerms p),
      s₂.readReg (regTermC p a.1) = (alg74Term x a).1 ∧
      s₂.readReg (regTermY p a.1) = (alg74Term x a).2 := by
    intro a
    rw [hother₂ (regTermC p a.1) (by dsimp [regTermC, Reg]; omega),
      hother₂ (regTermY p a.1) (by dsimp [regTermY, Reg]; omega)]
    exact htermC₁ a
  rcases computePerimLoop_exec x hh1 hw1 hw_p hw_h B hw_B
      (List.finRange (alg74NumTerms p)) s₂ hr3_2 hr15_2 htermC₂ with
    ⟨s₃, t₃, h3, harr₃, hr16_3, hr17_3, hr18_3, hr19_3, hother₃⟩
  change s₃.readReg 16 = pinfo.1 at hr16_3
  change s₃.readReg 17 = pinfo.2.1 at hr17_3
  change s₃.readReg 18 = pinfo.2.2.1 at hr18_3
  change s₃.readReg 19 = pinfo.2.2.2 at hr19_3
  rcases computePermLoop_exec hp0 x hh1 hw1 hw_p B
      (List.finRange p) s₃ (List.nodup_finRange p) hr19_3 with
    ⟨s₄, t₄, h4, harr₄, hperm₄_mem, hother₄⟩
  have hperm₄ : ∀ g : Fin p,
      s₄.readReg (regPermColor p g.1) =
        (colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p) g).1 :=
    fun g => hperm₄_mem g (List.mem_finRange g)
  have hr3_4 : s₄.readReg 3 = x.h := by
    rw [hother₄ 3 (fun g _ => by dsimp [regPermColor, Reg]; omega),
      hother₃ 3 (by decide) (by decide) (by decide) (by decide), hr3_2]
  have hr15_4 : s₄.readReg 15 = B := by
    rw [hother₄ 15 (fun g _ => by dsimp [regPermColor, Reg]; omega),
      hother₃ 15 (by decide) (by decide) (by decide) (by decide), hr15_2]
  have htermC₄ : ∀ a : Fin (alg74NumTerms p),
      s₄.readReg (regTermC p a.1) = (alg74Term x a).1 ∧
      s₄.readReg (regTermY p a.1) = (alg74Term x a).2 := by
    intro a
    have halt := a.2
    rw [hother₄ (regTermC p a.1) (fun g _ => by dsimp [regTermC, regPermColor, Reg]; omega),
      hother₃ (regTermC p a.1)
        (by dsimp [regTermC, Reg]; omega) (by dsimp [regTermC, Reg]; omega)
        (by dsimp [regTermC, Reg]; omega) (by dsimp [regTermC, Reg]; omega),
      hother₄ (regTermY p a.1) (fun g _ => by dsimp [regTermY, regPermColor, Reg]; omega),
      hother₃ (regTermY p a.1)
        (by dsimp [regTermY, Reg]; omega) (by dsimp [regTermY, Reg]; omega)
        (by dsimp [regTermY, Reg]; omega) (by dsimp [regTermY, Reg]; omega)]
    exact htermC₂ a
  rcases insertionSortLoop_exec hp0 x hh1 hw1 hw_h1 hw_p B hw_B
      (List.finRange (alg74NumTerms p)) s₄ hr3_4 hr15_4 htermC₄ hperm₄ with
    ⟨s₅, t₅, h5, harr₅, hslots₅_raw, hpres₅⟩
  have hslots₅ : ∀ j : Fin (alg74NumTerms p),
      SortSlotHolds hp0 x B s₅ j.1 (fullSortedGet x.h B (alg74NumTerms p) (alg74Term x) j) := by
    intro j
    have hj_len : j.1 < (fullSortedList x.h B (alg74NumTerms p) (alg74Term x)).length := by
      rw [length_fullSortedList]; exact j.2
    exact hslots₅_raw ⟨j.1, hj_len⟩
  let cSeq := fullColSeq x.h B (alg74NumTerms p) (alg74Term x)
  have hcSeq_le : ∀ j < alg74NumTerms p, cSeq j ≤ x.h := by
    intro j hj
    dsimp [cSeq, fullColSeq]
    simp only [hj, ↓reduceDIte]
    exact (alg74Term_bounds x hh1 _).2.1
  have hsortC₅ : ∀ j < alg74NumTerms p, s₅.readReg (regSortC p j) = cSeq j := by
    intro j hj
    dsimp [cSeq, fullColSeq]
    simp only [hj, ↓reduceDIte]
    exact (hslots₅ ⟨j, hj⟩).2.1
  rcases computeSafeColsLoop_exec hw2 hcSeq_le (by omega)
      (alg74NumTerms p) le_rfl s₅ hsortC₅ with
    ⟨s₆, t₆, h6, harr₆, hsafe₆, hother₆⟩
  have hexec : Exec w (routeTerminalsCmd p) s s₆ (t₁ + (t₂ + ((t₃ + t₄) + (t₅ + t₆)))) :=
    Exec.seq h1 (Exec.seq h2 (Exec.seq (Exec.seq h3 h4) (Exec.seq h5 h6)))
  have hpre_sort : ∀ reg : Reg, reg < regSortBase p → s₆.readReg reg = s₅.readReg reg := by
    intro reg hlt
    exact hother₆ reg (fun j _ => by dsimp [regSafeC, regSortBase, Reg] at *; omega)
  have hpre_ins : ∀ reg : Reg, reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 9 →
      reg < regSortBase p → s₆.readReg reg = s₄.readReg reg := by
    intro reg h6' h7' h8' h9' hlt
    rw [hpre_sort reg hlt, hpres₅ reg h6' h7' h8' h9' hlt]
  refine ⟨s₆, _, hexec, Exec.time_le_maxTime hexec (routeTerminalsCmd_free p),
    harr₆.trans (harr₅.trans (harr₄.trans (harr₃.trans (harr₂.trans harr₁)))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsafe₆⟩
  · intro reg hreg
    dsimp [Reg] at hreg
    have hlt_base : reg < regSortBase p := by
      dsimp [regSortBase, Reg] at *; omega
    have hne6 : reg ≠ 6 := by dsimp [Reg] at *; omega
    have hne7 : reg ≠ 7 := by dsimp [Reg] at *; omega
    have hne8 : reg ≠ 8 := by dsimp [Reg] at *; omega
    have hne9 : reg ≠ 9 := by dsimp [Reg] at *; omega
    have hne15 : reg ≠ 15 := by dsimp [Reg] at *; omega
    have hne16 : reg ≠ 16 := by dsimp [Reg] at *; omega
    have hne17 : reg ≠ 17 := by dsimp [Reg] at *; omega
    have hne18 : reg ≠ 18 := by dsimp [Reg] at *; omega
    have hne19 : reg ≠ 19 := by dsimp [Reg] at *; omega
    have hne_perm : ∀ g ∈ List.finRange p, reg ≠ regPermColor p g.1 := by
      intro g _
      dsimp [regPermColor, Reg] at *; omega
    have hne_cy : ∀ a ∈ List.finRange (alg74NumTerms p),
        reg ≠ regTermC p a.1 ∧ reg ≠ regTermY p a.1 := by
      intro a _
      dsimp [regTermC, regTermY, Reg] at *; omega
    change s₆.readReg reg = s.readReg reg
    rw [hpre_ins reg hne6 hne7 hne8 hne9 hlt_base,
      hother₄ reg hne_perm,
      hother₃ reg hne16 hne17 hne18 hne19,
      hother₂ reg hne15,
      hother₁ reg hne6 hne7 hne8 hne9 hne_cy]
  · change s₆.readReg 15 = B
    rw [hpre_ins 15 (by decide) (by decide) (by decide) (by decide)
      (by dsimp [regSortBase, Reg]; omega), hr15_4]
  · change s₆.readReg 16 = pinfo.1
    rw [hpre_ins 16 (by decide) (by decide) (by decide) (by decide)
      (by dsimp [regSortBase, Reg]; omega),
      hother₄ 16 (fun g _ => by dsimp [regPermColor, Reg]; omega), hr16_3]
  · change s₆.readReg 17 = pinfo.2.1
    rw [hpre_ins 17 (by decide) (by decide) (by decide) (by decide)
      (by dsimp [regSortBase, Reg]; omega),
      hother₄ 17 (fun g _ => by dsimp [regPermColor, Reg]; omega), hr17_3]
  · change s₆.readReg 18 = pinfo.2.2.1
    rw [hpre_ins 18 (by decide) (by decide) (by decide) (by decide)
      (by dsimp [regSortBase, Reg]; omega),
      hother₄ 18 (fun g _ => by dsimp [regPermColor, Reg]; omega), hr18_3]
  · change s₆.readReg 19 = pinfo.2.2.2
    rw [hpre_ins 19 (by decide) (by decide) (by decide) (by decide)
      (by dsimp [regSortBase, Reg]; omega),
      hother₄ 19 (fun g _ => by dsimp [regPermColor, Reg]; omega), hr19_3]
  · intro a
    have ha := a.2
    change s₆.readReg (regTermC p a.1) = _ ∧ s₆.readReg (regTermY p a.1) = _
    rw [hpre_ins (regTermC p a.1)
      (by dsimp [regTermC, Reg]; omega) (by dsimp [regTermC, Reg]; omega)
      (by dsimp [regTermC, Reg]; omega) (by dsimp [regTermC, Reg]; omega)
      (by dsimp [regTermC, regSortBase, Reg]; omega),
      hpre_ins (regTermY p a.1)
      (by dsimp [regTermY, Reg]; omega) (by dsimp [regTermY, Reg]; omega)
      (by dsimp [regTermY, Reg]; omega) (by dsimp [regTermY, Reg]; omega)
      (by dsimp [regTermY, regSortBase, Reg]; omega)]
    exact htermC₄ a
  · intro g
    have hg := g.2
    change s₆.readReg (regPermColor p g.1) = _
    rw [hpre_ins (regPermColor p g.1)
      (by dsimp [regPermColor, Reg]; omega) (by dsimp [regPermColor, Reg]; omega)
      (by dsimp [regPermColor, Reg]; omega) (by dsimp [regPermColor, Reg]; omega)
      (by dsimp [regPermColor, regSortBase, Reg]; omega)]
    exact hperm₄ g
  · intro j
    have hj := j.2
    refine sortSlotHolds_congr (hslots₅ j)
      (hother₆ _ (fun j' _ => by dsimp [regSortKey, regSafeC, regSortBase, Reg]; omega))
      (hother₆ _ (fun j' _ => by dsimp [regSortC, regSafeC, regSortBase, Reg]; omega))
      (hother₆ _ (fun j' _ => by dsimp [regSortY, regSafeC, regSortBase, Reg]; omega))
      (hother₆ _ (fun j' _ => by dsimp [regSortG, regSafeC, regSortBase, Reg]; omega))

end GraphMinor.Compute
