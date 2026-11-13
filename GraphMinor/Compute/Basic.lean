module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.List.Basic

/-!
# Word RAM model of computation

This file defines a first-order imperative programming language over bounded natural-number words
and 0-indexed arrays, together with its big-step operational semantics and time-complexity
definitions.

## Main definitions

* `GraphMinor.Compute.BinOp`: primitive binary operations on words (`add`, `sub`, `mul`, `div`,
  `mod`, `eq`, `lt`, `le`).
* `GraphMinor.Compute.Expr`: first-order expressions (constants, register reads, array reads,
  array lengths, and binary operations). Evaluating an expression costs the number of its AST
  nodes (`Expr.cost`), and every intermediate and final value must be strictly below `2 ^ w`.
* `GraphMinor.Compute.Cmd`: first-order commands (`skip`, `assign`, `write`, `alloc`, `seq`,
  `ite`, `while`).
* `GraphMinor.Compute.State`: machine state consisting of registers `Reg → ℕ` and arrays
  `Arr → List ℕ`.
* `GraphMinor.Compute.Exec`: big-step execution relation `Exec w c s s' t`, meaning that at word
  size `w`, command `c` starting from state `s` terminates in state `s'` in exactly `t` steps.
* `GraphMinor.Compute.ComputesInTime`: complexity statement that a program computes a function `f`
  on inputs of size `n` in time `O(T n)` with logarithmic word size `c * (Nat.log 2 (n + 2) + 1)`.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Register identifier. -/
abbrev Reg := ℕ

/-- Array identifier. -/
abbrev Arr := ℕ

/-- Standard input array identifier. -/
abbrev inArr : Arr := 0

/-- Standard output array identifier. -/
abbrev outArr : Arr := 1

/-- Standard output register identifier. -/
abbrev outReg : Reg := 0

/-- Primitive binary operations on natural-number words. -/
inductive BinOp where
  | add
  | sub
  | mul
  | div
  | mod
  | eq
  | lt
  | le
  deriving DecidableEq, Repr

/-- First-order expressions over registers and arrays. -/
inductive Expr where
  | const (n : ℕ)
  | reg (r : Reg)
  | read (a : Arr) (idx : Expr)
  | readMin (a : Arr) (idx cap : Expr)
  | len (a : Arr)
  | op (bop : BinOp) (e₁ e₂ : Expr)
  deriving DecidableEq, Repr

/-- First-order imperative commands. -/
inductive Cmd where
  | skip
  | assign (r : Reg) (e : Expr)
  | write (a : Arr) (idx val : Expr)
  | alloc (a : Arr) (len : Expr)
  | seq (c₁ c₂ : Cmd)
  | ite (cond : Expr) (c₁ c₂ : Cmd)
  | while (cond : Expr) (body : Cmd)
  deriving DecidableEq, Repr

/-- Machine state holding register values and 0-indexed arrays of words. -/
@[ext]
structure State where
  regs : Reg → ℕ
  arrs : Arr → List ℕ

/-- Update register `r` to `v` in state `s`. -/
def State.setReg (s : State) (r : Reg) (v : ℕ) : State where
  regs := Function.update s.regs r v
  arrs := s.arrs

/-- Replace array `a` with list `l` in state `s`. -/
def State.setArr (s : State) (a : Arr) (l : List ℕ) : State where
  regs := s.regs
  arrs := Function.update s.arrs a l

/-- Update index `i` of array `a` to `v` in state `s`. -/
def State.writeArr (s : State) (a : Arr) (i v : ℕ) : State :=
  s.setArr a ((s.arrs a).set i v)

/-- Initial state with `input` in `inArr`, all other arrays empty, and all registers `0`. -/
def initState (input : List ℕ) : State where
  regs := fun _ => 0
  arrs := fun a => if a = inArr then input else []

@[simp]
theorem State.setReg_regs_self (s : State) (r : Reg) (v : ℕ) :
    (s.setReg r v).regs r = v := by
  simp [State.setReg]

@[simp]
theorem State.setReg_regs_ne (s : State) {r r' : Reg} (v : ℕ) (h : r' ≠ r) :
    (s.setReg r v).regs r' = s.regs r' := by
  simp [State.setReg, h]

theorem State.setReg_regs (s : State) (r r' : Reg) (v : ℕ) :
    (s.setReg r v).regs r' = if r' = r then v else s.regs r' := by
  simp [State.setReg, Function.update_apply]

@[simp]
theorem State.setReg_arrs (s : State) (r : Reg) (v : ℕ) :
    (s.setReg r v).arrs = s.arrs := rfl

@[simp]
theorem State.setReg_setReg_same (s : State) (r : Reg) (v₁ v₂ : ℕ) :
    (s.setReg r v₁).setReg r v₂ = s.setReg r v₂ := by
  ext r' a <;> simp [State.setReg, Function.update_apply]

@[simp]
theorem State.setArr_regs (s : State) (a : Arr) (l : List ℕ) :
    (s.setArr a l).regs = s.regs := rfl

@[simp]
theorem State.setArr_arrs_self (s : State) (a : Arr) (l : List ℕ) :
    (s.setArr a l).arrs a = l := by
  simp [State.setArr]

@[simp]
theorem State.setArr_arrs_ne (s : State) {a a' : Arr} (l : List ℕ) (h : a' ≠ a) :
    (s.setArr a l).arrs a' = s.arrs a' := by
  simp [State.setArr, h]

theorem State.setArr_arrs (s : State) (a a' : Arr) (l : List ℕ) :
    (s.setArr a l).arrs a' = if a' = a then l else s.arrs a' := by
  simp [State.setArr, Function.update_apply]

@[simp]
theorem State.setArr_setArr_same (s : State) (a : Arr) (l₁ l₂ : List ℕ) :
    (s.setArr a l₁).setArr a l₂ = s.setArr a l₂ := by
  ext r a' <;> simp [State.setArr, Function.update_apply]

@[simp]
theorem State.writeArr_regs (s : State) (a : Arr) (i v : ℕ) :
    (s.writeArr a i v).regs = s.regs := rfl

@[simp]
theorem State.writeArr_arrs_self (s : State) (a : Arr) (i v : ℕ) :
    (s.writeArr a i v).arrs a = (s.arrs a).set i v := by
  simp [State.writeArr]

@[simp]
theorem State.writeArr_arrs_ne (s : State) {a a' : Arr} (i v : ℕ) (h : a' ≠ a) :
    (s.writeArr a i v).arrs a' = s.arrs a' := by
  simp [State.writeArr, h]

@[simp]
theorem State.initState_regs (input : List ℕ) (r : Reg) :
    (initState input).regs r = 0 := rfl

@[simp]
theorem State.initState_arrs_inArr (input : List ℕ) :
    (initState input).arrs inArr = input := by
  simp [initState]

/-- Number of AST nodes of an expression `e`. Evaluating `e` costs `e.cost`. -/
def Expr.cost : Expr → ℕ
  | .const _ => 1
  | .reg _ => 1
  | .read _ idx => idx.cost + 1
  | .readMin _ idx cap => idx.cost + cap.cost + 2
  | .len _ => 1
  | .op _ e₁ e₂ => e₁.cost + e₂.cost + 1

@[simp] theorem Expr.cost_const (n : ℕ) : (Expr.const n).cost = 1 := rfl
@[simp] theorem Expr.cost_reg (r : Reg) : (Expr.reg r).cost = 1 := rfl
@[simp] theorem Expr.cost_read (a : Arr) (idx : Expr) : (Expr.read a idx).cost = idx.cost + 1 := rfl
@[simp] theorem Expr.cost_readMin (a : Arr) (idx cap : Expr) :
    (Expr.readMin a idx cap).cost = idx.cost + cap.cost + 2 := rfl
@[simp] theorem Expr.cost_len (a : Arr) : (Expr.len a).cost = 1 := rfl
@[simp] theorem Expr.cost_op (bop : BinOp) (e₁ e₂ : Expr) :
    (Expr.op bop e₁ e₂).cost = e₁.cost + e₂.cost + 1 := rfl

theorem Expr.cost_pos (e : Expr) : 0 < e.cost := by
  cases e <;> simp [Expr.cost]

/-- Check that `v` fits in a word of `w` bits (`v < 2 ^ w`). -/
def checkWord (w v : ℕ) : Option ℕ :=
  if v < 2 ^ w then some v else none

@[simp]
theorem checkWord_eq_some {w v u : ℕ} :
    checkWord w v = some u ↔ v < 2 ^ w ∧ v = u := by
  unfold checkWord
  split_ifs with h <;> simp [h]

theorem checkWord_of_lt {w v : ℕ} (h : v < 2 ^ w) : checkWord w v = some v := by
  simp [h]

theorem checkWord_lt {w v u : ℕ} (h : checkWord w v = some u) : u < 2 ^ w := by
  rw [checkWord_eq_some] at h
  omega

theorem checkWord_mono {w₁ w₂ v u : ℕ} (hw : w₁ ≤ w₂) (h : checkWord w₁ v = some u) :
    checkWord w₂ v = some u := by
  have hpow : 2 ^ w₁ ≤ 2 ^ w₂ := Nat.pow_le_pow_right (by omega) hw
  rw [checkWord_eq_some] at h ⊢
  exact ⟨by omega, h.2⟩

/-- Raw unbounded value of a binary operation on `v₁` and `v₂` (`none` on division/remainder by 0). -/
def BinOp.raw : BinOp → ℕ → ℕ → Option ℕ
  | .add, v₁, v₂ => some (v₁ + v₂)
  | .sub, v₁, v₂ => some (v₁ - v₂)
  | .mul, v₁, v₂ => some (v₁ * v₂)
  | .div, v₁, v₂ => if v₂ = 0 then none else some (v₁ / v₂)
  | .mod, v₁, v₂ => if v₂ = 0 then none else some (v₁ % v₂)
  | .eq,  v₁, v₂ => some (if v₁ = v₂ then 1 else 0)
  | .lt,  v₁, v₂ => some (if v₁ < v₂ then 1 else 0)
  | .le,  v₁, v₂ => some (if v₁ ≤ v₂ then 1 else 0)

/-- Evaluate a binary operation on two words `v₁` and `v₂` under word size `w`.
Returns `none` on overflow (`≥ 2 ^ w`) or division/remainder by zero. -/
def BinOp.eval (w : ℕ) (bop : BinOp) (v₁ v₂ : ℕ) : Option ℕ :=
  match bop.raw v₁ v₂ with
  | some v => checkWord w v
  | none => none

/-- Evaluate an expression `e` in state `s` under word size `w`.
Returns `none` if any intermediate or final value is `≥ 2 ^ w`, any array read is out of bounds,
or any division/remainder is by zero. -/
def Expr.eval (w : ℕ) (s : State) : Expr → Option ℕ
  | .const n => checkWord w n
  | .reg r => checkWord w (s.regs r)
  | .read a idx =>
    match idx.eval w s with
    | some i =>
      if h : i < (s.arrs a).length then
        checkWord w (s.arrs a)[i]
      else none
    | none => none
  | .readMin a idx cap =>
    match idx.eval w s, cap.eval w s with
    | some i, some c =>
      if h : i < (s.arrs a).length then
        checkWord w (Nat.min (s.arrs a)[i] c)
      else none
    | _, _ => none
  | .len a => checkWord w (s.arrs a).length
  | .op bop e₁ e₂ =>
    match e₁.eval w s, e₂.eval w s with
    | some v₁, some v₂ => bop.eval w v₁ v₂
    | _, _ => none

theorem BinOp.eval_lt {w : ℕ} {bop : BinOp} {v₁ v₂ v : ℕ}
    (h : bop.eval w v₁ v₂ = some v) : v < 2 ^ w := by
  unfold BinOp.eval at h
  cases hraw : bop.raw v₁ v₂ with
  | none => simp [hraw] at h
  | some u =>
    rw [hraw] at h
    exact checkWord_lt h

theorem Expr.eval_lt {w : ℕ} {s : State} {e : Expr} {v : ℕ}
    (h : e.eval w s = some v) : v < 2 ^ w := by
  cases e with
  | const n => exact checkWord_lt h
  | reg r => exact checkWord_lt h
  | read a idx =>
    simp only [Expr.eval] at h
    cases hidx : idx.eval w s with
    | none => simp [hidx] at h
    | some i =>
      rw [hidx] at h
      dsimp only at h
      split_ifs at h with hi
      exact checkWord_lt h
  | readMin a idx cap =>
    simp only [Expr.eval] at h
    cases hidx : idx.eval w s with
    | none => simp [hidx] at h
    | some i =>
      cases hcap : cap.eval w s with
      | none => simp [hidx, hcap] at h
      | some c =>
        rw [hidx, hcap] at h
        dsimp only at h
        split_ifs at h with hi
        exact checkWord_lt h
  | len a => exact checkWord_lt h
  | op bop e₁ e₂ =>
    simp only [Expr.eval] at h
    cases h₁ : e₁.eval w s with
    | none => simp [h₁] at h
    | some v₁ =>
      cases h₂ : e₂.eval w s with
      | none => simp [h₁, h₂] at h
      | some v₂ =>
        rw [h₁, h₂] at h
        exact BinOp.eval_lt h

theorem BinOp.eval_mono {w₁ w₂ : ℕ} (hw : w₁ ≤ w₂) {bop : BinOp} {v₁ v₂ v : ℕ}
    (h : bop.eval w₁ v₁ v₂ = some v) : bop.eval w₂ v₁ v₂ = some v := by
  unfold BinOp.eval at h ⊢
  cases hraw : bop.raw v₁ v₂ with
  | none => simp [hraw] at h
  | some u =>
    rw [hraw] at h
    exact checkWord_mono hw h

theorem Expr.eval_mono {w₁ w₂ : ℕ} (hw : w₁ ≤ w₂) {s : State} {e : Expr} {v : ℕ}
    (h : e.eval w₁ s = some v) : e.eval w₂ s = some v := by
  induction e generalizing v with
  | const n => exact checkWord_mono hw h
  | reg r => exact checkWord_mono hw h
  | read a idx ih =>
    simp only [Expr.eval] at h ⊢
    cases hidx : idx.eval w₁ s with
    | none => simp [hidx] at h
    | some i =>
      rw [hidx] at h
      rw [ih hidx]
      dsimp only at h ⊢
      split_ifs at h with hi
      simp only [hi, ↓reduceDIte]
      exact checkWord_mono hw h
  | readMin a idx cap ih_idx ih_cap =>
    simp only [Expr.eval] at h ⊢
    cases hidx : idx.eval w₁ s with
    | none => simp [hidx] at h
    | some i =>
      cases hcap : cap.eval w₁ s with
      | none => simp [hidx, hcap] at h
      | some c =>
        rw [hidx, hcap] at h
        rw [ih_idx hidx, ih_cap hcap]
        dsimp only at h ⊢
        split_ifs at h with hi
        simp only [hi, ↓reduceDIte]
        exact checkWord_mono hw h
  | len a => exact checkWord_mono hw h
  | op bop e₁ e₂ ih₁ ih₂ =>
    simp only [Expr.eval] at h ⊢
    cases h₁ : e₁.eval w₁ s with
    | none => simp [h₁] at h
    | some v₁ =>
      cases h₂ : e₂.eval w₁ s with
      | none => simp [h₁, h₂] at h
      | some v₂ =>
        rw [h₁, h₂] at h
        rw [ih₁ h₁, ih₂ h₂]
        exact BinOp.eval_mono hw h

/-- Big-step operational semantics `Exec w c s s' t`: with word size `w`, executing command `c`
from initial state `s` terminates in state `s'` after `t` steps. -/
inductive Exec (w : ℕ) : Cmd → State → State → ℕ → Prop where
  | skip (s : State) :
      Exec w .skip s s 1
  | assign {r : Reg} {e : Expr} {s : State} {v : ℕ}
      (he : e.eval w s = some v) :
      Exec w (.assign r e) s (s.setReg r v) (e.cost + 1)
  | write {a : Arr} {idx val : Expr} {s : State} {i v : ℕ}
      (hi : idx.eval w s = some i)
      (hv : val.eval w s = some v)
      (hbound : i < (s.arrs a).length) :
      Exec w (.write a idx val) s (s.writeArr a i v) (idx.cost + val.cost + 1)
  | alloc {a : Arr} {len : Expr} {s : State} {m : ℕ}
      (hm : len.eval w s = some m) :
      Exec w (.alloc a len) s (s.setArr a (List.replicate m 0)) (len.cost + m)
  | seq {c₁ c₂ : Cmd} {s s₁ s₂ : State} {t₁ t₂ : ℕ}
      (h₁ : Exec w c₁ s s₁ t₁)
      (h₂ : Exec w c₂ s₁ s₂ t₂) :
      Exec w (.seq c₁ c₂) s s₂ (t₁ + t₂)
  | ite_true {cond : Expr} {c₁ c₂ : Cmd} {s s' : State} {v t : ℕ}
      (hcond : cond.eval w s = some v)
      (hv : v ≠ 0)
      (hbody : Exec w c₁ s s' t) :
      Exec w (.ite cond c₁ c₂) s s' (cond.cost + t)
  | ite_false {cond : Expr} {c₁ c₂ : Cmd} {s s' : State} {t : ℕ}
      (hcond : cond.eval w s = some 0)
      (hbody : Exec w c₂ s s' t) :
      Exec w (.ite cond c₁ c₂) s s' (cond.cost + t)
  | while_false {cond : Expr} {body : Cmd} {s : State}
      (hcond : cond.eval w s = some 0) :
      Exec w (.while cond body) s s cond.cost
  | while_true {cond : Expr} {body : Cmd} {s s₁ s₂ : State} {v t₁ t₂ : ℕ}
      (hcond : cond.eval w s = some v)
      (hv : v ≠ 0)
      (hbody : Exec w body s s₁ t₁)
      (hrest : Exec w (.while cond body) s₁ s₂ t₂) :
      Exec w (.while cond body) s s₂ (cond.cost + t₁ + t₂)

/-- Every terminating execution takes at least one step. -/
theorem Exec.time_pos {w : ℕ} {c : Cmd} {s s' : State} {t : ℕ} (h : Exec w c s s' t) : 0 < t := by
  induction h with
  | skip => omega
  | assign => omega
  | write => omega
  | alloc =>
    have := Expr.cost_pos ‹Expr›
    omega
  | seq _ _ ih₁ ih₂ => omega
  | ite_true _ _ _ ih => omega
  | ite_false _ _ ih => omega
  | while_false => exact Expr.cost_pos _
  | while_true _ _ _ _ ih₁ ih₂ => omega

/-- The big-step semantics `Exec` is deterministic: both the final state and the step count are
uniquely determined by the word size, command, and initial state. -/
theorem Exec.deterministic {w : ℕ} {c : Cmd} {s s₁ s₂ : State} {t₁ t₂ : ℕ}
    (h₁ : Exec w c s s₁ t₁) (h₂ : Exec w c s s₂ t₂) : s₁ = s₂ ∧ t₁ = t₂ := by
  induction h₁ generalizing s₂ t₂ with
  | skip =>
    cases h₂
    exact ⟨rfl, rfl⟩
  | assign he₁ =>
    cases h₂ with
    | assign he₂ =>
      rw [he₁] at he₂
      injection he₂ with hv
      subst hv
      exact ⟨rfl, rfl⟩
  | write hi₁ hv₁ _ =>
    cases h₂ with
    | write hi₂ hv₂ _ =>
      rw [hi₁] at hi₂; injection hi₂ with hi
      rw [hv₁] at hv₂; injection hv₂ with hv
      subst hi hv
      exact ⟨rfl, rfl⟩
  | alloc hm₁ =>
    cases h₂ with
    | alloc hm₂ =>
      rw [hm₁] at hm₂; injection hm₂ with hm
      subst hm
      exact ⟨rfl, rfl⟩
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₂a h₂b =>
      obtain ⟨rfl, rfl⟩ := ih₁ h₂a
      obtain ⟨rfl, rfl⟩ := ih₂ h₂b
      exact ⟨rfl, rfl⟩
  | ite_true hcond₁ hv₁ _ ih =>
    cases h₂ with
    | ite_true hcond₂ hv₂ hbody₂ =>
      obtain ⟨rfl, rfl⟩ := ih hbody₂
      exact ⟨rfl, rfl⟩
    | ite_false hcond₂ _ =>
      rw [hcond₁] at hcond₂; injection hcond₂ with hv
      exact False.elim (hv₁ hv)
  | ite_false hcond₁ _ ih =>
    cases h₂ with
    | ite_true hcond₂ hv₂ _ =>
      rw [hcond₁] at hcond₂; injection hcond₂ with hv
      exact False.elim (hv₂ hv.symm)
    | ite_false _ hbody₂ =>
      obtain ⟨rfl, rfl⟩ := ih hbody₂
      exact ⟨rfl, rfl⟩
  | while_false hcond₁ =>
    cases h₂ with
    | while_false => exact ⟨rfl, rfl⟩
    | while_true hcond₂ hv₂ _ _ =>
      rw [hcond₁] at hcond₂; injection hcond₂ with hv
      exact False.elim (hv₂ hv.symm)
  | while_true hcond₁ hv₁ _ _ ih₁ ih₂ =>
    cases h₂ with
    | while_false hcond₂ =>
      rw [hcond₁] at hcond₂; injection hcond₂ with hv
      exact False.elim (hv₁ hv)
    | while_true _ _ hbody₂ hrest₂ =>
      obtain ⟨rfl, rfl⟩ := ih₁ hbody₂
      obtain ⟨rfl, rfl⟩ := ih₂ hrest₂
      exact ⟨rfl, rfl⟩

/-- Execution is monotone in the word size `w`: increasing `w` preserves all executions and their
exact step counts. -/
theorem Exec.mono_wordSize {w₁ w₂ : ℕ} (hw : w₁ ≤ w₂) {c : Cmd} {s s' : State} {t : ℕ}
    (h : Exec w₁ c s s' t) : Exec w₂ c s s' t := by
  induction h with
  | skip s => exact .skip s
  | assign he => exact .assign (Expr.eval_mono hw he)
  | write hi hv hbound => exact .write (Expr.eval_mono hw hi) (Expr.eval_mono hw hv) hbound
  | alloc hm => exact .alloc (Expr.eval_mono hw hm)
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite_true hcond hv _ ih => exact .ite_true (Expr.eval_mono hw hcond) hv ih
  | ite_false hcond _ ih => exact .ite_false (Expr.eval_mono hw hcond) ih
  | while_false hcond => exact .while_false (Expr.eval_mono hw hcond)
  | while_true hcond hv _ _ ih₁ ih₂ =>
    exact .while_true (Expr.eval_mono hw hcond) hv ih₁ ih₂

/-- The finite set of registers assigned to by command `c`. -/
def Cmd.writtenRegs : Cmd → Finset Reg
  | .skip => ∅
  | .assign r _ => {r}
  | .write _ _ _ => ∅
  | .alloc _ _ => ∅
  | .seq c₁ c₂ => c₁.writtenRegs ∪ c₂.writtenRegs
  | .ite _ c₁ c₂ => c₁.writtenRegs ∪ c₂.writtenRegs
  | .while _ body => body.writtenRegs

/-- The finite set of arrays written to or allocated by command `c`. -/
def Cmd.writtenArrs : Cmd → Finset Arr
  | .skip => ∅
  | .assign _ _ => ∅
  | .write a _ _ => {a}
  | .alloc a _ => {a}
  | .seq c₁ c₂ => c₁.writtenArrs ∪ c₂.writtenArrs
  | .ite _ c₁ c₂ => c₁.writtenArrs ∪ c₂.writtenArrs
  | .while _ body => body.writtenArrs

/-- A register not in `c.writtenRegs` is unchanged by executing `c`. -/
theorem Exec.regs_eq_of_not_mem_writtenRegs {w : ℕ} {c : Cmd} {s s' : State} {t : ℕ}
    (h : Exec w c s s' t) {r : Reg} (hr : r ∉ c.writtenRegs) :
    s'.regs r = s.regs r := by
  induction h with
  | skip => rfl
  | assign =>
    simp only [Cmd.writtenRegs, Finset.mem_singleton] at hr
    exact State.setReg_regs_ne _ _ hr
  | write => rfl
  | alloc => rfl
  | seq _ _ ih₁ ih₂ =>
    simp only [Cmd.writtenRegs, Finset.mem_union, not_or] at hr
    rw [ih₂ hr.2, ih₁ hr.1]
  | ite_true _ _ _ ih =>
    simp only [Cmd.writtenRegs, Finset.mem_union, not_or] at hr
    exact ih hr.1
  | ite_false _ _ ih =>
    simp only [Cmd.writtenRegs, Finset.mem_union, not_or] at hr
    exact ih hr.2
  | while_false => rfl
  | while_true _ _ _ _ ih₁ ih₂ =>
    simp only [Cmd.writtenRegs] at hr
    rw [ih₂ hr, ih₁ hr]

/-- An array not in `c.writtenArrs` is unchanged by executing `c`. -/
theorem Exec.arrs_eq_of_not_mem_writtenArrs {w : ℕ} {c : Cmd} {s s' : State} {t : ℕ}
    (h : Exec w c s s' t) {a : Arr} (ha : a ∉ c.writtenArrs) :
    s'.arrs a = s.arrs a := by
  induction h with
  | skip => rfl
  | assign => rfl
  | write =>
    simp only [Cmd.writtenArrs, Finset.mem_singleton] at ha
    exact State.writeArr_arrs_ne _ _ _ ha
  | alloc =>
    simp only [Cmd.writtenArrs, Finset.mem_singleton] at ha
    exact State.setArr_arrs_ne _ _ ha
  | seq _ _ ih₁ ih₂ =>
    simp only [Cmd.writtenArrs, Finset.mem_union, not_or] at ha
    rw [ih₂ ha.2, ih₁ ha.1]
  | ite_true _ _ _ ih =>
    simp only [Cmd.writtenArrs, Finset.mem_union, not_or] at ha
    exact ih ha.1
  | ite_false _ _ ih =>
    simp only [Cmd.writtenArrs, Finset.mem_union, not_or] at ha
    exact ih ha.2
  | while_false => rfl
  | while_true _ _ _ _ ih₁ ih₂ =>
    simp only [Cmd.writtenArrs] at ha
    rw [ih₂ ha, ih₁ ha]

/-- The logarithmic word size `c * (Nat.log 2 (n + 2) + 1)` for input size `n` and constant `c`. -/
def wordSize (c n : ℕ) : ℕ :=
  c * (Nat.log 2 (n + 2) + 1)

theorem lt_two_pow_log_succ (n : ℕ) : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) :=
  Nat.lt_pow_succ_log_self (by decide) (n + 2)

theorem pow_lt_two_pow_wordSize {c : ℕ} (hc : 1 ≤ c) (n : ℕ) :
    (n + 2) ^ c < 2 ^ wordSize c n := by
  unfold wordSize
  rw [Nat.mul_comm, Nat.pow_mul]
  exact Nat.pow_lt_pow_left (lt_two_pow_log_succ n) (by omega)

theorem lt_two_pow_wordSize_of_le {c n k : ℕ} (hc : 1 ≤ c) (hk : k ≤ n + 1) :
    k < 2 ^ wordSize c n := by
  have h1 : n + 2 ≤ (n + 2) ^ c := Nat.le_self_pow (by omega) (n + 2)
  have h2 : (n + 2) ^ c < 2 ^ wordSize c n := pow_lt_two_pow_wordSize hc n
  omega

theorem lt_two_pow_wordSize_of_lt_pow {c n k : ℕ} (hc : 1 ≤ c) (hk : k ≤ (n + 2) ^ c) :
    k < 2 ^ wordSize c n :=
   Nat.lt_of_le_of_lt hk (pow_lt_two_pow_wordSize hc n)

theorem sq_lt_two_pow_wordSize {c n : ℕ} (hc : 2 ≤ c) :
    (n + 2) * (n + 2) < 2 ^ wordSize c n := by
  apply lt_two_pow_wordSize_of_lt_pow (by omega)
  calc (n + 2) * (n + 2) = (n + 2) ^ 2 := (Nat.pow_two (n + 2)).symm
    _ ≤ (n + 2) ^ c := Nat.pow_le_pow_right (by omega) hc

theorem two_mul_lt_two_pow_wordSize {c n : ℕ} (hc : 2 ≤ c) :
    2 * (n + 2) < 2 ^ wordSize c n := by
  have hsq := sq_lt_two_pow_wordSize (n := n) hc
  have hle : 2 * (n + 2) ≤ (n + 2) * (n + 2) := Nat.mul_le_mul_right (n + 2) (by omega)
  omega

theorem wordSize_mono_left {c₁ c₂ : ℕ} (hc : c₁ ≤ c₂) (n : ℕ) :
    wordSize c₁ n ≤ wordSize c₂ n :=
  Nat.mul_le_mul_right _ hc

theorem wordSize_mono_right (c : ℕ) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) :
    wordSize c n₁ ≤ wordSize c n₂ := by
  unfold wordSize
  apply Nat.mul_le_mul_left
  have : Nat.log 2 (n₁ + 2) ≤ Nat.log 2 (n₂ + 2) := Nat.log_mono_right (by omega)
  omega

/-- A program `P` computes `f : α → β` in time `T` (with respect to input size `size`, input
condition `InRel`, and output condition `OutRel`) if there exist constants `C, c ≥ 1` such that for
every input `x : α` of size `n = size x` and every initial state `s` satisfying `InRel x s`, running
`P` with word size `c * (Nat.log 2 (n + 2) + 1)` terminates within `C * T n` steps in a state `s'`
satisfying `OutRel (f x) s'`. -/
def ComputesInTime {α β : Type*} (size : α → ℕ) (InRel : α → State → Prop)
    (OutRel : β → State → Prop) (f : α → β) (P : Cmd) (T : ℕ → ℕ) : Prop :=
  ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : α) (s : State), InRel x s →
    ∃ s' t, Exec (wordSize c (size x)) P s s' t ∧ t ≤ C * T (size x) ∧ OutRel (f x) s'

/-- Standard input-array / output-array specialization of `ComputesInTime`, where the encoded input
is placed in `inArr` and the encoded output is written to `outArr`. -/
def ComputesArrInTime {α β : Type*} (size : α → ℕ) (encIn : α → List ℕ)
    (encOut : β → List ℕ) (f : α → β) (P : Cmd) (T : ℕ → ℕ) : Prop :=
  ComputesInTime size (fun x s => s.arrs inArr = encIn x)
    (fun y s' => s'.arrs outArr = encOut y) f P T

/-- Standard input-array / output-register specialization of `ComputesInTime`, where the encoded
input is placed in `inArr` and the natural-number output is written to `outReg`. -/
def ComputesRegInTime {α : Type*} (size : α → ℕ) (encIn : α → List ℕ)
    (f : α → ℕ) (P : Cmd) (T : ℕ → ℕ) : Prop :=
  ComputesInTime size (fun x s => s.arrs inArr = encIn x)
    (fun y s' => s'.regs outReg = y) f P T

/-- Every `ComputesArrInTime` program runs from `initState (encIn x)` in time `C * T (size x)`. -/
theorem ComputesArrInTime.exec_initState {α β : Type*} {size : α → ℕ} {encIn : α → List ℕ}
    {encOut : β → List ℕ} {f : α → β} {P : Cmd} {T : ℕ → ℕ}
    (h : ComputesArrInTime size encIn encOut f P T) :
    ∃ C c : ℕ, ∀ x : α, ∃ s' t,
      Exec (wordSize c (size x)) P (initState (encIn x)) s' t ∧
      t ≤ C * T (size x) ∧ s'.arrs outArr = encOut (f x) := by
  rcases h with ⟨C, c, _, _, hexec⟩
  exact ⟨C, c, fun x => hexec x (initState (encIn x)) rfl⟩

/-- Monotonicity of `ComputesInTime` in the time bound `T`. -/
theorem ComputesInTime.mono_time {α β : Type*} {size : α → ℕ} {InRel : α → State → Prop}
    {OutRel : β → State → Prop} {f : α → β} {P : Cmd} {T₁ T₂ : ℕ → ℕ}
    (h : ComputesInTime size InRel OutRel f P T₁)
    {K : ℕ} (hK : 1 ≤ K) (hle : ∀ n, T₁ n ≤ K * T₂ n) :
    ComputesInTime size InRel OutRel f P T₂ := by
  rcases h with ⟨C, c, hC, hc, hP⟩
  refine ⟨C * K, c, Nat.mul_pos hC hK, hc, fun x s hs => ?_⟩
  rcases hP x s hs with ⟨s', t, hexec, ht, hout⟩
  refine ⟨s', t, hexec, ?_, hout⟩
  calc t ≤ C * T₁ (size x) := ht
    _ ≤ C * (K * T₂ (size x)) := Nat.mul_le_mul_left C (hle (size x))
    _ = (C * K) * T₂ (size x) := (Nat.mul_assoc C K _).symm

/-- Sequential composition of two `ComputesInTime` stages when the intermediate size is bounded by
`sizeα x`. -/
theorem ComputesInTime.seq {α β γ : Type*} {sizeα : α → ℕ} {sizeβ : β → ℕ}
    {InRel : α → State → Prop} {MidRel : β → State → Prop} {OutRel : γ → State → Prop}
    {f : α → β} {g : β → γ} {P₁ P₂ : Cmd} {T₁ T₂ T : ℕ → ℕ}
    (h₁ : ComputesInTime sizeα InRel MidRel f P₁ T₁)
    (h₂ : ComputesInTime sizeβ MidRel OutRel g P₂ T₂)
    (hsize : ∀ x, sizeβ (f x) ≤ sizeα x)
    (hT : ∀ x, T₁ (sizeα x) + T₂ (sizeβ (f x)) ≤ T (sizeα x)) :
    ComputesInTime sizeα InRel OutRel (g ∘ f) (.seq P₁ P₂) T := by
  rcases h₁ with ⟨C₁, c₁, hC₁, hc₁, hP₁⟩
  rcases h₂ with ⟨C₂, c₂, hC₂, hc₂, hP₂⟩
  refine ⟨C₁ + C₂, c₁ + c₂, by omega, by omega, fun x s hs => ?_⟩
  rcases hP₁ x s hs with ⟨s₁, t₁, hexec₁, ht₁, hmid⟩
  rcases hP₂ (f x) s₁ hmid with ⟨s₂, t₂, hexec₂, ht₂, hout⟩
  have hw₁ : wordSize c₁ (sizeα x) ≤ wordSize (c₁ + c₂) (sizeα x) :=
    wordSize_mono_left (by omega) _
  have hw₂ : wordSize c₂ (sizeβ (f x)) ≤ wordSize (c₁ + c₂) (sizeα x) :=
    (wordSize_mono_right c₂ (hsize x)).trans (wordSize_mono_left (by omega) _)
  refine ⟨s₂, t₁ + t₂, .seq (hexec₁.mono_wordSize hw₁) (hexec₂.mono_wordSize hw₂), ?_, hout⟩
  have hbound := hT x
  calc t₁ + t₂ ≤ C₁ * T₁ (sizeα x) + C₂ * T₂ (sizeβ (f x)) := Nat.add_le_add ht₁ ht₂
    _ ≤ (C₁ + C₂) * T₁ (sizeα x) + (C₁ + C₂) * T₂ (sizeβ (f x)) := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_right _ (by omega)
      · exact Nat.mul_le_mul_right _ (by omega)
    _ = (C₁ + C₂) * (T₁ (sizeα x) + T₂ (sizeβ (f x))) := (Nat.mul_add _ _ _).symm
    _ ≤ (C₁ + C₂) * T (sizeα x) := Nat.mul_le_mul_left _ hbound

/-- Sequential composition of two `ComputesInTime` stages with the same size function and
monotone second-stage time bound `T₂`. -/
theorem ComputesInTime.seq_add {α β γ : Type*} {sizeα : α → ℕ} {sizeβ : β → ℕ}
    {InRel : α → State → Prop} {MidRel : β → State → Prop} {OutRel : γ → State → Prop}
    {f : α → β} {g : β → γ} {P₁ P₂ : Cmd} {T₁ T₂ : ℕ → ℕ}
    (h₁ : ComputesInTime sizeα InRel MidRel f P₁ T₁)
    (h₂ : ComputesInTime sizeβ MidRel OutRel g P₂ T₂)
    (hsize : ∀ x, sizeβ (f x) ≤ sizeα x)
    (hmono : Monotone T₂) :
    ComputesInTime sizeα InRel OutRel (g ∘ f) (.seq P₁ P₂) (fun n => T₁ n + T₂ n) :=
  h₁.seq h₂ hsize fun x => Nat.add_le_add_left (hmono (hsize x)) _

/-- A linear-time stage (`n + 1`) followed by a cubic-time stage (`(n + 1) ^ 3`) runs in cubic
time (`(n + 1) ^ 3`). -/
theorem ComputesInTime.linear_seq_cubic {α β γ : Type*} {sizeα : α → ℕ} {sizeβ : β → ℕ}
    {InRel : α → State → Prop} {MidRel : β → State → Prop} {OutRel : γ → State → Prop}
    {f : α → β} {g : β → γ} {P₁ P₂ : Cmd}
    (h₁ : ComputesInTime sizeα InRel MidRel f P₁ (fun n => n + 1))
    (h₂ : ComputesInTime sizeβ MidRel OutRel g P₂ (fun n => (n + 1) ^ 3))
    (hsize : ∀ x, sizeβ (f x) ≤ sizeα x) :
    ComputesInTime sizeα InRel OutRel (g ∘ f) (.seq P₁ P₂) (fun n => (n + 1) ^ 3) := by
  have hseq := h₁.seq_add h₂ hsize (fun a b hab => Nat.pow_le_pow_left (by omega) 3)
  refine hseq.mono_time (K := 2) (by omega) (fun n => ?_)
  have hle : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by omega) (n + 1)
  omega

/-- A quadratic-time stage (`(n + 1) ^ 2`) followed by a cubic-time stage (`(n + 1) ^ 3`) runs in
cubic time (`(n + 1) ^ 3`). -/
theorem ComputesInTime.quad_seq_cubic {α β γ : Type*} {sizeα : α → ℕ} {sizeβ : β → ℕ}
    {InRel : α → State → Prop} {MidRel : β → State → Prop} {OutRel : γ → State → Prop}
    {f : α → β} {g : β → γ} {P₁ P₂ : Cmd}
    (h₁ : ComputesInTime sizeα InRel MidRel f P₁ (fun n => (n + 1) ^ 2))
    (h₂ : ComputesInTime sizeβ MidRel OutRel g P₂ (fun n => (n + 1) ^ 3))
    (hsize : ∀ x, sizeβ (f x) ≤ sizeα x) :
    ComputesInTime sizeα InRel OutRel (g ∘ f) (.seq P₁ P₂) (fun n => (n + 1) ^ 3) := by
  have hseq := h₁.seq_add h₂ hsize (fun a b hab => Nat.pow_le_pow_left (by omega) 3)
  refine hseq.mono_time (K := 2) (by omega) (fun n => ?_)
  have hle : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- Relational variant of `ComputesInTime` for problems where the valid output is not unique:
there exist constants `C, c ≥ 1` such that for every input `x : α` of size `n = size x` and every
initial state `s` satisfying `InRel x s`, running `P` with word size `c * (Nat.log 2 (n + 2) + 1)`
terminates within `C * T n` steps in a state `s'` satisfying `OutRel x s'`. -/
def ComputesRelInTime {α : Type*} (size : α → ℕ) (InRel : α → State → Prop)
    (OutRel : α → State → Prop) (P : Cmd) (T : ℕ → ℕ) : Prop :=
  ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : α) (s : State), InRel x s →
    ∃ s' t, Exec (wordSize c (size x)) P s s' t ∧ t ≤ C * T (size x) ∧ OutRel x s'

/-- Standard input-array / output-array specialization of `ComputesRelInTime`, where the encoded
input is placed in `inArr` and the output list in `s'.arrs outArr` satisfies `OutRel x (s'.arrs outArr)`. -/
def ComputesArrRelInTime {α : Type*} (size : α → ℕ) (encIn : α → List ℕ)
    (OutRel : α → List ℕ → Prop) (P : Cmd) (T : ℕ → ℕ) : Prop :=
  ComputesRelInTime size (fun x s => s.arrs inArr = encIn x)
    (fun x s' => OutRel x (s'.arrs outArr)) P T

/-- Every `ComputesInTime` statement is a special case of `ComputesRelInTime`. -/
theorem ComputesInTime.to_computesRelInTime {α β : Type*} {size : α → ℕ}
    {InRel : α → State → Prop} {OutRel : β → State → Prop} {f : α → β} {P : Cmd} {T : ℕ → ℕ}
    (h : ComputesInTime size InRel OutRel f P T) :
    ComputesRelInTime size InRel (fun x s' => OutRel (f x) s') P T :=
  h

/-- Every `ComputesArrRelInTime` program runs from `initState (encIn x)` in time `C * T (size x)`. -/
theorem ComputesArrRelInTime.exec_initState {α : Type*} {size : α → ℕ} {encIn : α → List ℕ}
    {OutRel : α → List ℕ → Prop} {P : Cmd} {T : ℕ → ℕ}
    (h : ComputesArrRelInTime size encIn OutRel P T) :
    ∃ C c : ℕ, ∀ x : α, ∃ s' t,
      Exec (wordSize c (size x)) P (initState (encIn x)) s' t ∧
      t ≤ C * T (size x) ∧ OutRel x (s'.arrs outArr) := by
  rcases h with ⟨C, c, _, _, hexec⟩
  exact ⟨C, c, fun x => hexec x (initState (encIn x)) rfl⟩

/-- Monotonicity of `ComputesRelInTime` in the time bound `T`. -/
theorem ComputesRelInTime.mono_time {α : Type*} {size : α → ℕ} {InRel : α → State → Prop}
    {OutRel : α → State → Prop} {P : Cmd} {T₁ T₂ : ℕ → ℕ}
    (h : ComputesRelInTime size InRel OutRel P T₁)
    {K : ℕ} (hK : 1 ≤ K) (hle : ∀ n, T₁ n ≤ K * T₂ n) :
    ComputesRelInTime size InRel OutRel P T₂ := by
  rcases h with ⟨C, c, hC, hc, hP⟩
  refine ⟨C * K, c, Nat.mul_pos hC hK, hc, fun x s hs => ?_⟩
  rcases hP x s hs with ⟨s', t, hexec, ht, hout⟩
  refine ⟨s', t, hexec, ?_, hout⟩
  calc t ≤ C * T₁ (size x) := ht
    _ ≤ C * (K * T₂ (size x)) := Nat.mul_le_mul_left C (hle (size x))
    _ = (C * K) * T₂ (size x) := (Nat.mul_assoc C K _).symm

/-- Sequential composition of two `ComputesRelInTime` stages sharing the same input `x : α`. -/
theorem ComputesRelInTime.seq_same {α : Type*} {size : α → ℕ}
    {InRel MidRel OutRel : α → State → Prop} {P₁ P₂ : Cmd} {T₁ T₂ T : ℕ → ℕ}
    (h₁ : ComputesRelInTime size InRel MidRel P₁ T₁)
    (h₂ : ComputesRelInTime size MidRel OutRel P₂ T₂)
    (hT : ∀ x, T₁ (size x) + T₂ (size x) ≤ T (size x)) :
    ComputesRelInTime size InRel OutRel (.seq P₁ P₂) T := by
  rcases h₁ with ⟨C₁, c₁, hC₁, hc₁, hP₁⟩
  rcases h₂ with ⟨C₂, c₂, hC₂, hc₂, hP₂⟩
  refine ⟨C₁ + C₂, c₁ + c₂, by omega, by omega, fun x s hs => ?_⟩
  rcases hP₁ x s hs with ⟨s₁, t₁, hexec₁, ht₁, hmid⟩
  rcases hP₂ x s₁ hmid with ⟨s₂, t₂, hexec₂, ht₂, hout⟩
  have hw₁ : wordSize c₁ (size x) ≤ wordSize (c₁ + c₂) (size x) :=
    wordSize_mono_left (by omega) _
  have hw₂ : wordSize c₂ (size x) ≤ wordSize (c₁ + c₂) (size x) :=
    wordSize_mono_left (by omega) _
  refine ⟨s₂, t₁ + t₂, .seq (hexec₁.mono_wordSize hw₁) (hexec₂.mono_wordSize hw₂), ?_, hout⟩
  have hbound := hT x
  calc t₁ + t₂ ≤ C₁ * T₁ (size x) + C₂ * T₂ (size x) := Nat.add_le_add ht₁ ht₂
    _ ≤ (C₁ + C₂) * T₁ (size x) + (C₁ + C₂) * T₂ (size x) := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_right _ (by omega)
      · exact Nat.mul_le_mul_right _ (by omega)
    _ = (C₁ + C₂) * (T₁ (size x) + T₂ (size x)) := (Nat.mul_add _ _ _).symm
    _ ≤ (C₁ + C₂) * T (size x) := Nat.mul_le_mul_left _ hbound

end GraphMinor.Compute
