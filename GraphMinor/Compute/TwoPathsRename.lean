module

public import GraphMinor.Compute.Basic

/-!
# Renaming registers and arrays of a program

A program can be moved to other registers and arrays by an involution `f` of the addresses
(`renameCmd f`). A run of the renamed program from `renameState f s` is a run of the old program
from `s`, with the same time (`exec_renameCmd`). The loop of Algorithm 5.2 (`loopProg`) and the
search used by the extraction (`bfsHiProg`) are moved this way to the scratch space from `300` on.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

/-- Rename registers and arrays in an `Expr`. -/
def renameExpr (f : ℕ → ℕ) : Expr → Expr
  | .const n => .const n
  | .reg r => .reg (f r)
  | .read a idx => .read (f a) (renameExpr f idx)
  | .readMin a idx cap => .readMin (f a) (renameExpr f idx) (renameExpr f cap)
  | .len a => .len (f a)
  | .op bop e₁ e₂ => .op bop (renameExpr f e₁) (renameExpr f e₂)

/-- Rename registers and arrays in a `Cmd`. -/
def renameCmd (f : ℕ → ℕ) : Cmd → Cmd
  | .skip => .skip
  | .assign r e => .assign (f r) (renameExpr f e)
  | .write a idx val => .write (f a) (renameExpr f idx) (renameExpr f val)
  | .alloc a len => .alloc (f a) (renameExpr f len)
  | .seq c₁ c₂ => .seq (renameCmd f c₁) (renameCmd f c₂)
  | .ite cond c₁ c₂ => .ite (renameExpr f cond) (renameCmd f c₁) (renameCmd f c₂)
  | .while cond body => .while (renameExpr f cond) (renameCmd f body)

/-- Pull back a `State` along a renaming `f`. -/
def renameState (f : ℕ → ℕ) (s : State) : State where
  regs := fun r => s.regs (f r)
  arrs := fun a => s.arrs (f a)

@[simp]
theorem renameState_regs (f : ℕ → ℕ) (s : State) (r : ℕ) :
    (renameState f s).regs r = s.regs (f r) := rfl

@[simp]
theorem renameState_arrs (f : ℕ → ℕ) (s : State) (a : ℕ) :
    (renameState f s).arrs a = s.arrs (f a) := rfl

@[simp]
theorem cost_renameExpr (f : ℕ → ℕ) (e : Expr) : (renameExpr f e).cost = e.cost := by
  induction e <;> simp [renameExpr, Expr.cost, *]

theorem eval_renameExpr {f : ℕ → ℕ} (hf : Function.Involutive f) (w : ℕ) (s : State) (e : Expr) :
    (renameExpr f e).eval w (renameState f s) = e.eval w s := by
  induction e with
  | const n => rfl
  | reg r => simp [renameExpr, Expr.eval, hf r]
  | read a idx ih => simp [renameExpr, Expr.eval, hf a, ih]
  | readMin a idx cap ih₁ ih₂ => simp [renameExpr, Expr.eval, hf a, ih₁, ih₂]
  | len a => simp [renameExpr, Expr.eval, hf a]
  | op bop e₁ e₂ ih₁ ih₂ => simp [renameExpr, Expr.eval, ih₁, ih₂]

theorem renameState_setReg {f : ℕ → ℕ} (hf : Function.Involutive f) (s : State) (r v : ℕ) :
    renameState f (s.setReg r v) = (renameState f s).setReg (f r) v := by
  ext x
  · simp only [renameState, State.setReg, Function.update_apply]
    have : (f x = r) ↔ (x = f r) := ⟨fun h => by rw [← h, hf], fun h => by rw [h, hf]⟩
    simp [this]
  · rfl

theorem renameState_setArr {f : ℕ → ℕ} (hf : Function.Involutive f) (s : State) (a : ℕ) (l : List ℕ) :
    renameState f (s.setArr a l) = (renameState f s).setArr (f a) l := by
  ext x
  · rfl
  · simp only [renameState, State.setArr, Function.update_apply]
    have : (f x = a) ↔ (x = f a) := ⟨fun h => by rw [← h, hf], fun h => by rw [h, hf]⟩
    simp [this]

theorem renameState_writeArr {f : ℕ → ℕ} (hf : Function.Involutive f) (s : State) (a i v : ℕ) :
    renameState f (s.writeArr a i v) = (renameState f s).writeArr (f a) i v := by
  simp only [State.writeArr, renameState_setArr hf]
  congr 2
  simp [hf a]

theorem exec_renameCmd {f : ℕ → ℕ} (hf : Function.Involutive f) {w : ℕ} {c : Cmd} {s s' : State} {t : ℕ}
    (h : Exec w c s s' t) : Exec w (renameCmd f c) (renameState f s) (renameState f s') t := by
  induction h with
  | skip s => exact .skip (renameState f s)
  | assign he =>
    rw [renameState_setReg hf, ← cost_renameExpr f]
    exact .assign (by rw [eval_renameExpr hf]; exact he)
  | @write a idx val s₀ i v hi hv hbound =>
    rw [renameState_writeArr hf, ← cost_renameExpr f idx, ← cost_renameExpr f val]
    refine .write (by rw [eval_renameExpr hf]; exact hi)
      (by rw [eval_renameExpr hf]; exact hv) ?_
    simpa [hf a] using hbound
  | alloc hm =>
    rw [renameState_setArr hf, ← cost_renameExpr f]
    exact .alloc (by rw [eval_renameExpr hf]; exact hm)
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite_true hcond hv _ ih =>
    rw [← cost_renameExpr f]
    exact .ite_true (by rw [eval_renameExpr hf]; exact hcond) hv ih
  | ite_false hcond _ ih =>
    rw [← cost_renameExpr f]
    exact .ite_false (by rw [eval_renameExpr hf]; exact hcond) ih
  | while_false hcond =>
    rw [← cost_renameExpr f]
    exact .while_false (by rw [eval_renameExpr hf]; exact hcond)
  | while_true hcond hv _ _ ih₁ ih₂ =>
    rw [← cost_renameExpr f]
    exact .while_true (by rw [eval_renameExpr hf]; exact hcond) hv ih₁ ih₂

end GraphMinor.Compute.TwoPaths
