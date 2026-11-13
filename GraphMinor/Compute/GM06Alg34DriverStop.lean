module

public import GraphMinor.Compute.GM06Alg34Driver

/-!
# Exact execution of the driver's stopping command

Stopping saves a Boolean answer and clears the running flag. Both
assignments have fixed cost, retain every array and preserve all other
registers. These facts discharge the terminal cases of the queue loop.
-/

public section
namespace GraphMinor.Compute

/-- The driver's stopping command takes four steps and retains all arrays. -/
theorem gm06DriverStop_exec {w : ℕ} (hw : 1 < 2 ^ w) (b : Bool) (s : State) :
    ∃ s', Exec w (gm06DriverStop b) s s' 4 ∧
      s'.regs 9000 = 0 ∧ s'.regs 9001 = (if b then 1 else 0) ∧
      (∀ A : ℕ, s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 9000 → q ≠ 9001 → s'.regs q = s.regs q) := by
  let v : ℕ := if b then 1 else 0
  have hv : v < 2 ^ w := by cases b <;> simp only [v, Bool.false_eq_true, ↓reduceIte] <;> omega
  let s₁ := s.setReg 9001 v
  let s₂ := s₁.setReg 9000 0
  have he₁ : Exec w (.assign 9001 (.const v)) s s₁ 2 :=
    .assign (by simp only [Expr.eval, checkWord_of_lt hv])
  have he₂ : Exec w (.assign 9000 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord_of_lt (by omega : 0 < 2 ^ w)])
  refine ⟨s₂, .seq he₁ he₂, rfl, ?_, fun _ => rfl, ?_⟩
  · exact State.setReg_regs_ne _ _ (by decide)
  · intro q hq hq'
    exact (State.setReg_regs_ne _ _ hq).trans (State.setReg_regs_ne _ _ hq')

end GraphMinor.Compute
