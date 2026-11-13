module

public import GraphMinor.Compute.Basic

/-!
# Finite execution prefixes of the alternating-recursion loop

The recursive machine uses one loop and saved frames. A child call is
a finite prefix of that loop ending when its answer is ready, before
the parent continuation runs. Prefixes compose with exact time sums,
and a prefix ending at a false guard gives a complete loop execution.
-/

public section
namespace GraphMinor.Compute

/-- A finite sequence of guarded body executions, without requiring the loop to stop. -/
inductive GM02LoopPrefix (w : ℕ) (guard : Expr) (body : Cmd) : State → State → ℕ → Prop where
  | refl (s : State) : GM02LoopPrefix w guard body s s 0
  | step {s mid last : State} {v t_body t_rest : ℕ}
      (hguard : guard.eval w s = some v) (hv : v ≠ 0)
      (hbody : Exec w body s mid t_body) (hrest : GM02LoopPrefix w guard body mid last t_rest) :
      GM02LoopPrefix w guard body s last (guard.cost + t_body + t_rest)

/-- Concatenating loop prefixes adds their exact execution times. -/
theorem GM02LoopPrefix.trans {w : ℕ} {guard : Expr} {body : Cmd}
    {s mid last : State} {t u : ℕ} (h : GM02LoopPrefix w guard body s mid t)
    (h' : GM02LoopPrefix w guard body mid last u) : GM02LoopPrefix w guard body s last (t + u) := by
  induction h with
  | refl => simpa only [Nat.zero_add] using h'
  | step hg hv hb _ ih =>
    simpa only [Nat.add_assoc] using GM02LoopPrefix.step hg hv hb (ih h')

/-- One guarded body execution is a loop prefix. -/
theorem GM02LoopPrefix.single {w : ℕ} {guard : Expr} {body : Cmd}
    {s s' : State} {v t : ℕ} (hg : guard.eval w s = some v) (hv : v ≠ 0)
    (hb : Exec w body s s' t) : GM02LoopPrefix w guard body s s' (guard.cost + t) := by
  simpa only [Nat.add_zero] using GM02LoopPrefix.step hg hv hb (GM02LoopPrefix.refl s')

/-- A prefix followed by a full loop execution is a full loop execution. -/
theorem GM02LoopPrefix.to_exec {w : ℕ} {guard : Expr} {body : Cmd}
    {s mid last : State} {t u : ℕ} (h : GM02LoopPrefix w guard body s mid t)
    (h' : Exec w (.while guard body) mid last u) : Exec w (.while guard body) s last (t + u) := by
  induction h with
  | refl => simpa only [Nat.zero_add] using h'
  | step hg hv hb _ ih =>
    simpa only [Nat.add_assoc] using Exec.while_true hg hv hb (ih h')

/-- A prefix whose final guard is false gives a complete terminating loop run. -/
theorem GM02LoopPrefix.finish {w : ℕ} {guard : Expr} {body : Cmd}
    {s last : State} {t : ℕ} (h : GM02LoopPrefix w guard body s last t)
    (hg : guard.eval w last = some 0) : Exec w (.while guard body) s last (t + guard.cost) :=
  h.to_exec (Exec.while_false hg)

end GraphMinor.Compute
