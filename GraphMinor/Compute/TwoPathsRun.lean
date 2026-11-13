module

public import GraphMinor.Compute.Basic

/-!
# A step-bounded interpreter for Word RAM programs

`Cmd.run w fuel c s` runs the command `c` from the state `s` with word size `w`. The number `fuel`
bounds the depth of the run: each command, and each round of a loop, uses one unit. The result is
the final state and the number of steps, or `none` when the fuel runs out or the run fails.
`Cmd.run_sound` says that a result of `Cmd.run` is a run of the semantics `Exec`.

The interpreter is used to run the programs of the two-paths algorithm on small examples in
`Checks/TwoPathsExamples.lean`; the kernel evaluates it, with `decide`.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Run `c` from `s` with at most `fuel` nested commands and loop rounds. -/
def Cmd.run (w : ℕ) : ℕ → Cmd → State → Option (State × ℕ)
  | 0, _, _ => none
  | _ + 1, .skip, s => some (s, 1)
  | _ + 1, .assign r e, s =>
    match e.eval w s with
    | some v => some (s.setReg r v, e.cost + 1)
    | none => none
  | _ + 1, .write a idx val, s =>
    match idx.eval w s, val.eval w s with
    | some i, some v => if i < (s.arrs a).length then some (s.writeArr a i v, idx.cost + val.cost + 1)
        else none
    | _, _ => none
  | _ + 1, .alloc a len, s =>
    match len.eval w s with
    | some m => some (s.setArr a (List.replicate m 0), len.cost + m)
    | none => none
  | f + 1, .seq c₁ c₂, s =>
    match Cmd.run w f c₁ s with
    | some (s₁, t₁) =>
      match Cmd.run w f c₂ s₁ with
      | some (s₂, t₂) => some (s₂, t₁ + t₂)
      | none => none
    | none => none
  | f + 1, .ite cond c₁ c₂, s =>
    match cond.eval w s with
    | some 0 =>
      match Cmd.run w f c₂ s with
      | some (s', t) => some (s', cond.cost + t)
      | none => none
    | some _ =>
      match Cmd.run w f c₁ s with
      | some (s', t) => some (s', cond.cost + t)
      | none => none
    | none => none
  | f + 1, .while cond body, s =>
    match cond.eval w s with
    | some 0 => some (s, cond.cost)
    | some _ =>
      match Cmd.run w f body s with
      | some (s₁, t₁) =>
        match Cmd.run w f (.while cond body) s₁ with
        | some (s₂, t₂) => some (s₂, cond.cost + t₁ + t₂)
        | none => none
      | none => none
    | none => none

/-- A result of the interpreter is a run of the semantics. -/
theorem Cmd.run_sound {w : ℕ} :
    ∀ (fuel : ℕ) (c : Cmd) (s s' : State) (t : ℕ), Cmd.run w fuel c s = some (s', t) →
      Exec w c s s' t := by
  intro fuel
  induction fuel with
  | zero => intro c s s' t h; simp [Cmd.run] at h
  | succ f ih =>
    intro c s s' t h
    cases c with
    | skip =>
      simp only [Cmd.run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .skip s
    | assign r e =>
      simp only [Cmd.run] at h
      split at h
      · rename_i v hv
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .assign hv
      · simp at h
    | write a idx val =>
      simp only [Cmd.run] at h
      split at h
      · rename_i i v hi hv
        split_ifs at h with hb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .write hi hv hb
      · simp at h
    | alloc a len =>
      simp only [Cmd.run] at h
      split at h
      · rename_i m hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .alloc hm
      · simp at h
    | seq c₁ c₂ =>
      simp only [Cmd.run] at h
      split at h
      · rename_i s₁ t₁ h₁
        split at h
        · rename_i s₂ t₂ h₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .seq (ih _ _ _ _ h₁) (ih _ _ _ _ h₂)
        · simp at h
      · simp at h
    | ite cond c₁ c₂ =>
      simp only [Cmd.run] at h
      split at h
      · rename_i hc
        split at h
        · rename_i s₁ t₁ h₁
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .ite_false hc (ih _ _ _ _ h₁)
        · simp at h
      · rename_i v hc hv
        split at h
        · rename_i s₁ t₁ h₁
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .ite_true hv hc (ih _ _ _ _ h₁)
        · simp at h
      · simp at h
    | «while» cond body =>
      simp only [Cmd.run] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .while_false hc
      · rename_i v hc hv
        split at h
        · rename_i s₁ t₁ h₁
          split at h
          · rename_i s₂ t₂ h₂
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .while_true hv hc (ih _ _ _ _ h₁) (ih _ _ _ _ h₂)
          · simp at h
        · simp at h
      · simp at h

end GraphMinor.Compute
