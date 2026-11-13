module

public import GraphMinor.Compute.Basic

/-!
# Loops run round by round, and a loop rule with a potential

A program whose main part is one `while` loop is often proved correct one stretch of rounds at a
time: a recursive algorithm run with an explicit stack is such a program, and the stretch of rounds
that solves one recursive call is proved by induction on the calls. `Rounds w cond body s s' t`
says that some number of rounds of the loop `while cond do body`, each one starting in a state
where `cond` holds, lead from `s` to `s'` in `t` steps in all. Stretches compose (`Rounds.trans`),
and a stretch followed by a run of the loop is a run of the loop (`Exec.while_of_rounds`).

`Exec.while_pot` is the loop rule with a potential on ghost data: if each round costs at most the
drop of the potential, the whole loop costs at most the potential at the start.

`Exec.arrs_lt` says that a run keeps every entry of an array below `2 ^ w`, if it was so at the
start: the machine writes only words.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Some rounds of the loop `while cond do body` lead from `s` to `s'` in `t` steps: each round
starts in a state where `cond` holds and runs `body`. -/
inductive Rounds (w : ℕ) (cond : Expr) (body : Cmd) : State → State → ℕ → Prop
  | refl (s : State) : Rounds w cond body s s 0
  | step {s s₁ s₂ : State} {v t₁ t₂ : ℕ} (hcond : cond.eval w s = some v) (hv : v ≠ 0)
      (hbody : Exec w body s s₁ t₁) (hrest : Rounds w cond body s₁ s₂ t₂) :
      Rounds w cond body s s₂ (cond.cost + t₁ + t₂)

namespace Rounds

variable {w : ℕ} {cond : Expr} {body : Cmd}

/-- One round. -/
theorem single {s s₁ : State} {v t : ℕ} (hcond : cond.eval w s = some v) (hv : v ≠ 0)
    (hbody : Exec w body s s₁ t) : Rounds w cond body s s₁ (cond.cost + t) := by
  have h := Rounds.step hcond hv hbody (Rounds.refl s₁)
  simpa using h

/-- Two stretches of rounds, one after the other. -/
theorem trans {s s₁ s₂ : State} {t₁ t₂ : ℕ} (h₁ : Rounds w cond body s s₁ t₁)
    (h₂ : Rounds w cond body s₁ s₂ t₂) : Rounds w cond body s s₂ (t₁ + t₂) := by
  induction h₁ with
  | refl => simpa using h₂
  | step hcond hv hbody _ ih =>
    have h := Rounds.step hcond hv hbody (ih h₂)
    convert h using 1
    omega

end Rounds

/-- Every entry of array `a` stays below `2 ^ w` in a run, since the machine writes only values
of expressions, which are words, and `alloc` writes zeros. -/
theorem Exec.arrs_lt {w : ℕ} {c : Cmd} {s s' : State} {t : ℕ} (h : Exec w c s s' t) (a : Arr)
    (hs : ∀ v ∈ s.arrs a, v < 2 ^ w) : ∀ v ∈ s'.arrs a, v < 2 ^ w := by
  induction h with
  | skip => exact hs
  | assign => exact hs
  | @write a' idx val s i v hi hv hbound =>
    intro x hx
    by_cases ha : a = a'
    · subst ha
      rw [State.writeArr, State.setArr_arrs_self] at hx
      rcases List.mem_or_eq_of_mem_set hx with h | h
      · exact hs x h
      · exact h ▸ Expr.eval_lt hv
    · rw [State.writeArr, State.setArr_arrs_ne _ _ ha] at hx
      exact hs x hx
  | @alloc a' len s m hm =>
    intro x hx
    by_cases ha : a = a'
    · subst ha
      rw [State.setArr_arrs_self] at hx
      rw [List.eq_of_mem_replicate hx]
      exact Nat.two_pow_pos w
    · rw [State.setArr_arrs_ne _ _ ha] at hx
      exact hs x hx
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hs)
  | ite_true _ _ _ ih => exact ih hs
  | ite_false _ _ ih => exact ih hs
  | while_false => exact hs
  | while_true _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hs)

/-- Every entry of array `a` stays below `2 ^ w` in some rounds. -/
theorem Rounds.arrs_lt {w : ℕ} {cond : Expr} {body : Cmd} {s s' : State} {t : ℕ}
    (h : Rounds w cond body s s' t) (a : Arr)
    (hs : ∀ v ∈ s.arrs a, v < 2 ^ w) : ∀ v ∈ s'.arrs a, v < 2 ^ w := by
  induction h with
  | refl => exact hs
  | step _ _ hbody _ ih => exact ih (hbody.arrs_lt a hs)

/-- A stretch of rounds followed by a run of the loop is a run of the loop. -/
theorem Exec.while_of_rounds {w : ℕ} {cond : Expr} {body : Cmd} {s s₁ s₂ : State} {t₁ t₂ : ℕ}
    (h : Rounds w cond body s s₁ t₁) (h' : Exec w (.while cond body) s₁ s₂ t₂) :
    Exec w (.while cond body) s s₂ (t₁ + t₂) := by
  induction h with
  | refl => simpa using h'
  | step hcond hv hbody _ ih =>
    have h := Exec.while_true hcond hv hbody (ih h')
    convert h using 1
    omega

/-- **A loop rule with a potential.** The invariant `I g s` and the potential `Φ g` depend on
ghost data `g`. If, from every state of the invariant where `cond` holds, the body leads to a state
of the invariant and the round (the test and the body) costs at most the drop of the potential,
then the loop stops in a state of the invariant where `cond` fails, and it costs at most the
potential at the start plus one last test. -/
theorem Exec.while_pot {w : ℕ} {α : Type*} {cond : Expr} {body : Cmd} (I : α → State → Prop)
    (Φ : α → ℕ)
    (hround : ∀ g s, I g s → ∃ v, cond.eval w s = some v ∧ (v ≠ 0 →
      ∃ g' s' t, Exec w body s s' t ∧ I g' s' ∧ cond.cost + t + Φ g' ≤ Φ g)) :
    ∀ g s, I g s → ∃ g' s' t, Exec w (.while cond body) s s' t ∧ I g' s' ∧
      cond.eval w s' = some 0 ∧ t + Φ g' ≤ Φ g + cond.cost := by
  intro g
  induction hk : Φ g using Nat.strong_induction_on generalizing g with
  | _ k ih =>
    intro s hs
    obtain ⟨v, hv, hstep⟩ := hround g s hs
    by_cases hv0 : v = 0
    · subst hv0
      exact ⟨g, s, _, .while_false hv, hs, hv, by omega⟩
    · obtain ⟨g', s', t, hex, hI', hle⟩ := hstep hv0
      have ht := hex.time_pos
      obtain ⟨g'', s'', t', hex', hI'', hc'', hle'⟩ := ih (Φ g') (by omega) g' rfl s' hI'
      exact ⟨g'', s'', _, .while_true hv hv0 hex hex', hI'', hc'', by omega⟩

end GraphMinor.Compute
