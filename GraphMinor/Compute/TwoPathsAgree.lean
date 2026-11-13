module

public import GraphMinor.Compute.TwoPathsRun

/-!
# Runs that agree where a program looks

A Word RAM program reads and writes only the registers and arrays that occur in it
(`Cmd.usedRegs`, `Cmd.usedArrs`). So two states that agree on a set of registers and arrays that
contains these give runs that agree on that set, with the same number of steps
(`Exec.congr_used`). The interpreter `Cmd.run` also finds every run once it has enough fuel
(`Cmd.run_complete`).

These two facts let a functional model be defined by running a program from a fixed state
(`GraphMinor/Compute/TwoPathsBfs.lean`), and be compared with a run of the same program inside a
larger computation.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The registers that occur in an expression. -/
def Expr.usedRegs : Expr → Finset Reg
  | .const _ => ∅
  | .reg r => {r}
  | .read _ idx => idx.usedRegs
  | .readMin _ idx cap => idx.usedRegs ∪ cap.usedRegs
  | .len _ => ∅
  | .op _ e₁ e₂ => e₁.usedRegs ∪ e₂.usedRegs

/-- The arrays that occur in an expression. -/
def Expr.usedArrs : Expr → Finset Arr
  | .const _ => ∅
  | .reg _ => ∅
  | .read a idx => insert a idx.usedArrs
  | .readMin a idx cap => insert a (idx.usedArrs ∪ cap.usedArrs)
  | .len a => {a}
  | .op _ e₁ e₂ => e₁.usedArrs ∪ e₂.usedArrs

/-- The registers that occur in a command. -/
def Cmd.usedRegs : Cmd → Finset Reg
  | .skip => ∅
  | .assign r e => insert r e.usedRegs
  | .write _ idx val => idx.usedRegs ∪ val.usedRegs
  | .alloc _ len => len.usedRegs
  | .seq c₁ c₂ => c₁.usedRegs ∪ c₂.usedRegs
  | .ite e c₁ c₂ => e.usedRegs ∪ (c₁.usedRegs ∪ c₂.usedRegs)
  | .while e body => e.usedRegs ∪ body.usedRegs

/-- The arrays that occur in a command. -/
def Cmd.usedArrs : Cmd → Finset Arr
  | .skip => ∅
  | .assign _ e => e.usedArrs
  | .write a idx val => insert a (idx.usedArrs ∪ val.usedArrs)
  | .alloc a len => insert a len.usedArrs
  | .seq c₁ c₂ => c₁.usedArrs ∪ c₂.usedArrs
  | .ite e c₁ c₂ => e.usedArrs ∪ (c₁.usedArrs ∪ c₂.usedArrs)
  | .while e body => e.usedArrs ∪ body.usedArrs

/-- `s` and `s'` agree on the registers `R` and the arrays `A`. -/
def AgreeOn (R : Set Reg) (A : Set Arr) (s s' : State) : Prop :=
  (∀ r ∈ R, s'.regs r = s.regs r) ∧ ∀ a ∈ A, s'.arrs a = s.arrs a

end GraphMinor.Compute

end

namespace GraphMinor.Compute

public section

theorem Expr.eval_congr {w : ℕ} {R : Set Reg} {A : Set Arr} {s s' : State} (h : AgreeOn R A s s') :
    ∀ e : Expr, (∀ r ∈ e.usedRegs, r ∈ R) → (∀ a ∈ e.usedArrs, a ∈ A) →
      e.eval w s' = e.eval w s
  | .const _, _, _ => rfl
  | .reg r, hR, _ => by simp [Expr.eval, h.1 r (hR r (by simp [Expr.usedRegs]))]
  | .read a idx, hR, hA => by
    have hi := Expr.eval_congr (w := w) h idx (by simpa [Expr.usedRegs] using hR)
      (fun x hx => hA x (by simp [Expr.usedArrs, hx]))
    have ha := h.2 a (hA a (by simp [Expr.usedArrs]))
    simp only [Expr.eval, hi, ha]
  | .readMin a idx cap, hR, hA => by
    have hi := Expr.eval_congr (w := w) h idx (fun x hx => hR x (by simp [Expr.usedRegs, hx]))
      (fun x hx => hA x (by simp [Expr.usedArrs, hx]))
    have hc := Expr.eval_congr (w := w) h cap (fun x hx => hR x (by simp [Expr.usedRegs, hx]))
      (fun x hx => hA x (by simp [Expr.usedArrs, hx]))
    have ha := h.2 a (hA a (by simp [Expr.usedArrs]))
    simp only [Expr.eval, hi, hc, ha]
  | .len a, _, hA => by simp [Expr.eval, h.2 a (hA a (by simp [Expr.usedArrs]))]
  | .op _ e₁ e₂, hR, hA => by
    have h₁ := Expr.eval_congr (w := w) h e₁ (fun x hx => hR x (by simp [Expr.usedRegs, hx]))
      (fun x hx => hA x (by simp [Expr.usedArrs, hx]))
    have h₂ := Expr.eval_congr (w := w) h e₂ (fun x hx => hR x (by simp [Expr.usedRegs, hx]))
      (fun x hx => hA x (by simp [Expr.usedArrs, hx]))
    simp only [Expr.eval, h₁, h₂]

theorem AgreeOn.setReg {R : Set Reg} {A : Set Arr} {s s' : State} (h : AgreeOn R A s s') (r : Reg)
    (v : ℕ) : AgreeOn R A (s.setReg r v) (s'.setReg r v) :=
  ⟨fun x hx => by by_cases hxr : x = r <;> simp [State.setReg, hxr, h.1 x hx],
   fun a ha => by simp [h.2 a ha]⟩

theorem AgreeOn.setArr {R : Set Reg} {A : Set Arr} {s s' : State} (h : AgreeOn R A s s') (a : Arr)
    (l : List ℕ) : AgreeOn R A (s.setArr a l) (s'.setArr a l) :=
  ⟨fun x hx => by simp [h.1 x hx],
   fun x hx => by by_cases hxa : x = a <;> simp [State.setArr, hxa, h.2 x hx]⟩

/-- **Runs agree where the program looks.** If `s` and `s'` agree on registers `R` and arrays `A`
that contain all those occurring in `c`, a run of `c` from `s` gives a run from `s'` with the same
number of steps, ending in a state that agrees with the first end state on `R` and `A`. -/
theorem Exec.congr_used {w : ℕ} {R : Set Reg} {A : Set Arr} {c : Cmd} {s s₁ : State} {t : ℕ}
    (h : Exec w c s s₁ t) (hR : ∀ r ∈ c.usedRegs, r ∈ R) (hA : ∀ a ∈ c.usedArrs, a ∈ A)
    {s' : State} (hs : AgreeOn R A s s') :
    ∃ s₁', Exec w c s' s₁' t ∧ AgreeOn R A s₁ s₁' := by
  induction h generalizing s' with
  | skip => exact ⟨s', .skip _, hs⟩
  | @assign r e s v he =>
    have he' := Expr.eval_congr (w := w) hs e (fun x hx => hR x (by simp [Cmd.usedRegs, hx]))
      (fun x hx => hA x (by simpa [Cmd.usedArrs] using hx))
    refine ⟨s'.setReg r v, .assign (he' ▸ he), ?_⟩
    exact hs.setReg r v
  | @write a idx val s i v hi hv hb =>
    have hi' := Expr.eval_congr (w := w) hs idx (fun x hx => hR x (by simp [Cmd.usedRegs, hx]))
      (fun x hx => hA x (by simp [Cmd.usedArrs, hx]))
    have hv' := Expr.eval_congr (w := w) hs val (fun x hx => hR x (by simp [Cmd.usedRegs, hx]))
      (fun x hx => hA x (by simp [Cmd.usedArrs, hx]))
    have ha := hs.2 a (hA a (by simp [Cmd.usedArrs]))
    refine ⟨s'.writeArr a i v, .write (hi' ▸ hi) (hv' ▸ hv) (by rw [ha]; exact hb), ?_⟩
    simp only [State.writeArr, ha]
    exact hs.setArr a _
  | @alloc a len s m hm =>
    have hm' := Expr.eval_congr (w := w) hs len (fun x hx => hR x (by simpa [Cmd.usedRegs] using hx))
      (fun x hx => hA x (by simp [Cmd.usedArrs, hx]))
    exact ⟨_, .alloc (hm' ▸ hm), hs.setArr a _⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨s₁', h₁, hs₁⟩ := ih₁ (fun x hx => hR x (by simp [Cmd.usedRegs, hx]))
      (fun x hx => hA x (by simp [Cmd.usedArrs, hx])) hs
    obtain ⟨s₂', h₂, hs₂⟩ := ih₂ (fun x hx => hR x (by simp [Cmd.usedRegs, hx]))
      (fun x hx => hA x (by simp [Cmd.usedArrs, hx])) hs₁
    exact ⟨s₂', .seq h₁ h₂, hs₂⟩
  | @ite_true cond c₁ c₂ s s₁ v t hc hv _ ih =>
    have hc' := Expr.eval_congr (w := w) hs cond (fun x hx => hR x (by simp [Cmd.usedRegs, hx]))
      (fun x hx => hA x (by simp [Cmd.usedArrs, hx]))
    obtain ⟨s₁', h₁, hs₁⟩ := ih (fun x hx => hR x (by simp [Cmd.usedRegs, hx]))
      (fun x hx => hA x (by simp [Cmd.usedArrs, hx])) hs
    exact ⟨s₁', .ite_true (hc' ▸ hc) hv h₁, hs₁⟩
  | @ite_false cond c₁ c₂ s s₁ t hc _ ih =>
    have hc' := Expr.eval_congr (w := w) hs cond (fun x hx => hR x (by simp [Cmd.usedRegs, hx]))
      (fun x hx => hA x (by simp [Cmd.usedArrs, hx]))
    obtain ⟨s₁', h₁, hs₁⟩ := ih (fun x hx => hR x (by simp [Cmd.usedRegs, hx]))
      (fun x hx => hA x (by simp [Cmd.usedArrs, hx])) hs
    exact ⟨s₁', .ite_false (hc' ▸ hc) h₁, hs₁⟩
  | @while_false cond body s hc =>
    have hc' := Expr.eval_congr (w := w) hs cond (fun x hx => hR x (by simp [Cmd.usedRegs, hx]))
      (fun x hx => hA x (by simp [Cmd.usedArrs, hx]))
    exact ⟨s', .while_false (hc' ▸ hc), hs⟩
  | @while_true cond body s s₁ s₂ v t₁ t₂ hc hv _ _ ih₁ ih₂ =>
    have hc' := Expr.eval_congr (w := w) hs cond (fun x hx => hR x (by simp [Cmd.usedRegs, hx]))
      (fun x hx => hA x (by simp [Cmd.usedArrs, hx]))
    obtain ⟨s₁', h₁, hs₁⟩ := ih₁ (fun x hx => hR x (by simp [Cmd.usedRegs, hx]))
      (fun x hx => hA x (by simp [Cmd.usedArrs, hx])) hs
    obtain ⟨s₂', h₂, hs₂⟩ := ih₂ hR hA hs₁
    exact ⟨s₂', .while_true (hc' ▸ hc) hv h₁ h₂, hs₂⟩

/-- **The interpreter finds every run.** With at least as much fuel as the run has steps,
`Cmd.run` returns the end state and the number of steps of the run. -/
theorem Cmd.run_complete {w : ℕ} {c : Cmd} {s s' : State} {t : ℕ} (h : Exec w c s s' t) :
    ∀ fuel, t ≤ fuel → Cmd.run w fuel c s = some (s', t) := by
  induction h with
  | skip => intro f hf; obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩; rfl
  | assign he =>
    intro f hf; obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by have := Expr.cost_pos ‹_›; omega⟩
    simp [Cmd.run, he]
  | write hi hv hb =>
    intro f hf; obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [Cmd.run, hi, hv, hb]
  | alloc hm =>
    intro f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by have := Expr.cost_pos ‹_›; omega⟩
    simp [Cmd.run, hm]
  | seq h₁ h₂ ih₁ ih₂ =>
    intro f hf
    have := h₁.time_pos; have := h₂.time_pos
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [Cmd.run, ih₁ f (by omega), ih₂ f (by omega)]
  | @ite_true cond c₁ c₂ s s₁ v t hc hv h₁ ih =>
    intro f hf
    have := h₁.time_pos; have := Expr.cost_pos cond
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨v, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
    simp [Cmd.run, hc, ih f (by omega)]
  | @ite_false cond c₁ c₂ s s₁ t hc h₁ ih =>
    intro f hf
    have := h₁.time_pos; have := Expr.cost_pos cond
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [Cmd.run, hc, ih f (by omega)]
  | @while_false cond body s hc =>
    intro f hf
    have := Expr.cost_pos cond
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [Cmd.run, hc]
  | @while_true cond body s s₁ s₂ v t₁ t₂ hc hv h₁ h₂ ih₁ ih₂ =>
    intro f hf
    have := h₁.time_pos; have := h₂.time_pos; have := Expr.cost_pos cond
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨v, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
    simp [Cmd.run, hc, ih₁ f (by omega), ih₂ f (by omega)]

end

end GraphMinor.Compute
