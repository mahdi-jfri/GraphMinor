module

public import GraphMinor.Compute.Basic

/-!
# Keeping the first singleton found by the RAM

Registers 113 and 114 store a found flag and the corresponding label.
After testing one block, retain an earlier answer if present. Otherwise
copy the new candidate from registers 112 and 111. This constant-time
command implements left-biased option combination and preserves all arrays.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The found flag and optional label stored by the singleton search. -/
def gm06SingletonRegs (found : Option ℕ) (s : State) : Prop :=
  s.regs 113 = (if found.isSome then 1 else 0) ∧ ∀ v, found = some v → s.regs 114 = v

/-- Keep an existing singleton label, or copy the current successful block test. -/
def gm06KeepSingletonProg : Cmd :=
  .ite (.reg 113) .skip
    (.ite (.reg 112)
      (.seq (.assign 113 (.const 1)) (.assign 114 (.reg 111))) .skip)

/-- The candidate-retaining command computes option combination in at
most six steps. It changes only the found flag and found label. -/
theorem gm06KeepSingletonProg_exec {w : ℕ} (found candidate : Option ℕ)
    (hw : 1 < 2 ^ w) (hcw : ∀ v, candidate = some v → v < 2 ^ w)
    {s : State} (hfound : gm06SingletonRegs found s)
    (hcflag : s.regs 112 = (if candidate.isSome then 1 else 0))
    (hclabel : ∀ v, candidate = some v → s.regs 111 = v) :
    ∃ s' t, Exec w gm06KeepSingletonProg s s' t ∧ t ≤ 6 ∧
      gm06SingletonRegs (found.or candidate) s' ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 113 → q ≠ 114 → s'.regs q = s.regs q) := by
  have h0 : 0 < 2 ^ w := by omega
  cases found with
  | some v =>
    have hr : s.regs 113 = 1 := hfound.1
    have hex : Exec w gm06KeepSingletonProg s s 2 :=
      .ite_true (v := 1) (by simp [Expr.eval, checkWord, hr, hw]) (by decide) (.skip s)
    exact ⟨s, 2, hex, by decide, hfound, fun _ => rfl, fun _ _ _ => rfl⟩
  | none =>
    have hr : s.regs 113 = 0 := hfound.1
    have he : (Expr.reg 113).eval w s = some 0 := by simp [Expr.eval, checkWord, hr, h0]
    cases candidate with
    | none =>
      have hc : s.regs 112 = 0 := hcflag
      have hex : Exec w gm06KeepSingletonProg s s 3 :=
        .ite_false he (.ite_false (by simp [Expr.eval, checkWord, hc, h0]) (.skip s))
      exact ⟨s, 3, hex, by decide, hfound, fun _ => rfl, fun _ _ _ => rfl⟩
    | some v =>
      have hc : s.regs 112 = 1 := hcflag
      have hv : s.regs 111 = v := hclabel v rfl
      have hvw := hcw v rfl
      let s₁ := s.setReg 113 1
      let s₂ := s₁.setReg 114 v
      have hex₁ : Exec w (.assign 113 (.const 1)) s s₁ 2 :=
        .assign (by simp [Expr.eval, checkWord, hw])
      have hex₂ : Exec w (.assign 114 (.reg 111)) s₁ s₂ 2 :=
        .assign (by simp [Expr.eval, checkWord, s₁, hv, hvw])
      have hex : Exec w gm06KeepSingletonProg s s₂ 6 :=
        .ite_false he (.ite_true (v := 1) (by simp [Expr.eval, checkWord, hc, hw]) (by decide)
          (.seq hex₁ hex₂))
      refine ⟨s₂, 6, hex, by decide, ⟨?_, ?_⟩, fun _ => rfl, ?_⟩
      · simp [s₂, s₁]
      · intro a ha
        have hva : v = a := Option.some.inj ha
        simpa [s₂] using hva
      · intro q hq113 hq114
        exact (State.setReg_regs_ne _ _ hq114).trans (State.setReg_regs_ne _ _ hq113)

end GraphMinor.Compute
