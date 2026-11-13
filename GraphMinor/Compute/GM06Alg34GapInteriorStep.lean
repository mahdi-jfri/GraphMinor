module

public import GraphMinor.Compute.GM06Alg34GapInteriorStepData
public import GraphMinor.Compute.GM06Alg34GapInteriorUpdate
public import GraphMinor.Compute.GM06Alg34GapInteriorFindFrames
import Mathlib.Tactic.Ring

/-!
# One complete interior-component reduction step on the RAM

Search the supplied graph for a component away from its cuff. If the
search succeeds, install that component's exact augmented deletion
payload. Otherwise retain both input arrays. Register 6600 records
whether a deletion occurred, so the driver can continue reducing or
move to the remaining cases of VI (3.3).
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Search and perform one interior deletion, recording success in 6600. -/
def gm06GapInteriorStepProg : Cmd :=
  .seq gm06InteriorFindProg
    (.ite (.reg 113) (.seq gm06GapInteriorUpdateProg (.assign 6600 (.const 1)))
      (.assign 6600 (.const 0)))

private theorem step_budget (n : ℕ) :
    600 * (n + 1) ^ 3 + 1300 * (n + 2) ^ 3 + 3 ≤ 2000 * (n + 2) ^ 3 := by
  ring_nf
  omega

/-- The full search/deletion step computes exactly its finite augmented
result and success flag in cubic time, with arbitrary initial scratch. -/
theorem gm06GapInteriorStepProg_exec (X : GM06GapInput)
    (hshape : ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧ R.length = L.length)
    {c : ℕ} (hc : 3 ≤ c) {s : State} (hinput : s.arrs 0 = X.drawing.words)
    (hgap : s.arrs 47 = X.discGapWords) :
    ∃ s' t, Exec (wordSize c X.drawing.size) gm06GapInteriorStepProg s s' t ∧
      t ≤ 2000 * (X.drawing.size + 2) ^ 3 ∧
      s'.arrs 0 = X.interiorStepData.drawing.words ∧ s'.arrs 47 = X.interiorStepData.discGapWords ∧
      s'.regs 6600 = (if X.drawing.findInteriorComponent.isSome then 1 else 0) ∧
      (∀ A : ℕ, 50 ≤ A → s'.arrs A = s.arrs A) := by
  have hc2 : 2 ≤ c := by omega
  have hsize : X.drawing.size < 2 ^ wordSize c X.drawing.size :=
    lt_two_pow_wordSize_of_le (by omega) (Nat.le_succ _)
  have hw : 1 < 2 ^ wordSize c X.drawing.size := by
    have hh := X.drawing.five_le_words_length
    have hle := X.drawing.words_length_le_size
    omega
  obtain ⟨L, R, hL, hR, hlen⟩ := hshape
  obtain ⟨s₁, t₁, he₁, ht₁, hfound, hin₁, hadj, hlen₁, hn, _, _⟩ :=
    gm06InteriorFindProg_exec X.drawing hL hc2 hinput
  have hgap₁ : s₁.arrs 47 = X.discGapWords :=
    (gm06GapInteriorFind_array_frame he₁ (by decide)).trans hgap
  cases hf : X.drawing.findInteriorComponent with
  | none =>
    have hz : s₁.regs 113 = 0 := by
      simpa only [hf, Option.map_none, gm06SingletonRegs, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte] using hfound.1
    have hcond : (Expr.reg 113).eval (wordSize c X.drawing.size) s₁ = some 0 := by
      simp [Expr.eval, checkWord, hz, Nat.zero_lt_of_lt hw]
    let s₂ := s₁.setReg 6600 0
    have he₂ : Exec (wordSize c X.drawing.size) (.assign 6600 (.const 0)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
    refine ⟨s₂, t₁ + 3, .seq he₁ (.ite_false hcond he₂),
      (show t₁ + 3 ≤ 600 * (X.drawing.size + 1) ^ 3 + 1300 * (X.drawing.size + 2) ^ 3 + 3 by omega).trans
        (step_budget X.drawing.size), ?_, ?_, ?_, ?_⟩
    · rw [GM06GapInput.interiorStepData, hf]
      exact hin₁
    · rw [GM06GapInput.interiorStepData, hf]
      exact hgap₁
    · simp only [s₂, State.setReg_regs_self, hf, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    · intro A hA
      exact gm06GapInteriorFind_array_frame he₁ (by omega)
  | some a =>
    have hflag : s₁.regs 113 = 1 := by simpa [hf, gm06SingletonRegs] using hfound.1
    have hsel : s₁.regs 114 = a.val := hfound.2 _ (by simp [hf])
    have hcond : (Expr.reg 113).eval (wordSize c X.drawing.size) s₁ = some 1 := by
      simp [Expr.eval, checkWord, hflag, hw]
    obtain ⟨s₂, t₂, he₂, ht₂, hin₂, hgap₂, harr₂⟩ :=
      gm06GapInteriorUpdateProg_exec_input X a ⟨L, R, hL, hR, hlen⟩ hc hin₁ hgap₁ hsel hn hadj hlen₁
    let s₃ := s₂.setReg 6600 1
    have he₃ : Exec (wordSize c X.drawing.size) (.assign 6600 (.const 1)) s₂ s₃ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw])
    refine ⟨s₃, t₁ + (1 + (t₂ + 2)), .seq he₁ (.ite_true hcond (by decide) (.seq he₂ he₃)),
      (show t₁ + (1 + (t₂ + 2)) ≤ 600 * (X.drawing.size + 1) ^ 3 +
        1300 * (X.drawing.size + 2) ^ 3 + 3 by omega).trans (step_budget X.drawing.size), ?_, ?_, ?_, ?_⟩
    · rw [GM06GapInput.interiorStepData, hf]
      exact hin₂
    · rw [GM06GapInput.interiorStepData, hf]
      exact hgap₂
    · simp only [s₃, State.setReg_regs_self, hf, Option.isSome_some, ↓reduceIte]
    · intro A hA
      exact (harr₂ A hA).trans (gm06GapInteriorFind_array_frame he₁ (by omega))

end GraphMinor.Compute
