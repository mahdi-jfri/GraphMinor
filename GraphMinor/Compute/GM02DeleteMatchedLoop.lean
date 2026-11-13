module

public import GraphMinor.Compute.GM02MatchedLoopDeletion
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Clearing the host loop and its matching pattern loop

Clear the host edge flag at the saved host position. If the matching
pattern-loop scan returned an actual position rather than its edge-count
sentinel, clear that pattern flag too. These are the actual writes whose
mathematical meaning is proved by the matched-loop deletion lemma.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Delete the host edge at position 32 and the matching pattern edge returned in register 41. -/
def gm02DeleteMatchedLoopProg : Cmd :=
  .seq (.write 20 (.reg 32) (.const 0))
    (.ite (.op .lt (.reg 41) (.reg 15)) (.write 21 (.reg 41) (.const 0)) .skip)

/-- The actual flag writes implement matched loop deletion in at most nine steps. -/
theorem gm02DeleteMatchedLoopProg_exec {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (gflags hflags : List ℕ) (e v : ℕ)
    (hG : s.arrs 20 = gflags) (hH : s.arrs 21 = hflags)
    (he : e < gflags.length) (hHlen : hflags.length = x.edges.length)
    (hE : s.regs 32 = e) (hM : s.regs 15 = x.edges.length)
    (hresult : s.regs 41 = ((gm02FindPatternLoop x hflags v).map Fin.val).getD x.edges.length)
    (hw : 1 < 2 ^ w) (hEw : e < 2 ^ w) (hMw : x.edges.length < 2 ^ w) :
    ∃ s' t, Exec w gm02DeleteMatchedLoopProg s s' t ∧ t ≤ 9 ∧
      s'.arrs 20 = gflags.set e 0 ∧ s'.arrs 21 = gm02MatchedPatternFlags x hflags v ∧
      s'.regs = s.regs ∧ (∀ a, a ≠ 20 → a ≠ 21 → s'.arrs a = s.arrs a) := by
  let s₁ := s.writeArr 20 e 0
  have he₁ : Exec w (.write 20 (.reg 32) (.const 0)) s s₁ 3 :=
    .write (eval_reg hE hEw) (eval_const (Nat.two_pow_pos w)) (by rw [hG]; exact he)
  cases hfind : gm02FindPatternLoop x hflags v with
  | none =>
    have hz : s.regs 41 = x.edges.length := by simpa only [hfind, Option.map_none, Option.getD_none] using hresult
    have hcond : (Expr.op .lt (.reg 41) (.reg 15)).eval w s₁ = some 0 := by
      simpa only [Nat.lt_irrefl, ↓reduceIte] using
        eval_lt (eval_reg (s := s₁) hz hMw) (eval_reg (s := s₁) hM hMw) hw
    have he₂ : Exec w (.ite (.op .lt (.reg 41) (.reg 15)) (.write 21 (.reg 41) (.const 0)) .skip) s₁ s₁ 4 :=
      .ite_false hcond (.skip s₁)
    refine ⟨s₁, 7, .seq he₁ he₂, by decide, ?_, ?_, rfl, ?_⟩
    · simp only [s₁, State.writeArr_arrs_self, hG]
    · simp only [gm02MatchedPatternFlags, hfind]
      exact (State.writeArr_arrs_ne s e 0 (by decide : 21 ≠ 20)).trans hH
    · intro a ha20 _
      exact State.writeArr_arrs_ne _ _ _ ha20
  | some f =>
    have hz : s.regs 41 = f.val := by simpa only [hfind, Option.map_some, Option.getD_some] using hresult
    have hfw : f.val < 2 ^ w := f.isLt.trans hMw
    have hcond : (Expr.op .lt (.reg 41) (.reg 15)).eval w s₁ = some 1 := by
      simpa only [f.isLt, ↓reduceIte] using
        eval_lt (eval_reg (s := s₁) hz hfw) (eval_reg (s := s₁) hM hMw) hw
    let s₂ := s₁.writeArr 21 f.val 0
    have heWrite : Exec w (.write 21 (.reg 41) (.const 0)) s₁ s₂ 3 :=
      .write (eval_reg hz hfw) (eval_const (Nat.two_pow_pos w)) (by
        simp only [s₁, State.writeArr_arrs_ne _ _ _ (by decide : 21 ≠ 20), hH, hHlen]
        exact f.isLt)
    have he₂ : Exec w (.ite (.op .lt (.reg 41) (.reg 15)) (.write 21 (.reg 41) (.const 0)) .skip) s₁ s₂ 6 :=
      .ite_true hcond (by decide : 1 ≠ 0) heWrite
    refine ⟨s₂, 9, .seq he₁ he₂, le_rfl, ?_, ?_, rfl, ?_⟩
    · simp only [s₂, s₁, State.writeArr_arrs_ne _ _ _ (by decide : 20 ≠ 21), State.writeArr_arrs_self, hG]
    · simp only [gm02MatchedPatternFlags, hfind, s₂, State.writeArr_arrs_self,
        s₁, State.writeArr_arrs_ne _ _ _ (by decide : 21 ≠ 20), hH]
    · intro a ha20 ha21
      simp only [s₂, s₁, State.writeArr_arrs_ne _ _ _ ha20, State.writeArr_arrs_ne _ _ _ ha21]

end GraphMinor.Compute
