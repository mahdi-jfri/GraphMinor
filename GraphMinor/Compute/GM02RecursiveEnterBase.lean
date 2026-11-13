module

public import GraphMinor.Compute.GM02RecursiveEnterProgram

/-!
# Executing the exhaustive base case of A1 and A2

When the supplied graph has at most four times the fixed width many
vertices, the entry command selects the finite exhaustive program. It
returns the exact feasibility bit and switches to the return state,
leaving every array and the other recursive control registers intact.
-/

public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

/-- The machine's bounded entry branch executes exhaustion and prepares its exact answer. -/
theorem gm02RecursiveEnterProg_base_exec {w : ℕ} (q : ℕ) (x : GM02SimpleTerminatedInput)
    (s : State) (hsrc : s.arrs (gm02RecursiveParentArr q) = x.enc) (hsmall : x.n ≤ 4 * q)
    (hw : 4 + 2 * ((4 * q) * (4 * q)) + 4 * q < 2 ^ w) :
    ∃ s' t, Exec w (gm02RecursiveEnterProg q) s s' t ∧
      t ≤ (4 + 2 * ((4 * q) * (4 * q)) + 4 * q) *
        (4 * ((4 * q) * (4 * q) + 4 * q) + 10) + 6 ∧
      s'.regs outReg = (if x.A.Feasible (Graph.ofSimpleGraph x.G) then 1 else 0) ∧
      s'.regs (gm02RecursiveControlBase q + 18) = 3 ∧ s'.arrs = s.arrs ∧
      (∀ offset, offset ≠ 18 → offset ≠ 22 →
        s'.regs (gm02RecursiveControlBase q + offset) = s.regs (gm02RecursiveControlBase q + offset)) := by
  let p := gm02RecursiveParentArr q
  let b := gm02RecursiveControlBase q
  have hb := gm02RecursiveControlBase_ge q
  have hn : x.n < 2 ^ w := by omega
  have hq : 4 * q < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hg : (.op .le (.read p (.const 0)) (.const (4 * q)) : Expr).eval w s = some 1 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, hsrc, p, GM02SimpleTerminatedInput.enc,
      encGraph, checkWord_of_lt (by omega : 0 < 2 ^ w), checkWord_of_lt hn,
      checkWord_of_lt hq, hsmall, checkWord_of_lt h1]
  obtain ⟨s₁, t₁, he₁, ht₁, hout, hr₁, ha₁⟩ := gm02BaseExhaustionProg_exec p outReg (b + 22)
    x hsmall hw [] s (by simpa only [List.append_nil] using hsrc)
  let s₂ := s₁.setReg (b + 18) 3
  have he₂ : Exec w (.assign (b + 18) (.const 3)) s₁ s₂ 2 :=
    Exec.assign (checkWord_of_lt (by omega))
  have he : Exec w (gm02RecursiveEnterProg q) s s₂ (4 + (t₁ + 2)) :=
    Exec.ite_true (v := 1) hg (by decide) (Exec.seq he₁ he₂)
  refine ⟨s₂, 4 + (t₁ + 2), he, by omega, ?_, by simp [s₂, b], ha₁, ?_⟩
  · exact (State.setReg_regs_ne _ _
      (by dsimp only [b, Reg, outReg] at *; omega)).trans hout
  · intro offset h18 h22
    have hneq18 : b + offset ≠ b + 18 := by dsimp only [Reg] at *; omega
    have hneq22 : b + offset ≠ b + 22 := by dsimp only [Reg] at *; omega
    have hneqOut : b + offset ≠ outReg := by dsimp only [b, Reg, outReg] at *; omega
    exact (State.setReg_regs_ne _ _ hneq18).trans (hr₁ _ hneqOut hneq22)

end GraphMinor.Compute
