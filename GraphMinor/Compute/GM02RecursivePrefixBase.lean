module

public import GraphMinor.Compute.GM02RecursiveMachineProgram
public import GraphMinor.Compute.GM02RecursiveEnterBase
public import GraphMinor.Compute.GM02RecursiveWordSize
public import GraphMinor.Compute.GM02LoopPrefix

/-!
# The exhaustive base case inside the actual recursive loop

When the current input is bounded by four times the fixed width, the
loop dispatches its enter command to exhaustion and reaches the return
state with the exact answer. This gives a complete finite loop prefix
for either phase, retaining all arrays and saved-parent data.
-/

public section
namespace GraphMinor.Compute
open Classical

/-- The actual loop reaches its correct return state by exhaustion on every base input. -/
theorem gm02RecursivePrefix_base {w : ℕ} (q n : ℕ) (x : GM02SimpleTerminatedInput) (s : State)
    (hsrc : s.arrs (gm02RecursiveParentArr q) = x.enc)
    (hsmall : x.n ≤ 4 * q)
    (hstate : s.regs (gm02RecursiveControlBase q + 18) = 1)
    (hw : wordSize (gm02RecursiveWordConstant q) n ≤ w) :
    ∃ s' t, GM02LoopPrefix w (.reg (gm02RecursiveControlBase q + 18))
        (gm02RecursiveMachineStepProg q) s s' t ∧
      t ≤ (4 + 2 * ((4 * q) * (4 * q)) + 4 * q) *
        (4 * ((4 * q) * (4 * q) + 4 * q) + 10) + 10 ∧
      x.recursiveCorrect q s' ∧ s'.regs (gm02RecursiveControlBase q + 18) = 3 ∧
      s'.arrs = s.arrs ∧
      (∀ offset : ℕ, offset ≠ 18 → offset ≠ 22 →
        s'.regs (gm02RecursiveControlBase q + offset) = s.regs (gm02RecursiveControlBase q + offset)) := by
  obtain ⟨h4, hbase, _⟩ := gm02Recursive_fixed_wordBounds q n w hw
  obtain ⟨s₁, t₁, he₁, ht₁, hout, hstate₁, ha₁, hr₁⟩ :=
    gm02RecursiveEnterProg_base_exec q x s hsrc hsmall hbase
  have hg : (.op .eq (.reg (gm02RecursiveControlBase q + 18)) (.const 1) : Expr).eval w s = some 1 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, hstate, checkWord_of_lt (by omega : 1 < 2 ^ w)]
  have he : Exec w (gm02RecursiveMachineStepProg q) s s₁ (3 + t₁) :=
    Exec.ite_true (v := 1) hg (by decide) he₁
  have hguard : (.reg (gm02RecursiveControlBase q + 18) : Expr).eval w s = some 1 := by
    simp [Expr.eval, hstate, checkWord_of_lt (by omega : 1 < 2 ^ w)]
  refine ⟨s₁, 1 + (3 + t₁), GM02LoopPrefix.single hguard (by decide) he, by omega,
    ?_, hstate₁, ha₁, hr₁⟩
  by_cases hfeas : x.A.Feasible (Graph.ofSimpleGraph x.G)
  · exact Or.inl ⟨by simpa only [hfeas, ↓reduceIte] using hout, hfeas⟩
  · exact Or.inr (Or.inl ⟨by simpa only [hfeas, ↓reduceIte] using hout, hfeas⟩)

end GraphMinor.Compute
