module

public import GraphMinor.Compute.GM02RecursivePrefix
import GraphMinor.Compute.GM02RecursiveMachineInit
import GraphMinor.Compute.GM02RecursiveRootReturn
import GraphMinor.Compute.GM02RecursiveLoopRules
import GraphMinor.Compute.GM02RecursiveInstanceWords

/-!
# Complete execution of the alternating A2 machine

Initialize the plain input and polynomial saved-stack buffer. Apply the
proved alternating loop prefix at the root A2 bound, then execute the
empty-stack return and stop the loop. This closes the actual machine
execution with its correct three-way answer and explicit numerical time
bound, without supplying any separator, linkage, or recursive answer.
-/

public section
namespace GraphMinor.Compute

/-- The complete plain-input A2 program executes correctly with its explicit alternating budget. -/
theorem gm02RecursiveMachineProg_exec {w : ℕ} (q : ℕ) (x : GM02SimpleTerminatedInput)
    (s : State) (hsrc : s.arrs inArr = x.enc) (hindex : x.A.index ≤ 3 * q)
    (hw : wordSize (gm02RecursiveWordConstant q) x.n ≤ w) :
    ∃ s' t, Exec w (gm02RecursiveMachineProg q) s s' t ∧
      t ≤ 16 * x.enc.length + gm02SavedFrameCapacity x.n +
        gm02RecursiveTime q (2 * gm02RecursiveTimeCoefficient q) (q + 3) (2 * x.n + 1) + 52 ∧
      x.recursiveCorrect q s' := by
  let b := gm02RecursiveControlBase q
  have hbg := gm02RecursiveControlBase_ge q
  obtain ⟨h4, _, _, _, _, _, _, hcapW⟩ := gm02Recursive_fixed_wordBounds q x.n w hw
  obtain ⟨_, hlenW, _⟩ := gm02Recursive_instance_wordBounds q x.n w x le_rfl hw
  obtain ⟨s₁, t₁, he₁, ht₁, hP₁, hStack₁, _, _, hPos₁, hPhase₁, hRun₁, _⟩ :=
    gm02RecursiveMachineInitProg_exec q x s hsrc hlenW hcapW
  have hbudget : (2 * x.n + 1 + 1) * gm02SavedFrameSizeBound x.n ≤ gm02SavedFrameCapacity x.n := by
    change (2 * x.n + 1 + 1) * gm02SavedFrameSizeBound x.n ≤ (2 * x.n + 2) * gm02SavedFrameSizeBound x.n
    exact Nat.mul_le_mul_right _ (by omega)
  have hstack : IsPrefixBuffer (gm02RecursiveStackArr q) [] (gm02SavedFrameCapacity x.n) s₁ := by
    simpa only [IsPrefixBuffer, List.nil_append] using hStack₁
  obtain ⟨s₂, t₂, he₂, ht₂, hRun₂, hCorrect₂, _, _, hPos₂⟩ :=
    gm02RecursivePrefix_exec q x.n w hw (2 * x.n + 1) x.n true rfl le_rfl x le_rfl
      [] (gm02SavedFrameCapacity x.n) hbudget (by simp) s₁ hP₁ hPhase₁ hindex hRun₁ hstack hPos₁
  let s₃ := s₂.setReg (b + 18) 0
  have he₃ : Exec w (gm02RecursiveReturnProg q) s₂ s₃ 5 :=
    gm02RecursiveReturnProg_root_exec q s₂ hPos₂ (by omega)
  have hp₃ := gm02RecursiveLoop_return q hRun₂ (by omega : 3 < 2 ^ w) he₃
  have hstop : (.reg (b + 18) : Expr).eval w s₃ = some 0 := by
    simp [Expr.eval, s₃, checkWord_of_lt (by omega : 0 < 2 ^ w)]
  have heLoop := (he₂.trans hp₃).finish hstop
  have he : Exec w (gm02RecursiveMachineProg q) s s₃ (t₁ + ((t₂ + (7 + 5)) + 1)) :=
    Exec.seq he₁ heLoop
  refine ⟨s₃, _, he, by omega, ?_⟩
  have hout : s₃.regs outReg = s₂.regs outReg :=
    State.setReg_regs_ne _ _ (by dsimp only [b, outReg, Reg] at *; omega)
  simpa only [GM02SimpleTerminatedInput.recursiveCorrect, hout] using hCorrect₂

end GraphMinor.Compute
