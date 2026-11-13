module

public import GraphMinor.Compute.GM02RecursiveCapacityExpression
public import GraphMinor.Compute.GM02TerminatedWords

/-!
# Executing the root initialization

Copy the plain terminated input, read its vertex count, evaluate the
proved stack-capacity formula, and allocate the empty saved stack. The
result is the initial A2 enter state with exact root-size metadata.
Initialization has polynomial cost and uses no supplied auxiliary data.
-/

public section
namespace GraphMinor.Compute

/-- Initialization produces the exact root A2 state from the plain input array. -/
theorem gm02RecursiveMachineInitProg_exec {w : ℕ} (q : ℕ) (x : GM02SimpleTerminatedInput)
    (s : State) (hsrc : s.arrs inArr = x.enc) (hlen : x.enc.length < 2 ^ w)
    (hcap : gm02SavedFrameCapacity x.n < 2 ^ w) :
    ∃ s' t, Exec w (gm02RecursiveMachineInitProg q) s s' t ∧
      t ≤ 16 * x.enc.length + gm02SavedFrameCapacity x.n + 39 ∧
      s'.arrs (gm02RecursiveParentArr q) = x.enc ∧
      s'.arrs (gm02RecursiveStackArr q) = List.replicate (gm02SavedFrameCapacity x.n) 0 ∧
      s'.regs (gm02RecursiveControlBase q + 20) = x.n ∧
      s'.regs (gm02RecursiveControlBase q + 21) = gm02SavedFrameCapacity x.n ∧
      s'.regs (gm02RecursiveControlBase q + 10) = 0 ∧
      s'.regs (gm02RecursiveControlBase q + 3) = 1 ∧
      s'.regs (gm02RecursiveControlBase q + 18) = 1 ∧
      (∀ a, a ≠ gm02RecursiveParentArr q → a ≠ gm02RecursiveStackArr q →
        s'.arrs a = s.arrs a) := by
  let p := gm02RecursiveParentArr q
  let b := gm02RecursiveControlBase q
  let stack := gm02RecursiveStackArr q
  have hpge := gm02RecursiveParentArr_ge q
  have hf : 2 * x.n + 2 ≤ gm02SavedFrameCapacity x.n := by
    unfold gm02SavedFrameCapacity
    apply Nat.le_mul_of_pos_right
    unfold gm02SavedFrameSizeBound
    omega
  have hn : x.n < 2 ^ w := (show x.n ≤ gm02SavedFrameCapacity x.n by omega).trans_lt hcap
  have hw : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hp₁, ha₁, _⟩ := copyArray72Prog_exec inArr p 350 351
    (by dsimp only [p, inArr, Arr] at *; omega) (by decide) x.enc s hw hlen (x.enc_all_lt hn hlen) hsrc
  let s₂ := s₁.setReg (b + 20) x.n
  have he₂ : Exec w (.assign (b + 20) (.read p (.const 0))) s₁ s₂ 3 := by
    apply Exec.assign
    simp [Expr.eval, hp₁, GM02SimpleTerminatedInput.enc, encGraph,
      checkWord_of_lt (by omega : 0 < 2 ^ w), checkWord_of_lt hn]
  let s₃ := s₂.setReg (b + 21) (gm02SavedFrameCapacity x.n)
  have he₃ : Exec w (.assign (b + 21) (gm02RecursiveCapacityExpr q)) s₂ s₃ 18 :=
    Exec.assign (gm02RecursiveCapacityExpr_eval q s₂ (by simp [s₂, b]) hcap)
  let s₄ := s₃.setArr stack (List.replicate (gm02SavedFrameCapacity x.n) 0)
  have he₄ : Exec w (.alloc stack (.reg (b + 21))) s₃ s₄ (1 + gm02SavedFrameCapacity x.n) :=
    Exec.alloc (by simp [Expr.eval, s₃, checkWord_of_lt hcap])
  let s₅ := s₄.setReg (b + 10) 0
  have he₅ : Exec w (.assign (b + 10) (.const 0)) s₄ s₅ 2 :=
    Exec.assign (checkWord_of_lt (by omega))
  let s₆ := s₅.setReg (b + 3) 1
  have he₆ : Exec w (.assign (b + 3) (.const 1)) s₅ s₆ 2 := Exec.assign (checkWord_of_lt hw)
  let s₇ := s₆.setReg (b + 18) 1
  have he₇ : Exec w (.assign (b + 18) (.const 1)) s₆ s₇ 2 := Exec.assign (checkWord_of_lt hw)
  refine ⟨s₇, t₁ + (3 + (18 + ((1 + gm02SavedFrameCapacity x.n) + (2 + (2 + 2))))),
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ (Exec.seq he₆ he₇))))),
    by omega, ?_, ?_, ?_, ?_, ?_, ?_, by simp [s₇, b], ?_⟩
  · exact (State.setArr_arrs_ne (a := stack) (a' := p) s₃ _
      (by dsimp only [p, stack, gm02RecursiveStackArr, Arr]; omega)).trans hp₁
  · simp [s₇, s₆, s₅, s₄, stack]
  · simp [s₇, s₆, s₅, s₄, s₃, s₂, b]
  · simp [s₇, s₆, s₅, s₄, s₃, b]
  · simp [s₇, s₆, s₅, b]
  · simp [s₇, s₆, b]
  · intro a hap has
    exact (State.setArr_arrs_ne (a := stack) (a' := a) s₃ _ has).trans (ha₁ a hap)

end GraphMinor.Compute
