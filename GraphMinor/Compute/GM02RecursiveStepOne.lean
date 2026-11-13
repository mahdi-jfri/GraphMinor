module

public import GraphMinor.Compute.GM02RecursiveSeparator
public import GraphMinor.Compute.GM02SeparatorWidthReport
import Mathlib.Tactic.Ring

/-!
# Step 1 of the alternating recursion, including width reports

Run the phase's actual separator program. A successful call leaves both
membership arrays available for crossing-scheme generation. A rejected
call is justified by (2.6), and its output flag is changed to the recursive
width-report flag. The extra control costs at most five instructions.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Convert a separator rejection into the internal width-report flag. -/
def gm02SeparatorReportProg : Cmd :=
  .ite (.op .eq (.reg outReg) (.const 0)) (.assign outReg (.const 2)) .skip

/-- The complete Step 1 of A1 or A2, II pages 316–317. -/
def gm02RecursiveStepOneProg (allVertices : Bool) (k : ℕ) (src graph bits : Arr) : Cmd :=
  .seq (gm02RecursiveSeparatorProg allVertices k src graph bits) gm02SeparatorReportProg

private theorem time_add_five {n k t : ℕ}
    (ht : t ≤ (10000 * (k + 1) ^ 2 + 150) * (n + 1) ^ (k + 3)) :
    t + 5 ≤ (10000 * (k + 1) ^ 2 + 155) * (n + 1) ^ (k + 3) := by
  have hp : 1 ≤ (n + 1) ^ (k + 3) := Nat.one_le_pow _ _ (by omega)
  have h5 : 5 ≤ 5 * (n + 1) ^ (k + 3) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 5 hp
  calc
    t + 5 ≤ (10000 * (k + 1) ^ 2 + 150) * (n + 1) ^ (k + 3) +
        5 * (n + 1) ^ (k + 3) := Nat.add_le_add ht h5
    _ = _ := by ring

/-- The executable first step returns either a valid width report or an
actual balanced separation with usable membership arrays. -/
theorem gm02RecursiveStepOneProg_exec {w k : ℕ} (allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (src graph bits : Arr) (hsg : src ≠ graph) (hsb : src ≠ bits)
    (hgb : graph ≠ bits) (hg0 : graph ≠ inArr) (hb0 : bits ≠ inArr)
    (s : State) (hsrc : s.arrs src = x.enc) (hw : 4 < 2 ^ w) (hlen : x.enc.length < 2 ^ w)
    (hsep : 2 + 2 * (edgeListOf x.G).length + x.n < 2 ^ w)
    (hn : 3 * x.n < 2 ^ w) (hb : x.n + 1 < 2 ^ w) (hp : (x.n + 1) ^ k < 2 ^ w) :
    ∃ s' t, Exec w (gm02RecursiveStepOneProg allVertices k src graph bits) s s' t ∧
      t ≤ (10000 * (k + 1) ^ 2 + 155) * (x.n + 1) ^ (k + 3) ∧
      ((s'.regs outReg = 2 ∧ k ≤ x.width) ∨
        (s'.regs outReg = 1 ∧ ∃ L R : Finset (Fin x.n),
          s'.arrs outArr = gm02VertexBits L ∧ s'.arrs 2 = gm02VertexBits R ∧
          (gm02RecursiveSeparatorInput allVertices x).validSides (k : ℤ) (s'.arrs outArr) (s'.arrs 2))) ∧
      (∀ a, a ≠ graph → a ≠ bits → a ≠ inArr →
        a ∉ (gm02BalancedSeparationProg k).writtenArrs → s'.arrs a = s.arrs a) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hout, hbits, ha⟩ := gm02RecursiveSeparatorProg_exec_bits
    allVertices x src graph bits hsg hsb hgb hg0 hb0 s hsrc hw hlen hsep hn hb hp
  have ht := time_add_five ht₁
  have hzero : 0 < 2 ^ w := Nat.two_pow_pos _
  have hone : 1 < 2 ^ w := by omega
  rcases hout with ⟨hflag, hvalid⟩ | ⟨hflag, hno⟩
  · obtain ⟨L, R, hL, hR⟩ := hbits hflag
    have he₂ : Exec w gm02SeparatorReportProg s₁ s₁ 4 := by
      unfold gm02SeparatorReportProg
      apply Exec.ite_false (t := 1)
      · simp [Expr.eval, BinOp.eval, BinOp.raw, hflag, checkWord_of_lt hzero, checkWord_of_lt hone]
      · exact Exec.skip s₁
    exact ⟨s₁, t₁ + 4, Exec.seq he₁ he₂, by omega, Or.inr ⟨hflag, L, R, hL, hR, hvalid⟩, ha⟩
  · have hwidth := gm02RecursiveSeparator_reject_width allVertices x k s₁ (Or.inr ⟨hflag, hno⟩) hflag
    let s₂ := s₁.setReg outReg 2
    have he₂ : Exec w gm02SeparatorReportProg s₁ s₂ 5 := by
      unfold gm02SeparatorReportProg
      apply Exec.ite_true (v := 1) (t := 2)
      · simp [Expr.eval, BinOp.eval, BinOp.raw, hflag, checkWord_of_lt hzero, checkWord_of_lt hone]
      · decide
      · exact Exec.assign (by simp [Expr.eval, checkWord_of_lt (by omega : 2 < 2 ^ w)])
    refine ⟨s₂, t₁ + 5, Exec.seq he₁ he₂, ht, Or.inl ⟨by simp [s₂], hwidth⟩, ?_⟩
    intro a hag hab ha0 haw
    exact ha a hag hab ha0 haw

end GraphMinor.Compute
