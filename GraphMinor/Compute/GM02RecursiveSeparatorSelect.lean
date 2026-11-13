module

public import GraphMinor.Compute.GM02RecursiveSeparatorFrames

/-!
# Executing the phase-selected separator command

The phase register selects all vertices for A1 and terminal support for
A2. Apply the proved separator step to that exact subset. The selected
command returns a valid width report or balanced side bits, preserves
the retained parent/stack range, and leaves the control block unchanged.
-/

public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

/-- The separator selector executes the paper's exact query for the current phase. -/
theorem gm02RecursiveSeparatorSelectProg_exec {w : ℕ} (q : ℕ) (allVertices : Bool)
    (x : GM02SimpleTerminatedInput) (s : State)
    (hsrc : s.arrs (gm02RecursiveParentArr q) = x.enc)
    (hphase : s.regs (gm02RecursiveControlBase q + 3) = if allVertices then 0 else 1)
    (hw : 4 < 2 ^ w) (hlen : x.enc.length < 2 ^ w)
    (hsep : 2 + 2 * (edgeListOf x.G).length + x.n < 2 ^ w)
    (hn : 3 * x.n < 2 ^ w) (hb : x.n + 1 < 2 ^ w) (hp : (x.n + 1) ^ q < 2 ^ w) :
    ∃ s' t, Exec w (gm02RecursiveSeparatorSelectProg q) s s' t ∧
      t ≤ (10000 * (q + 1) ^ 2 + 155) * (x.n + 1) ^ (q + 3) + 3 ∧
      ((s'.regs outReg = 2 ∧ q ≤ x.width) ∨
        (s'.regs outReg = 1 ∧ ∃ L R : Finset (Fin x.n),
          s'.arrs outArr = gm02VertexBits L ∧ s'.arrs 2 = gm02VertexBits R ∧
          (gm02RecursiveSeparatorInput allVertices x).validSides (q : ℤ)
            (s'.arrs outArr) (s'.arrs 2))) ∧
      (∀ offset : ℕ, offset ≠ 50 → offset ≠ 51 →
        s'.arrs (gm02RecursiveParentArr q + offset) = s.arrs (gm02RecursiveParentArr q + offset)) ∧
      (∀ offset : ℕ, s'.regs (gm02RecursiveControlBase q + offset) =
        s.regs (gm02RecursiveControlBase q + offset)) := by
  let p := gm02RecursiveParentArr q
  have hpg := gm02RecursiveParentArr_ge q
  obtain ⟨s', t, he, ht, hout, ha⟩ := gm02RecursiveStepOneProg_exec allVertices x p (p + 50) (p + 51)
    (by dsimp only [Arr]; omega) (by dsimp only [Arr]; omega) (by dsimp only [Arr]; omega)
    (by dsimp only [p, inArr, Arr] at *; omega) (by dsimp only [p, inArr, Arr] at *; omega)
    s hsrc hw hlen hsep hn hb hp
  have hsel : Exec w (gm02RecursiveSeparatorSelectProg q) s s' (3 + t) := by
    cases allVertices with
    | false =>
      apply Exec.ite_false (t := t) _ he
      simp [Expr.eval, BinOp.eval, BinOp.raw, hphase,
        checkWord_of_lt (by omega : 0 < 2 ^ w), checkWord_of_lt (by omega : 1 < 2 ^ w)]
    | true =>
      apply Exec.ite_true (v := 1) (t := t) _ (by decide) he
      simp [Expr.eval, BinOp.eval, BinOp.raw, hphase,
        checkWord_of_lt (by omega : 0 < 2 ^ w), checkWord_of_lt (by omega : 1 < 2 ^ w)]
  refine ⟨s', 3 + t, hsel, by omega, hout, ?_, ?_⟩
  · intro offset h50 h51
    exact ha _ (by dsimp only [Arr]; omega) (by dsimp only [Arr]; omega)
      (by dsimp only [p, inArr, Arr] at *; omega) (gm02RecursiveParentArr_not_written q offset)
  · intro offset
    exact hsel.regs_eq_of_not_mem_writtenRegs (gm02RecursiveSeparatorSelectProg_control_not_written q offset)

end GraphMinor.Compute
