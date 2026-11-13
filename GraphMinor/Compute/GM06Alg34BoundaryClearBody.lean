module

public import GraphMinor.Compute.GM06Alg34BoundaryHitPrefix

/-!
# Accumulating a new-boundary closure-hit flag

For the current supplied cell, test its BFS mark and closure incidence.
A contribution clears the accumulator in register zero. Other tests
leave the accumulator unchanged. The body preserves all arrays and
all other registers, allowing the counted clearing-scan rule to apply.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Clear accumulator 0 when cell 204 contributes to boundary label 205. -/
def gm06BoundaryClearBodyProg : Cmd :=
  .ite gm06BoundaryHitExpr (.assign 0 (.const 0)) .skip

/-- Each boundary contribution test takes at most eleven steps and
clears exactly when the finite contribution predicate succeeds. -/
theorem gm06BoundaryClearBodyProg_exec {w : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (a c b : Fin x.cellCount) (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) {s : State}
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs a)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hcell : s.regs 204 = c.val) (hboundary : s.regs 205 = b.val) :
    ∃ s' t, Exec w gm06BoundaryClearBodyProg s s' t ∧ t ≤ 11 ∧
      s'.regs 0 = (if gm06BoundaryContribution x vs a b c.val then 0 else s.regs 0) ∧
      (∀ k, s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q ≠ 0 → s'.regs q = s.regs q) := by
  have htest := gm06BoundaryHitExpr_eval x vs a c b hw hN hsquare hmarks hmat hc hcell hboundary
  have hf : gm06BoundaryContribution x vs a b c.val =
      decide ((x.complementGraph vs).Reachable a c ∧
        x.cellNumbering.symm b ∈ x.cellClosure (x.cellNumbering.symm c)) := by
    simp only [gm06BoundaryContribution, dite_eq_left c.isLt]
  by_cases h : (x.complementGraph vs).Reachable a c ∧
      x.cellNumbering.symm b ∈ x.cellClosure (x.cellNumbering.symm c)
  · have htest' : gm06BoundaryHitExpr.eval w s = some 1 := by simpa [h] using htest
    have hzero : (Expr.const 0).eval w s = some 0 := by
      simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw]
    refine ⟨s.setReg 0 0, 11, Exec.ite_true htest' (by omega) (.assign hzero), le_rfl,
      ?_, fun _ => rfl, fun q hq => ?_⟩
    · simp [hf, h]
    · simp [State.setReg, hq]
  · have htest' : gm06BoundaryHitExpr.eval w s = some 0 := by simpa [h] using htest
    refine ⟨s, 10, Exec.ite_false htest' (Exec.skip s), by omega, ?_, fun _ => rfl, fun _ _ => rfl⟩
    simp [hf, h]

end GraphMinor.Compute
