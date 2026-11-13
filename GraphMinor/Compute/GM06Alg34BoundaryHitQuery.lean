module

public import GraphMinor.Compute.GM06Alg34BoundaryHitLoop

/-!
# A complete RAM query for new region closure hits

Set the scan bound from the supplied cell count, initialize the
no-contribution accumulator to one, and scan the reached closures.
Complement the accumulator to return the exact closure-hit bit in a
scratch register. The supplied arrays remain unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Query whether label 205 lies in the closure of the source component,
returning its bit in register 206. -/
def gm06BoundaryHitQueryProg : Cmd :=
  .seq (.assign 105 (.reg 170))
    (.seq (.assign 0 (.const 1))
      (.seq gm06BoundaryHitLoopProg (.assign 206 (.op .sub (.const 1) (.reg 0)))))

/-- A full closure-hit query takes at most `18 * N + 13` steps and
preserves every supplied or computed array. -/
theorem gm06BoundaryHitQueryProg_exec {w : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (a b : Fin x.cellCount) (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (ha : x.activeCell vs (x.cellNumbering.symm a) = false) {s : State}
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs a)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hboundary : s.regs 205 = b.val) :
    ∃ s' t, Exec w gm06BoundaryHitQueryProg s s' t ∧ t ≤ 18 * x.cellCount + 13 ∧
      s'.regs 206 = (if x.regionClosureHit vs a (x.cellNumbering.symm b) then 1 else 0) ∧
      (∀ k, s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 105 → q ≠ 204 → q ≠ 206 → s'.regs q = s.regs q) := by
  let s₁ := s.setReg 105 x.cellCount
  let s₂ := s₁.setReg 0 1
  have hex₁ : Exec w (.assign 105 (.reg 170)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hc, hN])
  have hex₂ : Exec w (.assign 0 (.const 1)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  obtain ⟨s₃, t, hex₃, ht, hacc, harr, hreg⟩ :=
    gm06BoundaryHitLoopProg_exec x vs a b hw hN hsquare ha (s := s₂) hmarks hmat
      (by simpa [s₂, s₁] using hc) (by simp [s₂, s₁]) (by simpa [s₂, s₁] using hboundary)
  have hacc' : s₃.regs 0 = if x.regionClosureHit vs a (x.cellNumbering.symm b) then 0 else 1 := by
    simpa only [s₂, State.setReg_regs_self] using hacc
  have hval : (Expr.op .sub (.const 1) (.reg 0)).eval w s₃ =
      some (if x.regionClosureHit vs a (x.cellNumbering.symm b) then 1 else 0) := by
    cases hh : x.regionClosureHit vs a (x.cellNumbering.symm b) <;>
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hacc', hh, hw, Nat.zero_lt_of_lt hw]
  let s₄ := s₃.setReg 206 (if x.regionClosureHit vs a (x.cellNumbering.symm b) then 1 else 0)
  have hex₄ : Exec w (.assign 206 (.op .sub (.const 1) (.reg 0))) s₃ s₄ 4 := .assign hval
  refine ⟨s₄, 2 + (2 + (t + 4)), Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ hex₄)),
    by omega, by simp [s₄], harr, ?_⟩
  intro q hq₁ hq₂ hq₃ hq₄
  have hq : s₄.regs q = s₃.regs q := by simp [s₄, hq₄]
  exact hq.trans ((hreg q hq₁ hq₃).trans (by simp [s₂, s₁, hq₁, hq₂]))

end GraphMinor.Compute
