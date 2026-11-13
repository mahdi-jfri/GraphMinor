module

public import GraphMinor.Compute.GM06Alg34GapRootLoop

/-!
# Starting the canonical reached-root scan

Initialize only the scan position. The proved scan needs no initial
output value because it always reaches the component's canonical root.
Thus the resulting new region label is read from finite arrays alone.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read the reached root's new label into register 6401. -/
def gm06GapRootScanProg : Cmd :=
  .seq (.assign 6400 (.const 0)) gm06GapRootLoopProg

/-- Starting from arbitrary scratch, the reached-root scan returns the
exact new region label with a linear bound and preserves every array. -/
theorem gm06GapRootScanProg_exec {w : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (r : Fin x.regions.length) (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    {s : State}
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs (x.cellNumbering (.inr (.inr r))))
    (hmask : s.arrs 36 = gm06RootMask x vs)
    (hranks : s.arrs 37 = List.ofFn (fun b : Fin x.cellCount => ((gm06RootMask x vs).take b.val).sum)) :
    ∃ s' t, Exec w gm06GapRootScanProg s s' t ∧ t ≤ 14 * x.cellCount + 5 ∧
      s'.regs 6401 = (x.regionAfterDeletion vs r).val ∧
      (∀ A : ℕ, s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 6400 → q ≠ 6401 → s'.regs q = s.regs q) := by
  let s₁ := s.setReg 6400 0
  have hinit : Exec w (.assign 6400 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  obtain ⟨s', t, hex, ht, _, hval, harr, hreg⟩ :=
    gm06GapRootLoopProg_exec x vs r hw hN (s := s₁) (by simp [s₁]) hmarks hmask hranks
  refine ⟨s', 2 + t, .seq hinit hex, by omega, hval, harr, ?_⟩
  intro q hq hq'
  exact (hreg q hq hq').trans (State.setReg_regs_ne _ _ hq)

end GraphMinor.Compute
