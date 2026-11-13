module

public import GraphMinor.Compute.GM06Alg511StoredWinding
import GraphMinor.Compute.GM06Alg511WindingWordBounds

/-!
# Output word bounds for the stored-linkage winding phase

The VI (5.11) winding phase clears its two accumulators before the
sum loop. Successful RAM assignments check their word bounds, and
the endpoint scan preserves those registers. Thus the final bounds
follow from actual execution even with arbitrary initial scratch.
-/

public section
namespace GraphMinor.Compute

private theorem sum_bounds {w : ℕ} {s s' : State} {t : ℕ}
    (he : Exec w gm06Alg511TurnSumProg s s' t) :
    s'.regs 21 < 2 ^ w ∧ s'.regs 22 < 2 ^ w := by
  cases he with
  | seq hp hrest =>
    have hpos := gm06Alg511Exec_reg_lt hrest (gm06Alg511Assigned_reg_lt hp)
    refine ⟨hpos, ?_⟩
    cases hrest with
    | seq hq hloop => exact gm06Alg511Exec_reg_lt hloop (gm06Alg511Assigned_reg_lt hq)

private theorem trace_bounds {w : ℕ} {s s' : State} {t : ℕ}
    (he : Exec w gm06Alg511TraceChosenTurnProg s s' t) :
    s'.regs 21 < 2 ^ w ∧ s'.regs 22 < 2 ^ w := by
  cases he with
  | seq _ hrest =>
    cases hrest with
    | seq _ hchosen =>
      cases hchosen with
      | seq _ hcopy =>
        cases hcopy with
        | seq _ hsum => exact sum_bounds hsum

/-- Both computed accumulators of the full stored initial linkage
fit the execution word, with no bound on initial scratch registers. -/
theorem gm06Alg511StoredInitialWindingProg_regs_lt {w : ℕ} {s s' : State} {t : ℕ}
    (he : Exec w gm06Alg511StoredInitialWindingProg s s' t) :
    s'.regs 21 < 2 ^ w ∧ s'.regs 22 < 2 ^ w := by
  cases he with
  | seq _ hstored =>
    cases hstored with
    | seq _ hrest =>
      cases hrest with
      | seq htrace hscan =>
        obtain ⟨hp, hq⟩ := trace_bounds htrace
        exact ⟨gm06Alg511Exec_reg_lt hscan hp, gm06Alg511Exec_reg_lt hscan hq⟩

end GraphMinor.Compute
