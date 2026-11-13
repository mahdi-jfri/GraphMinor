module

public import GraphMinor.Compute.GM06Alg34ReachRanks

/-!
# Computing the canonical region-root bit

Read the source's exclusive component prefix count. It is zero exactly
when the source reaches no smaller label. Multiply that test by the
inactive flag to obtain the canonical region-root bit. All counts are
bounded by the supplied cell count.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test source label 187 for being a canonical region root, using its
active bit in register 199 and component prefix counts in array 35. -/
def gm06RootTestExpr : Expr :=
  .op .mul (.op .sub (.const 1) (.reg 199))
    (.op .eq (.read 35 (.reg 187)) (.const 0))

/-- The prefix-count zero test and inactive flag compute the exact
canonical region-root bit of the finite input. -/
theorem gm06RootTestExpr_eval {w : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    {s : State} (ha : s.regs 187 = a.val)
    (hactive : s.regs 199 = if x.activeCell vs (x.cellNumbering.symm a) then 1 else 0)
    (hranks : s.arrs 35 = List.ofFn (fun b : Fin x.cellCount =>
      ((gm06ComplementReachData x vs a).take b.val).sum)) :
    gm06RootTestExpr.eval w s = some (if x.isRegionRoot vs a then 1 else 0) := by
  let p := ((gm06ComplementReachData x vs a).take a.val).sum
  have hsum : p ≤ x.cellCount :=
    ((List.take_sublist a.val (gm06ComplementReachData x vs a)).sum_le_sum
      (fun _ _ => Nat.zero_le _)).trans (gm06ComplementReachData_sum_le x vs a)
  have hpw := hsum.trans_lt hN
  have haw := a.isLt.trans hN
  have hlen : a.val < (s.arrs 35).length := by rw [hranks, List.length_ofFn]; exact a.isLt
  have hget : (s.arrs 35)[a.val]'hlen = p := by simp only [hranks, List.getElem_ofFn]; rfl
  have hroot : x.isRegionRoot vs a = true ↔
      x.activeCell vs (x.cellNumbering.symm a) = false ∧ p = 0 := by
    rw [x.isRegionRoot_iff_no_smaller_reachable]
    exact and_congr_right (fun _ => (gm06ComplementReachData_prefix_zero_iff x vs a).symm)
  have hbit : (if x.isRegionRoot vs a then (1 : ℕ) else 0) =
      if x.activeCell vs (x.cellNumbering.symm a) = false ∧ p = 0 then 1 else 0 := by
    simp only [hroot]
  rw [hbit]
  cases hact : x.activeCell vs (x.cellNumbering.symm a) <;> by_cases hp : p = 0 <;>
    simp [gm06RootTestExpr, Expr.eval, BinOp.eval, BinOp.raw, checkWord, ha, hactive,
      hlen, hget, haw, hpw, hact, hp, hw, Nat.zero_lt_of_lt hw]

end GraphMinor.Compute
