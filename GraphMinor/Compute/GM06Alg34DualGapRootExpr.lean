module

public import GraphMinor.Compute.GM06Alg34DualGapRanks

/-!
# Reading the least dual gap representative

The source's exclusive prefix count vanishes exactly when it is the
least label of its class. A single array read and comparison compute
this canonical root bit.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test the exclusive count at source gap 120 for zero. -/
def gm06GapRootExpr : Expr := .op .eq (.read 44 (.reg 120)) (.const 0)

/-- The zero-prefix expression computes the exact canonical gap root bit. -/
theorem gm06GapRootExpr_eval {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (a : Fin L.length) (hw : 1 < 2 ^ w)
    (hk : L.length < 2 ^ w) {s : State} (ha : s.regs 120 = a.val)
    (hranks : s.arrs 44 = List.ofFn (fun b : Fin L.length =>
      ((gm06GapRow x L a).take b.val).sum)) :
    gm06GapRootExpr.eval w s = some (if gm06GapIsRoot x L a then 1 else 0) := by
  let p := ((gm06GapRow x L a).take a.val).sum
  have hsum : p ≤ L.length :=
    ((List.take_sublist a.val (gm06GapRow x L a)).sum_le_sum
      (fun _ _ => Nat.zero_le _)).trans (gm06GapRow_sum_le x L a)
  have hpw := hsum.trans_lt hk
  have haw := a.isLt.trans hk
  have hlen : a.val < (s.arrs 44).length := by rw [hranks, List.length_ofFn]; exact a.isLt
  have hget : (s.arrs 44)[a.val]'hlen = p := by simp only [hranks, List.getElem_ofFn]; rfl
  have hroot : gm06GapIsRoot x L a = true ↔ p = 0 :=
    (gm06GapRow_prefix_zero_iff x L a).symm
  have hbit : (if gm06GapIsRoot x L a then (1 : ℕ) else 0) = if p = 0 then 1 else 0 := by
    simp only [hroot]
  rw [hbit]
  by_cases hp : p = 0 <;>
    simp [gm06GapRootExpr, Expr.eval, BinOp.eval, BinOp.raw, checkWord, ha,
      hlen, hget, haw, hpw, hp, hw, Nat.zero_lt_of_lt hw]

end GraphMinor.Compute
