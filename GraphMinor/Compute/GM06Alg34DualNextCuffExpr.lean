module

public import GraphMinor.Compute.GM06Alg34CyclicShift
public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Reading the next primal cuff label on the RAM

The following dual gap uses the next old primal vertex. Add one to the
current cuff index and reduce modulo the supplied cuff length. A read
at that position returns precisely the cyclic-successor label of the
finite augmented dual construction.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Cyclic successor agrees with one addition followed by remainder. -/
theorem gm06CycleSucc_val_mod {n : ℕ} (i : Fin n) :
    (gm06CycleSucc i).val = (i.val + 1) % n := by
  change (if i.val + 1 < n then i.val + 1 else 0) = _
  by_cases hi : i.val + 1 < n
  · rw [ite_eq_left hi, Nat.mod_eq_of_lt hi]
  · have he : i.val + 1 = n := by omega
    rw [ite_eq_right hi, he, Nat.mod_self]

/-- Read the next old cuff label after the index in register 8000. -/
def gm06DualNextCuffExpr : Expr :=
  .read 2 (.op .mod (.op .add (.reg 8000) (.const 1)) (.len 2))

/-- The RAM remainder read is exactly the next supplied primal cuff label. -/
theorem gm06DualNextCuffExpr_eval {w n : ℕ} (L : List (Fin n)) (i : Fin L.length)
    {s : State} (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hk : L.length < 2 ^ w)
    (hsource : s.arrs 2 = L.map Fin.val) (hindex : s.regs 8000 = i.val) :
    gm06DualNextCuffExpr.eval w s = some (L.get (gm06CycleSucc i)).val := by
  have hsum : i.val + 1 < 2 ^ w := (by omega : i.val + 1 ≤ L.length).trans_lt hk
  have hmod : (i.val + 1) % L.length < L.length :=
    Nat.mod_lt _ (by omega : 0 < L.length)
  have hmodw := hmod.trans hk
  have hne : L.length ≠ 0 := by omega
  have hidxw := i.isLt.trans hk
  have hlen : (s.arrs 2).length = L.length := by simp only [hsource, List.length_map]
  have hget : (s.arrs 2)[(i.val + 1) % L.length]'(by rw [hlen]; exact hmod) =
      (L.get (gm06CycleSucc i)).val := by
    simp only [hsource, List.getElem_map, List.get_eq_getElem]
    congr 2
    exact (gm06CycleSucc_val_mod i).symm
  have hword := (L.get (gm06CycleSucc i)).isLt.trans hn
  simp only [gm06DualNextCuffExpr, Expr.eval, hindex,
    checkWord_of_lt hidxw, checkWord_of_lt hw, BinOp.eval, BinOp.raw,
    checkWord_of_lt hsum, hlen, hne, ↓reduceIte, checkWord_of_lt hk, checkWord_of_lt hmodw]
  simp only [show (i.val + 1) % L.length < (s.arrs 2).length from hlen.symm ▸ hmod,
    hmod, ↓reduceDIte, hget, checkWord_of_lt hword]

end GraphMinor.Compute
