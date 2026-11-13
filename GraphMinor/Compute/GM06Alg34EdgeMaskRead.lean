module

public import GraphMinor.Compute.GM06Alg34EdgeMaskData

/-!
# Reading the surviving-edge flag

The edge mask has one zero-one entry per supplied edge label. Reading
it at the current old edge index gives exactly the finite survival
test used to decide whether to emit a relabelled endpoint pair.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read the surviving-edge flag at an old edge label in a register. -/
def gm06EdgeActiveExpr (r : ℕ) : Expr := .read 6 (.reg r)

/-- The edge-mask lookup returns the exact finite induced-edge bit. -/
theorem gm06EdgeActiveExpr_eval {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (e : Fin x.ends.length) (r : ℕ)
    (hw : 1 < 2 ^ w) (hm : x.ends.length < 2 ^ w) {s : State}
    (hmask : s.arrs 6 = gm06EdgeMask x vs) (hr : s.regs r = e.val) :
    (gm06EdgeActiveExpr r).eval w s =
      some (if x.activeCell vs (.inr (.inl e)) then 1 else 0) := by
  have hew := e.isLt.trans hm
  have hlen : e.val < (s.arrs 6).length := by simp [hmask, gm06EdgeMask, e.isLt]
  have hget : (s.arrs 6)[e.val]'hlen =
      if x.activeCell vs (.inr (.inl e)) then 1 else 0 := by simp [hmask, gm06EdgeMask]
  cases he : x.activeCell vs (.inr (.inl e)) <;>
    simp [gm06EdgeActiveExpr, Expr.eval, hr, checkWord, hew, hlen, hget, he,
      hw, Nat.zero_lt_of_lt hw]

end GraphMinor.Compute
