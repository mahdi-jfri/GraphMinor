module

public import GraphMinor.Compute.GM06Alg34CrossExpr

/-!
# Reading a cuff vertex's block tag

A cuff position first indexes array 2, which holds the supplied cyclic
vertex list. The resulting vertex label indexes array 3, the computed
block table. The two reads give exactly the tag used by the finite
crossing test. All bounds follow from the two supplied lists.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read the division tag at a cuff position held in a register. -/
def gm06ColourRead (r : ℕ) : Expr := .read 3 (.read 2 (.reg r))

private theorem gm06_read_eval {w a i v : ℕ} {e : Expr} {s : State}
    (he : e.eval w s = some i) (hi : i < (s.arrs a).length)
    (hv : (s.arrs a).getD i 0 = v) (hw : v < 2 ^ w) :
    (Expr.read a e).eval w s = some v := by
  have hget : (s.arrs a)[i] = v := by simpa only [List.getD_eq_getElem _ _ hi] using hv
  simp [Expr.eval, he, hi, hget, checkWord, hw]

/-- The two array reads compute the exact finite block tag at a valid
cuff position, without any disjointness assumption on the division. -/
theorem gm06ColourRead_eval {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (i : Fin L.length) (r : ℕ) {s : State}
    (hr : s.regs r = i.val) (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hk : L.length < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w) :
    (gm06ColourRead r).eval w s = some (gm06BlockTag x.division (L.get i)) := by
  have hiw : i.val < 2 ^ w := lt_trans i.isLt hk
  have he : (Expr.reg r).eval w s = some i.val := by
    simp [Expr.eval, checkWord, hr, hiw]
  have hget : (s.arrs 2).getD i.val 0 = (L.get i).val := by
    rw [hL, List.getD_eq_getElem _ _ (by simpa using i.isLt)]
    simp
  have he2 := gm06_read_eval he (by simpa [hL] using i.isLt) hget
    (lt_trans (L.get i).isLt hn)
  have hlen : (s.arrs 3).length = x.n := by
    rw [hD, gm06DivisionIds_length, List.length_replicate]
  have htag : (s.arrs 3).getD (L.get i).val 0 = gm06BlockTag x.division (L.get i) := by
    rw [hD, gm06DivisionIds_fin_getD]
  exact gm06_read_eval he2 (by rw [hlen]; exact (L.get i).isLt) htag
    (lt_of_le_of_lt (gm06BlockTag_le_length _ _) hd)

end GraphMinor.Compute
