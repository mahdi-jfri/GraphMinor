module

public import GraphMinor.Compute.GM06Alg34VertexMask

/-!
# Reading supplied gap incidence during deletion

A cuff slot reads its vertex from array 2 and its incident old region
from array 47. The vertex indexes the computed survival mask in array
4. These reads return exactly the supplied finite values and the
survival bit used by the retained-gap update.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read the supplied cuff vertex at scan position 6403. -/
def gm06GapUpdateVertexExpr : Expr := .read 2 (.reg 6403)

/-- Test whether that supplied cuff vertex survives deletion. -/
def gm06GapUpdateActiveExpr : Expr := .read 4 gm06GapUpdateVertexExpr

/-- Read the supplied old region at the same cuff gap position. -/
def gm06GapUpdateRegionExpr : Expr := .read 47 (.reg 6403)

private theorem read_ofFn {w n A : ℕ} {e : Expr} (f : Fin n → ℕ) (a : Fin n)
    (hf : f a < 2 ^ w) {s : State} (hA : s.arrs A = List.ofFn f)
    (he : e.eval w s = some a.val) :
    (Expr.read A e).eval w s = some (f a) := by
  have hlen : a.val < (s.arrs A).length := by simp [hA, a.isLt]
  have hget : (s.arrs A)[a.val]'hlen = f a := by simp [hA]
  simp [Expr.eval, checkWord, he, hlen, hget, hf]

/-- The nested mask read tests exactly the supplied cuff vertex's survival. -/
theorem gm06GapUpdateActiveExpr_eval {w n : ℕ} (vs L : List (Fin n))
    (i : Fin L.length) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w)
    (hk : L.length < 2 ^ w) {s : State}
    (hi : s.regs 6403 = i.val) (hL : s.arrs 2 = L.map Fin.val)
    (hmask : s.arrs 4 = gm06VertexMask vs) :
    gm06GapUpdateActiveExpr.eval w s = some (if L.get i ∈ vs then 1 else 0) := by
  have hreg : (Expr.reg 6403).eval w s = some i.val := by
    simp [Expr.eval, checkWord, hi, i.isLt.trans hk]
  have hread : gm06GapUpdateVertexExpr.eval w s = some (L.get i).val := by
    have hlist : s.arrs 2 = List.ofFn (fun j : Fin L.length => (L.get j).val) := by
      exact hL.trans ((congrArg (List.map Fin.val) (List.ofFn_get L).symm).trans
        (List.map_ofFn (f := L.get) (g := Fin.val)))
    exact read_ofFn (fun j : Fin L.length => (L.get j).val) i
      ((L.get i).isLt.trans hn) hlist hreg
  exact read_ofFn (fun v : Fin n => if v ∈ vs then 1 else 0) (L.get i)
    (by split <;> omega) hmask hread

/-- The gap region read returns exactly the supplied region number at that slot. -/
theorem gm06GapUpdateRegionExpr_eval {w k m : ℕ} (g : Fin k → Fin m)
    (i : Fin k) (hk : k < 2 ^ w) (hm : m < 2 ^ w) {s : State}
    (hi : s.regs 6403 = i.val) (hR : s.arrs 47 = List.ofFn (fun j => (g j).val)) :
    gm06GapUpdateRegionExpr.eval w s = some (g i).val :=
  read_ofFn (fun j => (g j).val) i ((g i).isLt.trans hm) hR
    (by simp [Expr.eval, checkWord, hi, i.isLt.trans hk])

end GraphMinor.Compute
