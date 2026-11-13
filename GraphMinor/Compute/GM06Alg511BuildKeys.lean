module

public import GraphMinor.Compute.GM06Alg511DartKeys
public import GraphMinor.Compute.GM06Alg511MapValues
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Computing the directed edge key array

The winding phase of VI (5.11), page 134, selects an edge for each
step of the returned vertex path. Build its search table from the
supplied consecutive endpoint positions. Swapping positions uses
parity arithmetic, so each table entry takes constant RAM time.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Arithmetic expression for the other position of a consecutive pair. -/
def gm06Alg511MateExpr : Expr :=
  .op .sub (.op .add (.reg 20) (.const 1))
    (.op .mul (.const 2) (.op .mod (.reg 20) (.const 2)))

/-- Construct endpoint-pair search keys from endpoint array 3 and
vertex count register 41, using counter 20 and destination 1100. -/
def gm06Alg511BuildKeysProg : Cmd :=
  gm06Alg511MapValuesProg 20 (.len 3) 1100
    (.op .add (.op .mul (.read 3 (.reg 20)) (.reg 41))
      (.read 3 gm06Alg511MateExpr))

/-- The parity expression computes the other endpoint position without overflow. -/
theorem gm06Alg511MateExpr_eval {w j m : ℕ} (s : State)
    (hw : 2 < 2 ^ w) (hn : 2 * m < 2 ^ w) (hj : j < 2 * m)
    (hr : s.regs 20 = j) :
    gm06Alg511MateExpr.eval w s = some (gm06DartMate j) := by
  have hjw : j < 2 ^ w := hj.trans hn
  have hmod : (Expr.op .mod (.reg 20) (.const 2)).eval w s = some (j % 2) := by
    simp [Expr.eval, hr, BinOp.eval, BinOp.raw, checkWord, hjw, hw,
      (Nat.mod_lt j (by decide : 0 < 2)).trans hw]
  have hplus : j + 1 < 2 ^ w := lt_of_le_of_lt (by omega) hn
  have htimes : 2 * (j % 2) < 2 ^ w := lt_of_le_of_lt (by omega) hw
  have he := Crossing.eval_sub
    (Crossing.eval_add (Crossing.eval_reg hr hjw) (Crossing.eval_const (by omega)) hplus)
    (Crossing.eval_mul (Crossing.eval_const hw) hmod htimes)
  have heq : j + 1 - 2 * (j % 2) = gm06DartMate j := by
    unfold gm06DartMate
    split <;> omega
  simpa only [gm06Alg511MateExpr, heq] using he

/-- The key table is computed in linear time from ordinary supplied
endpoint data. All other arrays and registers are preserved. -/
theorem gm06Alg511BuildKeysProg_exec {w : ℕ} (x : GM06Alg511Input)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G) (s : State)
    (hw : 2 < 2 ^ w) (hlen : x.endpoints.length < 2 ^ w)
    (hn : x.vertexCount < 2 ^ w) (hsquare : x.vertexCount * x.vertexCount < 2 ^ w)
    (harr : s.arrs 3 = x.endpoints) (hrn : s.regs 41 = x.vertexCount) :
    ∃ s' t, Exec w gm06Alg511BuildKeysProg s s' t ∧
      t ≤ 6 + 25 * x.endpoints.length ∧ Keeps [20] [1100] s s' ∧
      s'.arrs 1100 = gm06Alg511DartKeys x := by
  have hlen' : x.endpoints.length = 2 * rep.pairs.length := by
    have hend : x.endpoints = gm06EndpointWords
        (rep.pairs.map fun p => (p.1.val, p.2.val)) := rep.endpoints
    rw [hend, gm06EndpointWords_length, List.length_map]
  let f := fun d => x.endpoints.getD d 0 * x.vertexCount +
    x.endpoints.getD (gm06DartMate d) 0
  obtain ⟨s', t, he, ht, hk, hout⟩ := gm06Alg511MapValuesProg_exec
    20 (.len 3) 1100 _ x.endpoints.length f s (by omega) hlen
    (fun st h => Crossing.eval_len ((h.2 3 (by decide)).trans harr) hlen)
    (fun st d h hd hdlen => by
      have ha : st.arrs 3 = x.endpoints := (h.2 3 (by decide)).trans harr
      have hm : gm06DartMate d < x.endpoints.length := by
        rw [hlen'] at hdlen ⊢
        exact gm06DartMate_lt hdlen
      have hda : x.endpoints.getD d 0 < x.vertexCount :=
        rep.endpoint_lt (by
          change x.endpoints.getD d 0 ∈ x.endpoints
          simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hdlen,
            Option.getD_some] using List.getElem_mem hdlen)
      have hdb : x.endpoints.getD (gm06DartMate d) 0 < x.vertexCount :=
        rep.endpoint_lt (by
          change x.endpoints.getD (gm06DartMate d) 0 ∈ x.endpoints
          simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm,
            Option.getD_some] using List.getElem_mem hm)
      have hkey : f d < 2 ^ w := (gm06Alg511PairKey_lt hda hdb).trans hsquare
      have hread : (Expr.read 3 (.reg 20)).eval w st = some (x.endpoints.getD d 0) := by
        simpa [ha, hdlen] using Crossing.eval_read
          (a := 3) (Crossing.eval_reg hd (hdlen.trans hlen)) (ha ▸ hdlen)
          (by simpa [ha, hdlen] using hda.trans hn)
      have hreadm : (Expr.read 3 gm06Alg511MateExpr).eval w st =
          some (x.endpoints.getD (gm06DartMate d) 0) := by
        simpa [ha, hm] using Crossing.eval_read (a := 3)
          (gm06Alg511MateExpr_eval st hw (hlen' ▸ hlen) (hlen' ▸ hdlen) hd) (ha ▸ hm)
          (by simpa [ha, hm] using hdb.trans hn)
      exact Crossing.eval_add
        (Crossing.eval_mul hread
          (Crossing.eval_reg ((h.1 41 (by decide)).trans hrn) hn)
          (lt_of_le_of_lt (Nat.le_add_right _ _) hkey)) hreadm hkey)
  refine ⟨s', t, he, ?_, hk, hout⟩
  norm_num [Expr.cost, gm06Alg511MateExpr] at ht ⊢
  simpa only [Nat.mul_comm] using ht

end GraphMinor.Compute
