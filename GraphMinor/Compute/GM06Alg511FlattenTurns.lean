module

public import GraphMinor.Compute.GM06Alg511TurnLayout
public import GraphMinor.Compute.GM06Alg511MapValues
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Reading the supplied integer edge turns

For VI (5.11), page 134, the turn accumulator reads two magnitude
words per edge. Build this array from the supplied turn-row code,
skipping its count and length words. The loop uses no path choices
or geometric witnesses and preserves the supplied code.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Index of a magnitude word in the supplied two-word integer rows. -/
def gm06Alg511TurnIndexExpr : Expr :=
  .op .add (.op .add (.const 2)
    (.op .mul (.const 3) (.op .div (.reg 20) (.const 2))))
    (.op .mod (.reg 20) (.const 2))

/-- Copy the integer magnitude words from turn-row array 1005 into
array 11, the signed accumulator's input. -/
def gm06Alg511FlattenTurnsProg : Cmd :=
  gm06Alg511MapValuesProg 20
    (.op .mul (.const 2) (.read 1005 (.const 0))) 11
    (.read 1005 gm06Alg511TurnIndexExpr)

/-- Flattening the supplied signed rows takes linear time and
produces exactly the turn accumulator's paired-word layout. -/
theorem gm06Alg511FlattenTurnsProg_exec {w : ℕ} (turns : List ℤ) (s : State)
    (hw : 3 < 2 ^ w)
    (hlen : (gm06EncodeRows (turns.map gm06Alg511IntegerWords)).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06EncodeRows (turns.map gm06Alg511IntegerWords), v < 2 ^ w)
    (harr : s.arrs 1005 = gm06EncodeRows (turns.map gm06Alg511IntegerWords)) :
    ∃ s' t, Exec w gm06Alg511FlattenTurnsProg s s' t ∧
      t ≤ 12 + 50 * turns.length ∧ Keeps [20] [11] s s' ∧
      s'.arrs 11 = gm06Alg511TurnWords turns := by
  let code := gm06EncodeRows (turns.map gm06Alg511IntegerWords)
  have hlen' : code.length = 1 + 3 * turns.length := gm06Alg511TurnCode_length turns
  change code.length < 2 ^ w at hlen
  have hk : 2 * turns.length < 2 ^ w := lt_of_le_of_lt (by omega) hlen
  have hm : turns.length < 2 ^ w := lt_of_le_of_lt (by omega) hlen
  obtain ⟨s', t, he, ht, hkeep, hout⟩ := gm06Alg511MapValuesProg_exec
    20 (.op .mul (.const 2) (.read 1005 (.const 0))) 11
    (.read 1005 gm06Alg511TurnIndexExpr) (2 * turns.length)
    (fun d => (gm06Alg511TurnWords turns).getD d 0) s (by omega) hk
    (fun st h => by
      have ha : st.arrs 1005 = code := (h.2 1005 (by decide)).trans harr
      have hc : (Expr.read 1005 (.const 0)).eval w st = some turns.length := by
        simp [Expr.eval, ha, code, gm06EncodeRows, checkWord, hm]
      exact Crossing.eval_mul (Crossing.eval_const (by omega)) hc hk)
    (fun st d h hd hdlen => by
      have ha : st.arrs 1005 = code := (h.2 1005 (by decide)).trans harr
      have hq : d / 2 < turns.length := by omega
      have hj : 2 + 3 * (d / 2) + d % 2 < code.length := by omega
      have hdfit : d < 2 ^ w := hdlen.trans hk
      have hqfit : d / 2 < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hdfit
      have hrfit : d % 2 < 2 ^ w := lt_trans (Nat.mod_lt _ (by decide)) (by omega)
      have hmul : 3 * (d / 2) < 2 ^ w := lt_of_le_of_lt (by omega) hlen
      have hadd : 2 + 3 * (d / 2) < 2 ^ w := lt_of_le_of_lt (by omega) hlen
      have hjfit : 2 + 3 * (d / 2) + d % 2 < 2 ^ w := hj.trans hlen
      have hindex : gm06Alg511TurnIndexExpr.eval w st =
          some (2 + 3 * (d / 2) + d % 2) := by
        simp [gm06Alg511TurnIndexExpr, Expr.eval, hd, BinOp.eval, BinOp.raw,
          checkWord, hdfit, hqfit, hrfit, hmul, hadd, hjfit,
          show 2 < 2 ^ w by omega, hw]
      have hv : code.getD (2 + 3 * (d / 2) + d % 2) 0 < 2 ^ w := by
        apply hwords
        change code.getD _ 0 ∈ code
        simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
          Option.getD_some] using List.getElem_mem hj
      have heval := Crossing.eval_read (a := 1005) hindex (ha ▸ hj)
        (by simpa [ha, hj] using hv)
      have hlookup : code[2 + 3 * (d / 2) + d % 2] =
          (gm06Alg511TurnWords turns).getD d 0 := by
        have hlookup' : code.getD (2 + 3 * (d / 2) + d % 2) 0 =
            (gm06Alg511TurnWords turns).getD d 0 :=
          gm06Alg511TurnCode_flatten_getD turns d hdlen
        simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
          Option.getD_some] using hlookup'
      simpa only [ha, hlookup] using heval)
  refine ⟨s', t, he, ?_, hkeep, ?_⟩
  · norm_num [Expr.cost, gm06Alg511TurnIndexExpr] at ht
    nlinarith [ht]
  · rw [hout]
    apply List.ext_getElem
    · simp [gm06Alg511TurnWords_length]
    · intro i hi hi'
      simp only [List.length_map, List.length_range] at hi
      simp [hi']

end GraphMinor.Compute
