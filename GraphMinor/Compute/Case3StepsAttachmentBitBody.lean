module

public import GraphMinor.Compute.Case3StepsComponentDegreesProg

/-!
# Testing one attachment vertex

A vertex belongs to the attachment set when it is in the core and has a
positive neighbor count into the selected component. Both tests are reads
from existing arrays. Their product is a normalized zero-or-one word.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Write one core-masked positive-degree bit. -/
def case3AttachmentBitBody (a_Z a_deg a_att r_i : ℕ) : Cmd :=
  .write a_att (.reg r_i)
    (.op .mul (.read a_Z (.reg r_i))
      (.op .lt (.const 0) (.read a_deg (.reg r_i))))

/-- One attachment test takes nine steps and writes the correct indicator. -/
theorem case3AttachmentBitBody_exec {w : ℕ} (x : Alg81Input)
    (Z : Finset (Fin x.n)) (u v : Fin x.n) (a_Z a_deg a_att r_i : ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    {s : State} (hZ : IsBitSet Z a_Z s)
    (hdeg : IsDegIntoArr x.G (case3ComponentRowSet x Z u) a_deg s)
    (hlen : (s.arrs a_att).length = x.n) (hri : s.regs r_i = v.1) :
    Exec w (case3AttachmentBitBody a_Z a_deg a_att r_i) s
      (s.writeArr a_att v.1 (if v ∈ case3AttachmentRowSet x Z u then 1 else 0)) 9 := by
  have h0 : 0 < 2 ^ w := by omega
  have hvw : v.1 < 2 ^ w := v.2.trans hn
  have hvZ : v.1 < (s.arrs a_Z).length := by rw [hZ.1]; exact v.2
  have hb : (s.arrs a_Z)[v.1]'hvZ = if v ∈ Z then 1 else 0 := by
    simpa only [hZ.arr_eq_bitSetList] using getElem_bitSetList Z v.1 v.2
  obtain ⟨hdlen, hdval⟩ := hdeg
  have hvD : v.1 < (s.arrs a_deg).length := by rw [hdlen]; exact v.2
  have hd : (s.arrs a_deg)[v.1]'hvD = degInto x.G (case3ComponentRowSet x Z u) v := hdval v
  have hdw : degInto x.G (case3ComponentRowSet x Z u) v < 2 ^ w :=
    (degInto_le_n _ _ _).trans_lt hn
  have hidx : (Expr.reg r_i).eval w s = some v.1 := by
    simp only [Expr.eval, checkWord, hri, hvw, ↓reduceIte]
  have hval : (Expr.op .mul (.read a_Z (.reg r_i))
      (.op .lt (.const 0) (.read a_deg (.reg r_i)))).eval w s =
        some (if v ∈ case3AttachmentRowSet x Z u then 1 else 0) := by
    by_cases hz : v ∈ Z <;>
      by_cases hp : 0 < degInto x.G (case3ComponentRowSet x Z u) v <;>
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hvw, hvZ, hvD,
        hb, hd, hdw, hw, h0, hz, hp, case3AttachmentRowSet]
  exact .write hidx hval (by rw [hlen]; exact v.2)

end GraphMinor.Compute
