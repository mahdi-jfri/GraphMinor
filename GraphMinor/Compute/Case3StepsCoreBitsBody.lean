module

public import GraphMinor.Compute.Case3StepsCoreDecode

/-!
# One word of the core bitset

The (8.6) decoder uses nonzero words of the output tail as membership bits.
The program checks the output length before reading. It caps a read at one,
so it also implements the decoder for words larger than the current word
size, without requiring a bound on those words themselves.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Normalize the word at `a_raw[r_i + 1]`, or write zero if it is missing. -/
def case3CoreBitBody (a_raw a_Z r_i : ℕ) : Cmd :=
  .ite (.op .lt (.op .add (.reg r_i) (.const 1)) (.len a_raw))
    (.write a_Z (.reg r_i)
      (.op .lt (.const 0) (.readMin a_raw (.op .add (.reg r_i) (.const 1)) (.const 1))))
    (.write a_Z (.reg r_i) (.const 0))

/-- One normalized bit is written in at most fifteen steps. -/
theorem case3CoreBitBody_exec {w n k : ℕ} (out : List ℕ)
    (a_raw a_Z r_i : ℕ) (hk : k < n) (hn : n + 1 < 2 ^ w)
    (hlen : out.length < 2 ^ w) {s : State}
    (hraw : s.arrs a_raw = out) (hZ : (s.arrs a_Z).length = n) (hi : s.regs r_i = k) :
    ∃ t, Exec w (case3CoreBitBody a_raw a_Z r_i) s
      (s.writeArr a_Z k (if out.getD (k + 1) 0 = 0 then 0 else 1)) t ∧ t ≤ 15 := by
  have hw : 1 < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  have hkw : k < 2 ^ w := by omega
  have hkp : k + 1 < 2 ^ w := by omega
  have hkZ : k < (s.arrs a_Z).length := by rw [hZ]; exact hk
  by_cases hp : k + 1 < out.length
  · have hcond : (Expr.op .lt (.op .add (.reg r_i) (.const 1)) (.len a_raw)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hi, hraw, hkw, hw, hkp, hlen, hp]
    have hbitw : (if out.getD (k + 1) 0 = 0 then 0 else 1) < 2 ^ w := by
      split_ifs <;> omega
    have hval : (Expr.op .lt (.const 0)
        (.readMin a_raw (.op .add (.reg r_i) (.const 1)) (.const 1))).eval w s =
        some (if out.getD (k + 1) 0 = 0 then 0 else 1) := by
      rw [List.getD_eq_getElem out 0 hp]
      by_cases hz : out[k + 1] = 0
      · simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hi, hraw, hkw, hw, hkp, hp, hz, h0]
      · have hmin : min out[k + 1] 1 = 1 := Nat.min_eq_right (by omega)
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hi, hraw, hkw, hw, hkp, hp, hz, hmin, h0]
    refine ⟨15, .ite_true (t := 10) hcond (by decide) ?_, by omega⟩
    exact .write (by simp only [Expr.eval, hi, checkWord, hkw, ↓reduceIte]) hval hkZ
  · have hcond : (Expr.op .lt (.op .add (.reg r_i) (.const 1)) (.len a_raw)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hi, hraw, hkw, hw, hkp, hlen, hp, h0]
    have hb : (if out.getD (k + 1) 0 = 0 then 0 else 1) = 0 := by
      rw [List.getD_eq_default out 0 (by omega)]
      rfl
    rw [hb]
    refine ⟨8, .ite_false (t := 3) hcond ?_, by omega⟩
    exact .write (by simp only [Expr.eval, hi, checkWord, hkw, ↓reduceIte])
      (by simp only [Expr.eval, checkWord, h0, ↓reduceIte]) hkZ

end GraphMinor.Compute
