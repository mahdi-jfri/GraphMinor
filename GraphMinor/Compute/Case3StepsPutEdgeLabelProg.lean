module

public import GraphMinor.Compute.Case3StepsEdgeMatrix

/-!
# Writing both directed positions of an edge owner

The endpoint matrix uses row-major positions. Two writes record the same
owner for the two directions of a simple edge. All registers survive, and
the endpoint bounds ensure that both writes lie inside the square table.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Write register 44 at the two endpoint positions in the owner matrix. -/
def case3PutEdgeLabelProg : Cmd :=
  .seq (.write 34 (.op .add (.op .mul (.reg 42) (.reg 14)) (.reg 43)) (.reg 44))
    (.write 34 (.op .add (.op .mul (.reg 43) (.reg 14)) (.reg 42)) (.reg 44))

/-- Two directed owner writes take fourteen steps and retain all registers. -/
theorem case3PutEdgeLabelProg_exec {w n : ℕ} (u v : Fin n) (label : ℕ)
    (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w) (hlabel : label < 2 ^ w)
    {s : State} (hlen : (s.arrs 34).length = n * n)
    (hrn : s.regs 14 = n) (hru : s.regs 42 = u.1) (hrv : s.regs 43 = v.1)
    (hrlabel : s.regs 44 = label) :
    Exec w case3PutEdgeLabelProg s
      ((s.writeArr 34 (case3PairPosition u v) label).writeArr 34 (case3PairPosition v u) label) 14 := by
  have hidx (a b : Fin n) (ra rb : ℕ) (hra : s.regs ra = a.1) (hrb : s.regs rb = b.1) :
      (Expr.op .add (.op .mul (.reg ra) (.reg 14)) (.reg rb)).eval w s =
        some (case3PairPosition a b) := by
    have hpos := (case3PairPosition_lt a b).trans hsquare
    have hmul : a.1 * n < 2 ^ w := by
      unfold case3PairPosition at hpos
      omega
    dsimp only [case3PairPosition] at hpos
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hra, hrb, hrn,
      a.2.trans hn, b.2.trans hn, hn, hmul, case3PairPosition, hpos]
  have hv : (Expr.reg 44).eval w s = some label := by
    simp only [Expr.eval, checkWord, hrlabel, hlabel, ↓reduceIte]
  have hex₁ : Exec w
      (.write 34 (.op .add (.op .mul (.reg 42) (.reg 14)) (.reg 43)) (.reg 44)) s
      (s.writeArr 34 (case3PairPosition u v) label) 7 :=
    .write (hidx u v 42 43 hru hrv) hv (by rw [hlen]; exact case3PairPosition_lt u v)
  have hex₂ : Exec w
      (.write 34 (.op .add (.op .mul (.reg 43) (.reg 14)) (.reg 42)) (.reg 44))
      (s.writeArr 34 (case3PairPosition u v) label)
      ((s.writeArr 34 (case3PairPosition u v) label).writeArr 34 (case3PairPosition v u) label) 7 :=
    .write (by simpa only [Expr.eval, State.writeArr_regs] using hidx v u 43 42 hrv hru)
      (by simpa only [Expr.eval, State.writeArr_regs] using hv)
      (by rw [State.writeArr_arrs_self, List.length_set, hlen]; exact case3PairPosition_lt v u)
  exact .seq hex₁ hex₂

end GraphMinor.Compute
