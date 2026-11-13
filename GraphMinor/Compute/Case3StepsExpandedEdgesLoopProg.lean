module

public import GraphMinor.Compute.Case3StepsExpandPairProg

/-!
# Scanning the compact member's positive pairs

The completed record prefix contains every copy of the pairs already read.
The remaining edge multiplicity is a decreasing cost bound: reading one
pair costs a constant, and expanding it costs a constant per directed copy.
Thus the whole scan is linear in the member's positive pairs and edges.
-/

public section

namespace GraphMinor.Compute

/-- The positive-pair loop writes the exact renamed expanded record. Its
cost is bounded by the remaining pair count and remaining edge multiplicity. -/
theorem case3ExpandedEdgesLoopProg_exec {w n N : ℕ} (G : MultiDigraph n) (orig : Fin n → Fin N)
    (hinj : Function.Injective orig) (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * G.numActivePairs < 2 ^ w) (he : 3 * G.numEdges + 1 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = G.numActivePairs) {s : State}
    (hG : s.arrs 38 = G.enc)
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1))
    (hrA : s.regs 105 = G.numActivePairs) (hrk : s.regs 103 = k)
    (hrq : s.regs 109 = MultiDigraph.sumEdgeMult G (G.activePairsList.take k))
    (hdst : s.arrs 50 =
      case3ExpandedPairs G (origVertexEmb orig hinj) (G.activePairsList.take k) ++
        List.replicate (3 * (G.numEdges - MultiDigraph.sumEdgeMult G (G.activePairsList.take k))) 0) :
    ∃ s' t, Exec w (forUp 103 (.reg 105) case3ExpandPairProg) s s' t ∧
      t ≤ 3 + 41 * rem + 26 * (G.numEdges - MultiDigraph.sumEdgeMult G (G.activePairsList.take k)) ∧
      s'.arrs 50 = case3ExpandedPairs G (origVertexEmb orig hinj) G.activePairsList := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hAw : G.numActivePairs < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = G.numActivePairs := by omega
    have hc : (Expr.op .lt (.reg 103) (.reg 105)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrA, hk, hAw, h0]
    refine ⟨s, 3, .while_false hc, by omega, ?_⟩
    have htake : G.activePairsList.take k = G.activePairsList := by
      apply List.take_of_length_le
      exact hk.ge
    simpa only [htake, G.sumEdgeMult_activePairsList, Nat.sub_self,
      Nat.mul_zero, List.replicate_zero, List.append_nil] using hdst
  | succ rem ih =>
    have hk : k < G.numActivePairs := by omega
    have hkw : k < 2 ^ w := by omega
    have hkp : k + 1 < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg 103) (.reg 105)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrA, hk, hkw, hAw, h1]
    obtain ⟨sB, tB, hexB, htB, hdstB, hrqB, harrB, hregB⟩ :=
      case3ExpandPairProg_exec G orig hinj ⟨k, hk⟩ hw hn hN hA he hG hlabels hrk hrq hdst
    let sC := sB.setReg 103 (k + 1)
    have hrkB : sB.regs 103 = k := (hregB 103 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hrk
    have hexC : Exec w (.assign 103 (.op .add (.reg 103) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrkB, hkw, h1, hkp])
    obtain ⟨s', t, hex, ht, hdst'⟩ := ih (k + 1) (by omega) (s := sC)
      ((harrB 38 (by decide)).trans hG) ((harrB 47 (by decide)).trans hlabels)
      (by rw [State.setReg_regs_ne _ _ (by decide), hregB 105 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]; exact hrA)
      (State.setReg_regs_self ..)
      (by rw [State.setReg_regs_ne _ _ (by decide)]; exact hrqB) hdstB
    refine ⟨s', 3 + (tB + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex, ?_, hdst'⟩
    have hsuc := case3PairPrefix_edges_succ G k hk
    have hle := case3PairPrefix_edges_le G (k + 1)
    have hle' := case3PairPrefix_edges_le G k
    change tB ≤ 26 * G.edgeMult (G.activePairsList[k]).1 (G.activePairsList[k]).2 + 34 at htB
    omega

end GraphMinor.Compute
