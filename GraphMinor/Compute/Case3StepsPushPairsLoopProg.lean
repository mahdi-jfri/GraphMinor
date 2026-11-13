module

public import GraphMinor.Compute.Case3StepsPushPairProg

/-!
# Restoring every positive member pair

The completed prefix contains restored pair records in the compact graph's
order. The remaining slots are zero until their pair is visited. Every
positive pair costs the same constant, independent of its multiplicity.
-/

public section

namespace GraphMinor.Compute

/-- The pair scan restores exactly the canonical ambient-label encoding
body and takes constant time per positive pair. -/
theorem case3PushPairsLoopProg_exec {w N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
    (hw : 3 < 2 ^ w) (hcard : S.card < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w) (he : D.numEdges < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = D.numActivePairs) {s : State}
    (hD : s.arrs 39 = D.enc) (hlistlen : S.card ≤ (s.arrs 32).length)
    (hlist : ∀ i : Fin S.card, (s.arrs 32).getD i.1 0 = (S.orderEmbOfFin rfl i).1)
    (hdst : s.arrs 54 = [N, D.numActivePairs] ++ case3PushFlatTriples S D (D.activePairsList.take k) ++
      List.replicate (3 * (D.numActivePairs - k)) 0)
    (hrA : s.regs 105 = D.numActivePairs) (hrk : s.regs 103 = k) :
    ∃ s' t, Exec w (forUp 103 (.reg 105) case3PushPairProg) s s' t ∧ t ≤ 3 + 35 * rem ∧
      s'.arrs 54 = (case3PushMultigraph S D).enc := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hAw : D.numActivePairs < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = D.numActivePairs := by omega
    have hc : (Expr.op .lt (.reg 103) (.reg 105)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrA, hk, hAw, h0]
    refine ⟨s, 3, .while_false hc, by omega, ?_⟩
    rw [case3PushMultigraph_enc]
    have htake : D.activePairsList.take D.numActivePairs = D.activePairsList := List.take_of_length_le le_rfl
    simpa only [hk, htake, Nat.sub_self, Nat.mul_zero, List.replicate_zero, List.append_nil] using hdst
  | succ rem ih =>
    have hk : k < D.numActivePairs := by omega
    have hkw : k < 2 ^ w := by omega
    have hkp : k + 1 < 2 ^ w := by omega
    have hc : (Expr.op .lt (.reg 103) (.reg 105)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrA, hk, hkw, hAw, h1]
    let pre := [N, D.numActivePairs] ++ case3PushFlatTriples S D (D.activePairsList.take k)
    let suf := List.replicate (3 * (D.numActivePairs - (k + 1))) 0
    have hpre : pre.length = 2 + 3 * k := by
      simp only [pre, List.length_append, List.length_cons, List.length_nil,
        case3PushFlatTriples_length, List.length_take]
      rw [Nat.min_eq_left (show k ≤ D.activePairsList.length from hk.le)]
    have hrep : List.replicate (3 * (D.numActivePairs - k)) 0 = [0, 0, 0] ++ suf := by
      rw [show 3 * (D.numActivePairs - k) = 3 + 3 * (D.numActivePairs - (k + 1)) by omega,
        List.replicate_add]
      rfl
    obtain ⟨sB, hexB, hdstB, harrB, hregB⟩ := case3PushPairProg_exec S D ⟨k, hk⟩ pre suf hpre
      hw hcard hN hA he hD hlistlen hlist (by rw [hdst, hrep]; simp only [pre, List.append_assoc]) hrk
    let sC := sB.setReg 103 (k + 1)
    have hexC : Exec w (.assign 103 (.op .add (.reg 103) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hregB 103 (by decide), hrk, hkw, h1, hkp])
    have hdstC : sC.arrs 54 = [N, D.numActivePairs] ++ case3PushFlatTriples S D (D.activePairsList.take (k + 1)) ++
        List.replicate (3 * (D.numActivePairs - (k + 1))) 0 := by
      rw [State.setReg_arrs, hdstB, case3PushFlatTriples_take_succ S D k hk]
      simp only [pre, suf, List.append_assoc]
      rfl
    obtain ⟨s', t, hex, ht, hdst'⟩ := ih (k + 1) (by omega) (s := sC)
      ((harrB 39 (by decide)).trans hD)
      (by rw [State.setReg_arrs, harrB 32 (by decide)]; exact hlistlen)
      (by intro i; rw [State.setReg_arrs, harrB 32 (by decide)]; exact hlist i)
      hdstC
      (by rw [State.setReg_regs_ne _ _ (show (105 : ℕ) ≠ 103 by decide), hregB 105 (by decide)]; exact hrA)
      (State.setReg_regs_self ..)
    exact ⟨s', 3 + (28 + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex, by omega, hdst'⟩

end GraphMinor.Compute
