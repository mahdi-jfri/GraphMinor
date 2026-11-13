module

public import GraphMinor.Compute.GM06Alg34VertexEdgeMark
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Active-edge adjacency marks after deleting an initial vertex

Reduction 2 in VI, page 129, separates components attached only
at an initial vertex. Its component search ignores inactive edges
and all edges touching that vertex. The local matrix step checks
these conditions before marking the two endpoint adjacencies.
Loops are skipped by the verified edge writer.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Adjacency row marks for an active edge not touching the removed vertex. -/
def gm06PuncturedEdgeRows {n : ℕ} (e : Fin n × Fin n) (b : ℕ) (cut : Fin n) :
    List (ℕ × List ℕ) :=
  if b = 1 then if e.1 = cut then [] else if e.2 = cut then [] else gm06VertexEdgeRows e else []

/-- Guard the endpoint writer by activity in 134 and the removed label in 135. -/
def gm06PuncturedEdgeMarkProg : Cmd :=
  .ite (.op .eq (.reg 134) (.const 1))
    (.ite (.op .eq (.reg 132) (.reg 135)) .skip
      (.ite (.op .eq (.reg 133) (.reg 135)) .skip gm06VertexEdgeMarkProg)) .skip

/-- One guarded edge contributes exactly its punctured adjacency marks,
with constant time and no change to the endpoint registers. -/
theorem gm06PuncturedEdgeMarkProg_exec {w n : ℕ} (e : Fin n × Fin n) (b : ℕ) (cut : Fin n)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w) (hb : b ≤ 1)
    {s : State} (hN : s.regs 100 = n) (hA : s.regs 132 = e.1.val)
    (hB : s.regs 133 = e.2.val) (hactive : s.regs 134 = b) (hcut : s.regs 135 = cut.val)
    (hcap : (s.arrs 28).length = n * n) :
    ∃ s' t, Exec w gm06PuncturedEdgeMarkProg s s' t ∧ t ≤ 26 ∧
      s'.arrs 28 = (gm06PuncturedEdgeRows e b cut).foldl (gm06MatrixMarkRow n) (s.arrs 28) ∧
      (∀ a : ℕ, a ≠ 28 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, s'.regs q = s.regs q) := by
  have hbword : b < 2 ^ w := hb.trans_lt hw
  have htest := GraphMinor.Compute.Crossing.eval_eq
    (GraphMinor.Compute.Crossing.eval_reg hactive hbword)
    (GraphMinor.Compute.Crossing.eval_const hw) hw
  have htestA := GraphMinor.Compute.Crossing.eval_eq
    (GraphMinor.Compute.Crossing.eval_reg hA (e.1.isLt.trans hn))
    (GraphMinor.Compute.Crossing.eval_reg hcut (cut.isLt.trans hn)) hw
  have htestB := GraphMinor.Compute.Crossing.eval_eq
    (GraphMinor.Compute.Crossing.eval_reg hB (e.2.isLt.trans hn))
    (GraphMinor.Compute.Crossing.eval_reg hcut (cut.isLt.trans hn)) hw
  by_cases hb1 : b = 1
  · have hact : (Expr.op .eq (.reg 134) (.const 1)).eval w s = some 1 := by simpa [hb1] using htest
    by_cases hAc : e.1 = cut
    · have hAc' : e.1.val = cut.val := congrArg Fin.val hAc
      have heq : (Expr.op .eq (.reg 132) (.reg 135)).eval w s = some 1 := by simpa [hAc'] using htestA
      refine ⟨s, 7, .ite_true hact (by decide) (.ite_true heq (by decide) (.skip s)),
        by omega, ?_, fun _ _ => rfl, fun _ => rfl⟩
      simp [gm06PuncturedEdgeRows, hb1, hAc]
    · have hAc' : e.1.val ≠ cut.val := fun h => hAc (Fin.ext h)
      have heq : (Expr.op .eq (.reg 132) (.reg 135)).eval w s = some 0 := by simpa [hAc'] using htestA
      by_cases hBc : e.2 = cut
      · have hBc' : e.2.val = cut.val := congrArg Fin.val hBc
        have heqB : (Expr.op .eq (.reg 133) (.reg 135)).eval w s = some 1 := by simpa [hBc'] using htestB
        refine ⟨s, 10, .ite_true hact (by decide) (.ite_false heq (.ite_true heqB (by decide) (.skip s))),
          by omega, ?_, fun _ _ => rfl, fun _ => rfl⟩
        simp [gm06PuncturedEdgeRows, hb1, hAc, hBc]
      · have hBc' : e.2.val ≠ cut.val := fun h => hBc (Fin.ext h)
        have heqB : (Expr.op .eq (.reg 133) (.reg 135)).eval w s = some 0 := by simpa [hBc'] using htestB
        obtain ⟨s', t, he, ht, hmat, ha, hg⟩ :=
          gm06VertexEdgeMarkProg_exec e hw hn hsquare hN hA hB hcap
        refine ⟨s', 3 + (3 + (3 + t)), .ite_true hact (by decide) (.ite_false heq (.ite_false heqB he)),
          by omega, ?_, ha, hg⟩
        simpa only [gm06PuncturedEdgeRows, hb1, hAc, hBc, ite_true, ite_false] using hmat
  · have hact : (Expr.op .eq (.reg 134) (.const 1)).eval w s = some 0 := by simpa [hb1] using htest
    refine ⟨s, 4, .ite_false hact (.skip s), by omega, ?_, fun _ _ => rfl, fun _ => rfl⟩
    simp [gm06PuncturedEdgeRows, hb1]

end GraphMinor.Compute
