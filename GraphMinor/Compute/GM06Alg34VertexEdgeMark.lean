module

public import GraphMinor.Compute.GM06Alg34VertexMatrixData
import GraphMinor.Compute.GM06Alg34RegionRow

/-!
# Marking one supplied edge in the vertex adjacency matrix

Skip a loop. Otherwise mark the two directed positions given by the
endpoint registers. The matrix remains the same size, and neither the
endpoint registers nor the source input changes.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Mark both orientations of the endpoints in 132/133 in matrix array 28. -/
def gm06VertexEdgeMarkProg : Cmd :=
  .ite (.op .eq (.reg 132) (.reg 133)) .skip
    (.seq (.write 28 (.op .add (.op .mul (.reg 100) (.reg 132)) (.reg 133)) (.const 1))
      (.write 28 (.op .add (.op .mul (.reg 100) (.reg 133)) (.reg 132)) (.const 1)))

/-- One edge updates exactly its finite row marks in at most seventeen
steps, preserving all registers and all other arrays. -/
theorem gm06VertexEdgeMarkProg_exec {w n : ℕ} (e : Fin n × Fin n)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    {s : State} (hNr : s.regs 100 = n) (hA : s.regs 132 = e.1.val)
    (hB : s.regs 133 = e.2.val) (hcap : (s.arrs 28).length = n * n) :
    ∃ s' t, Exec w gm06VertexEdgeMarkProg s s' t ∧ t ≤ 17 ∧
      s'.arrs 28 = (gm06VertexEdgeRows e).foldl (gm06MatrixMarkRow n) (s.arrs 28) ∧
      (∀ a : ℕ, a ≠ 28 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, s'.regs q = s.regs q) := by
  have ha := e.1.isLt.trans hn
  have hb := e.2.isLt.trans hn
  by_cases he : e.1 = e.2
  · have hc : (Expr.op .eq (.reg 132) (.reg 133)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hA, hB, ha, hb, he, hw]
    refine ⟨s, 4, .ite_true hc (by decide) (.skip s), by omega, ?_, fun _ _ => rfl, fun _ => rfl⟩
    simp only [gm06VertexEdgeRows, he, ↓reduceIte, List.foldl_nil]
  · have he' : e.1.val ≠ e.2.val := fun h => he (Fin.ext h)
    have hc : (Expr.op .eq (.reg 132) (.reg 133)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hA, hB, ha, hb, he', Nat.zero_lt_of_lt hw]
    have hab := gm06MatrixAddress_lt e.1.isLt e.2.isLt
    have hba := gm06MatrixAddress_lt e.2.isLt e.1.isLt
    have hpa : n * e.1.val < 2 ^ w := by omega
    have hpb : n * e.2.val < 2 ^ w := by omega
    have habw := hab.trans hsquare
    have hbaw := hba.trans hsquare
    let s₁ := s.writeArr 28 (n * e.1.val + e.2.val) 1
    let s₂ := s₁.writeArr 28 (n * e.2.val + e.1.val) 1
    have hex₁ : Exec w (.write 28
        (.op .add (.op .mul (.reg 100) (.reg 132)) (.reg 133)) (.const 1)) s s₁ 7 :=
      .write (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hNr, hA, hB, hn, ha, hb, hpa, habw])
        (by simp [Expr.eval, checkWord, hw]) (by rw [hcap]; exact hab)
    have hex₂ : Exec w (.write 28
        (.op .add (.op .mul (.reg 100) (.reg 133)) (.reg 132)) (.const 1)) s₁ s₂ 7 :=
      .write (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hNr, hA, hB, hn, ha, hb, hpb, hbaw])
        (by simp [Expr.eval, checkWord, hw])
        (by simp only [s₁, State.writeArr, State.setArr_arrs_self, List.length_set, hcap]; exact hba)
    refine ⟨s₂, 17, .ite_false hc (.seq hex₁ hex₂), by omega, ?_, ?_, fun _ => rfl⟩
    · simp [s₂, s₁, State.writeArr, gm06VertexEdgeRows, he, gm06MatrixMarkRow, gm06MarkCells]
    · intro a ha40
      exact (State.writeArr_arrs_ne _ _ _ ha40).trans (State.writeArr_arrs_ne _ _ _ ha40)

end GraphMinor.Compute
