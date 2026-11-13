module

public import GraphMinor.Compute.GM06Alg34ActiveEdgeExpr
public import GraphMinor.Compute.GM06Alg34RankRead
public import GraphMinor.Compute.GM06Alg34VertexWords

/-!
# Emitting one surviving vertex label

Test the old label in register 109 against the active mask. If it
survives, copy its new rank to the next reserved buffer position and
advance the output count. Otherwise leave the buffer and count alone.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Emit the old vertex label in register 109 into buffer 9, counted by register 142. -/
def gm06EmitVertexProg : Cmd :=
  .ite (gm06ActiveVertexExpr 109)
    (.seq (.write 9 (.reg 142) (gm06VertexRankExpr 109))
      (.assign 142 (.op .add (.reg 142) (.const 1)))) .skip

/-- A single vertex emission implements filtering and relabelling in
at most ten steps, preserving the input, masks, and rank tables. -/
theorem gm06EmitVertexProg_exec {w k : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (v : Fin x.n) (hw : 1 < 2 ^ w)
    (hn : x.n < 2 ^ w) (hk : k + 1 < 2 ^ w) {s : State}
    (hlabel : s.regs 109 = v.val) (hcount : s.regs 142 = k)
    (hmask : s.arrs 4 = gm06VertexMask vs) (hrank : s.arrs 5 = gm06VertexRanks vs)
    (hcap : k < (s.arrs 9).length) :
    ∃ s' t, Exec w gm06EmitVertexProg s s' t ∧ t ≤ 10 ∧
      s'.arrs 9 = (if v ∈ vs then (s.arrs 9).set k ((x.activeVertices vs).idxOf v) else s.arrs 9) ∧
      s'.regs 142 = k + (if v ∈ vs then 1 else 0) ∧
      (∀ a : ℕ, a ≠ 9 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 142 → s'.regs q = s.regs q) := by
  have hc := gm06ActiveVertexExpr_eval vs v 109 hw hn hmask hlabel
  have hkw : k < 2 ^ w := by omega
  by_cases hv : v ∈ vs
  · have hr := gm06VertexRankExpr_eval x vs v hv 109 hn hrank hlabel
    let rank := (x.activeVertices vs).idxOf v
    let s₁ := s.writeArr 9 k rank
    have he₁ : Exec w (.write 9 (.reg 142) (gm06VertexRankExpr 109)) s s₁ 4 :=
      .write (by simp [Expr.eval, checkWord, hcount, hkw]) hr hcap
    let s₂ := s₁.setReg 142 (k + 1)
    have he₂ : Exec w (.assign 142 (.op .add (.reg 142) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcount, hkw, hw, hk])
    have hc' : (gm06ActiveVertexExpr 109).eval w s = some 1 := by simpa only [hv, ↓reduceIte] using hc
    have hex : Exec w gm06EmitVertexProg s s₂ 10 :=
      .ite_true hc' (by decide) (.seq he₁ he₂)
    refine ⟨s₂, 10, hex, le_rfl, ?_, ?_, ?_, ?_⟩
    · simp only [hv, ↓reduceIte]
      rfl
    · simp [s₂, hv]
    · intro a ha
      exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [gm06EmitVertexProg, Cmd.writtenArrs, ha])
    · intro q hq
      exact hex.regs_eq_of_not_mem_writtenRegs (by simp [gm06EmitVertexProg, Cmd.writtenRegs, hq])
  · have hc' : (gm06ActiveVertexExpr 109).eval w s = some 0 := by simpa only [hv, ↓reduceIte] using hc
    refine ⟨s, 3, .ite_false hc' (.skip s), by decide, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    · simp only [hv, ↓reduceIte]
    · simpa only [hv, ↓reduceIte, Nat.add_zero] using hcount

end GraphMinor.Compute
