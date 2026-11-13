module

public import GraphMinor.Compute.GM06Alg34ReadEnds
public import GraphMinor.Compute.GM06Alg34ActiveEdgeExpr

/-!
# One surviving-edge table entry

Read an edge's endpoint pair from the input stream, test both endpoints
in the active vertex mask, and write the result to the edge table.
The step preserves all other table entries and the supplied input.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read one edge and write its survival bit at the edge index in register 135. -/
def gm06EdgeMaskStepProg : Cmd :=
  .seq gm06ReadEndsProg (.write 6 (.reg 135) (gm06ActiveEdgeExpr 132 133))

/-- The edge-table step writes exactly the finite induced-edge predicate,
advances two endpoint words, and takes at most 23 RAM steps. -/
theorem gm06EdgeMaskStepProg_exec {w off k : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (e : Fin x.ends.length) (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hoff : off + 2 < 2 ^ w)
    (hk : k < 2 ^ w) {s : State}
    (hstream : AtStream 0 off (x.ends[e].1.val :: x.ends[e].2.val :: tail) s)
    (hpos : s.regs 103 = off) (hindex : s.regs 135 = k)
    (hmask : s.arrs 4 = gm06VertexMask vs) (hcap : k < (s.arrs 6).length) :
    ∃ s' t, Exec w gm06EdgeMaskStepProg s s' t ∧ t ≤ 23 ∧
      s'.arrs 6 = (s.arrs 6).set k (if x.activeCell vs (.inr (.inl e)) then 1 else 0) ∧
      s'.regs 103 = off + 2 ∧ AtStream 0 (off + 2) tail s' ∧
      (∀ a : ℕ, a ≠ 6 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 132 → q ≠ 133 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hA, hB, hp₁, hs₁, ha₁, hr₁⟩ :=
    gm06ReadEndsProg_exec hw hoff (x.ends[e].1.isLt.trans hn)
      (x.ends[e].2.isLt.trans hn) hstream hpos
  have hmask₁ : s₁.arrs 4 = gm06VertexMask vs := (ha₁ 4).trans hmask
  have hidx₁ : s₁.regs 135 = k :=
    (hr₁ 135 (by decide) (by decide) (by decide)).trans hindex
  have hval := gm06ActiveEdgeExpr_eval x vs e 132 133 hw hn hmask₁ hA hB
  let bit := if x.activeCell vs (.inr (.inl e)) then 1 else 0
  let s₂ := s₁.writeArr 6 k bit
  have he₂ : Exec w (.write 6 (.reg 135) (gm06ActiveEdgeExpr 132 133)) s₁ s₂ 7 :=
    .write (by simp [Expr.eval, checkWord, hidx₁, hk]) hval
      (by rw [ha₁ 6]; exact hcap)
  refine ⟨s₂, t₁ + 7, .seq he₁ he₂, by omega, ?_, hp₁, ?_, ?_, ?_⟩
  · change (s₁.arrs 6).set k bit = _
    rw [ha₁ 6]
  · exact hs₁.of_arr_eq (State.writeArr_arrs_ne _ _ _ (by decide))
  · intro a ha
    exact (State.writeArr_arrs_ne _ _ _ ha).trans (ha₁ a)
  · exact hr₁

end GraphMinor.Compute
