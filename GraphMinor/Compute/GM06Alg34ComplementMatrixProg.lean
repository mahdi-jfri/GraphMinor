module

public import GraphMinor.Compute.GM06Alg34ComplementMatrixLoop

/-!
# Allocating and computing the complement adjacency matrix

Allocate one slot per ordered pair of supplied cells, start the flat
index at zero, and run the verified scan. The resulting matrix can be
passed directly to the existing adjacency-list and component programs.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute the complement adjacency matrix in array 28. -/
def gm06ComplementMatrixProg : Cmd :=
  .seq (.alloc 28 (.op .mul (.reg 170) (.reg 170)))
    (.seq (.assign 186 (.const 0)) gm06ComplementMatrixLoopProg)

/-- From computed closure and survival tables, construct the exact
complement adjacency matrix in at most `123 * N² + 9` RAM steps. -/
theorem gm06ComplementMatrixProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    {s : State} (hmat : s.arrs 12 = gm06ClosureMatrixData x)
    (hc : s.regs 170 = x.cellCount) (hn : s.regs 100 = x.n)
    (hm : s.regs 101 = x.ends.length) (hv : s.arrs 4 = gm06VertexMask vs)
    (he : s.arrs 6 = gm06EdgeMask x vs) :
    ∃ s' t, Exec w gm06ComplementMatrixProg s s' t ∧
      t ≤ 123 * (x.cellCount * x.cellCount) + 9 ∧
      s'.arrs 28 = gm06ComplementMatrixData x vs ∧
      IsAdjMatrix (x.complementGraph vs) 28 s' ∧
      (∀ k : ℕ, k ≠ 28 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q ≠ 180 → q ≠ 181 → q ≠ 182 → q ≠ 183 → q ≠ 184 → q ≠ 186 →
        s'.regs q = s.regs q) := by
  let N := x.cellCount * x.cellCount
  let s₁ := s.setArr 28 (List.replicate N 0)
  let s₂ := s₁.setReg 186 0
  have heval : (Expr.op .mul (.reg 170) (.reg 170)).eval w s = some N := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc, hN, hsquare, N]
  have hex₁ : Exec w (.alloc 28 (.op .mul (.reg 170) (.reg 170))) s s₁ (3 + N) := .alloc heval
  have hex₂ : Exec w (.assign 186 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  obtain ⟨s₃, t, hex₃, ht, hbuf, _, harr, hreg⟩ :=
    gm06ComplementMatrixLoopProg_exec x vs hw hN hsquare (s := s₂)
      (by simpa [s₂, s₁] using hmat) (by simpa [s₂, s₁] using hc) (by simp [s₂])
      (by simpa [s₂, s₁] using hn) (by simpa [s₂, s₁] using hm)
      (by simpa [s₂, s₁] using hv) (by simpa [s₂, s₁] using he)
      (by simp [s₂, s₁, N])
  refine ⟨s₃, (3 + N) + (2 + t), Exec.seq hex₁ (Exec.seq hex₂ hex₃),
    by dsimp only [N]; omega, hbuf, ?_, ?_, ?_⟩
  · change IsAdjMatrixList (x.complementGraph vs) (s₃.arrs 28)
    simpa only [hbuf] using gm06ComplementMatrixData_isAdjMatrixList x vs
  · intro k hk
    exact (harr k hk).trans (by simp [s₂, s₁, hk])
  · intro q hq₁ hq₂ hq₃ hq₄ hq₅ hq₆
    exact (hreg q hq₁ hq₂ hq₃ hq₄ hq₅ hq₆).trans (by simp [s₂, s₁, hq₆])

end GraphMinor.Compute
