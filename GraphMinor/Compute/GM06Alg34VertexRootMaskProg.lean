module

public import GraphMinor.Compute.GM06Alg34VertexRootMaskLoop

/-!
# Allocating and computing the canonical component-root mask

Allocate one flag for each supplied cell, initialize the source scan,
and query every label. Only finite input arrays and derived graph
arrays are read. The mask selects exactly the component representatives
used by the induced drawing payload.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Allocate root mask 36 and compute its canonical flags. -/
def gm06VertexRootMaskProg : Cmd :=
  .seq (.alloc 36 (.reg 4)) (.seq (.assign 187 (.const 0)) gm06VertexRootMaskLoopProg)

/-- The root-mask construction starts with arbitrary scratch and
computes exactly the canonical component representatives in cubic time. -/
theorem gm06VertexRootMaskProg_exec {w : ℕ} (x : GM06DrawingData) 
    (hw : 1 < 2 ^ w) (hN : x.n < 2 ^ w)
    (hsquare : x.n * x.n < 2 ^ w) {s : State}
    (hsize : s.regs 4 = x.n)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n) :
    ∃ s' t, Exec w gm06VertexRootMaskProg s s' t ∧
      t ≤ x.n * (26 * (x.n * x.n) + 46 * x.n + 80) + x.n + 6 ∧
      s'.arrs 36 = gm06VertexRootMask x ∧
      (∀ k : ℕ, k ≠ 33 → k ≠ 34 → k ≠ 35 → k ≠ 36 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, (q < 190 ∨ 201 ≤ q) → q ≠ 187 → s'.regs q = s.regs q) := by
  let s₁ := s.setArr 36 (List.replicate x.n 0)
  let s₂ := s₁.setReg 187 0
  have hex₁ : Exec w (.alloc 36 (.reg 4)) s s₁ (1 + x.n) :=
    .alloc (by simp [Expr.eval, checkWord, hsize, hN])
  have hex₂ : Exec w (.assign 187 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hlists₂ : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s₂ :=
    hlists.of_arrs_eq (by simp [s₂, s₁]) (by simp [s₂, s₁]) (by simp [s₂, s₁])
  obtain ⟨s₃, t, hex₃, ht, hbuf, _, harr, hreg⟩ :=
    gm06VertexRootMaskLoopProg_exec x hw hN hsquare (s := s₂)
      (by simpa [s₂, s₁] using hsize) (by simp [s₂])
      hlists₂ (by simpa [s₂, s₁] using hlen) (by simp [s₂, s₁])
  refine ⟨s₃, (1 + x.n) + (2 + t), Exec.seq hex₁ (Exec.seq hex₂ hex₃),
    by omega, hbuf, ?_, ?_⟩
  · intro k hk₁ hk₂ hk₃ hk₄
    exact (harr k hk₁ hk₂ hk₃ hk₄).trans (by simp [s₂, s₁, hk₄])
  · intro q hq hq'
    exact (hreg q hq hq').trans (by simp [s₂, s₁, hq'])

end GraphMinor.Compute
