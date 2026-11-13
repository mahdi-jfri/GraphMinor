module

public import GraphMinor.Compute.GM06Alg34RootMaskLoop

/-!
# Allocating and computing the canonical region-root mask

Allocate one flag for each supplied cell, initialize the source scan,
and query every label. Only finite input arrays and derived graph
arrays are read. The mask selects exactly the region representatives
used by the induced drawing payload.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Allocate root mask 36 and compute its canonical flags. -/
def gm06RootMaskProg : Cmd :=
  .seq (.alloc 36 (.reg 4)) (.seq (.assign 187 (.const 0)) gm06RootMaskLoopProg)

/-- The root-mask construction starts with arbitrary scratch and
computes exactly the canonical region representatives in cubic time. -/
theorem gm06RootMaskProg_exec {w : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) {s : State}
    (hsize : s.regs 4 = x.cellCount) (hn : s.regs 100 = x.n)
    (hm : s.regs 101 = x.ends.length) (hv : s.arrs 4 = gm06VertexMask vs)
    (he : s.arrs 6 = gm06EdgeMask x vs)
    (hlists : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s)
    (hlen : (s.arrs 32).length = x.cellCount * x.cellCount) :
    ∃ s' t, Exec w gm06RootMaskProg s s' t ∧
      t ≤ x.cellCount * (26 * (x.cellCount * x.cellCount) + 46 * x.cellCount + 80) + x.cellCount + 6 ∧
      s'.arrs 36 = gm06RootMask x vs ∧
      (∀ k : ℕ, k ≠ 33 → k ≠ 34 → k ≠ 35 → k ≠ 36 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, (q < 190 ∨ 201 ≤ q) → q ≠ 187 → s'.regs q = s.regs q) := by
  let s₁ := s.setArr 36 (List.replicate x.cellCount 0)
  let s₂ := s₁.setReg 187 0
  have hex₁ : Exec w (.alloc 36 (.reg 4)) s s₁ (1 + x.cellCount) :=
    .alloc (by simp [Expr.eval, checkWord, hsize, hN])
  have hex₂ : Exec w (.assign 187 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hlists₂ : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s₂ :=
    hlists.of_arrs_eq (by simp [s₂, s₁]) (by simp [s₂, s₁]) (by simp [s₂, s₁])
  obtain ⟨s₃, t, hex₃, ht, hbuf, _, harr, hreg⟩ :=
    gm06RootMaskLoopProg_exec x vs hw hN hsquare (s := s₂)
      (by simpa [s₂, s₁] using hsize) (by simp [s₂])
      (by simpa [s₂, s₁] using hn) (by simpa [s₂, s₁] using hm)
      (by simpa [s₂, s₁] using hv) (by simpa [s₂, s₁] using he)
      hlists₂ (by simpa [s₂, s₁] using hlen) (by simp [s₂, s₁])
  refine ⟨s₃, (1 + x.cellCount) + (2 + t), Exec.seq hex₁ (Exec.seq hex₂ hex₃),
    by omega, hbuf, ?_, ?_⟩
  · intro k hk₁ hk₂ hk₃ hk₄
    exact (harr k hk₁ hk₂ hk₃ hk₄).trans (by simp [s₂, s₁, hk₄])
  · intro q hq hq'
    exact (hreg q hq hq').trans (by simp [s₂, s₁, hq'])

end GraphMinor.Compute
