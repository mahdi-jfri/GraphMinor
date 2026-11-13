module

public import GraphMinor.Compute.Basic

/-!
# Allocating the supplied-cell incidence matrix

Add the vertex, edge, and region counts from the input header. Store
the total in register 170 and allocate its square as the zero-filled
closure matrix. All later incidence passes use this fixed allocation.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute the total supplied-cell count and allocate its square in array 12. -/
def gm06InitCellMatrixProg : Cmd :=
  .seq (.assign 170 (.op .add (.reg 100) (.op .add (.reg 101) (.reg 102))))
    (.alloc 12 (.op .mul (.reg 170) (.reg 170)))

/-- The header-driven allocation produces exactly the zero-filled square
cell matrix, preserving the input and all other header registers. -/
theorem gm06InitCellMatrixProg_exec {w n m r : ℕ}
    (hN : n + (m + r) < 2 ^ w)
    (hsquare : (n + (m + r)) * (n + (m + r)) < 2 ^ w) {s : State}
    (hn : s.regs 100 = n) (hm : s.regs 101 = m) (hr : s.regs 102 = r) :
    ∃ s', Exec w gm06InitCellMatrixProg s s' ((n + (m + r)) * (n + (m + r)) + 9) ∧
      s'.arrs 12 = List.replicate ((n + (m + r)) * (n + (m + r))) 0 ∧
      s'.regs 170 = n + (m + r) ∧
      (∀ a : ℕ, a ≠ 12 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 170 → s'.regs q = s.regs q) := by
  have hnw : n < 2 ^ w := by omega
  have hmw : m < 2 ^ w := by omega
  have hrw : r < 2 ^ w := by omega
  have hmrw : m + r < 2 ^ w := by omega
  let N := n + (m + r)
  let s₁ := s.setReg 170 N
  have he₁ : Exec w (.assign 170 (.op .add (.reg 100) (.op .add (.reg 101) (.reg 102)))) s s₁ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hn, hm, hr, hnw, hmw, hrw, hmrw, hN, N])
  let s₂ := s₁.setArr 12 (List.replicate (N * N) 0)
  have he₂ : Exec w (.alloc 12 (.op .mul (.reg 170) (.reg 170))) s₁ s₂ (3 + N * N) :=
    .alloc (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, N, hN, hsquare])
  have hex : Exec w gm06InitCellMatrixProg s s₂ ((n + (m + r)) * (n + (m + r)) + 9) := by
    have hh : Exec w gm06InitCellMatrixProg s s₂ (6 + (3 + N * N)) := .seq he₁ he₂
    have ht : 6 + (3 + N * N) = N * N + 9 := by omega
    exact ht ▸ hh
  refine ⟨s₂, hex, rfl, ?_, ?_, ?_⟩
  · simp [s₂, s₁, N]
  · intro a ha
    exact State.setArr_arrs_ne _ _ ha
  · intro q hq
    exact State.setReg_regs_ne _ _ hq

end GraphMinor.Compute
