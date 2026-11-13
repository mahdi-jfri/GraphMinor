module

public import GraphMinor.Compute.GM06Alg34ComplementMatrixProg
public import GraphMinor.Compute.Algorithm81

/-!
# Computing adjacency lists for the complement graph

Build the complement matrix from the supplied closure and survival
tables, then use the verified matrix-to-list scan. The resulting CSR
lists describe exactly the finite graph used for region components.
The original drawing array, masks, and closure table remain intact.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute complement adjacency lists in arrays 30, 31, and 32. -/
def gm06ComplementAdjListProg : Cmd :=
  .seq gm06ComplementMatrixProg
    (.seq (.assign 4 (.reg 170)) (matToAdjListRegProg 4 28 30 31 32 5 6 7 8))

/-- The complete matrix-and-list construction computes the complement
CSR lists in quadratic time, preserving all arrays below 28. -/
theorem gm06ComplementAdjListProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    {s : State} (hmat : s.arrs 12 = gm06ClosureMatrixData x)
    (hc : s.regs 170 = x.cellCount) (hn : s.regs 100 = x.n)
    (hm : s.regs 101 = x.ends.length) (hv : s.arrs 4 = gm06VertexMask vs)
    (he : s.arrs 6 = gm06EdgeMask x vs) :
    ∃ s' t, Exec w gm06ComplementAdjListProg s s' t ∧
      t ≤ 149 * (x.cellCount * x.cellCount) + 24 * x.cellCount + 23 ∧
      IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s' ∧
      (s'.arrs 32).length = x.cellCount * x.cellCount ∧
      s'.regs 4 = x.cellCount ∧
      (∀ k : ℕ, k < 28 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, 100 ≤ q → q ≠ 180 → q ≠ 181 → q ≠ 182 → q ≠ 183 → q ≠ 184 → q ≠ 186 →
        s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, _, hmatrix, harr₁, hreg₁⟩ :=
    gm06ComplementMatrixProg_exec x vs hw hN hsquare hmat hc hn hm hv he
  have hc₁ : s₁.regs 170 = x.cellCount := (hreg₁ _ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans hc
  let s₂ := s₁.setReg 4 x.cellCount
  have hex₂ : Exec w (.assign 4 (.reg 170)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hc₁, hN])
  have hmatrix₂ : IsAdjMatrix (x.complementGraph vs) 28 s₂ :=
    IsAdjMatrix.of_arrs_eq hmatrix rfl
  obtain ⟨s₃, t₃, hex₃, ht₃, hlists, hlen, hreg₃, harr₃⟩ :=
    matToAdjListRegProg_exec (x.complementGraph vs) hw hsquare hmatrix₂ (by simp [s₂])
  refine ⟨s₃, t₁ + (2 + t₃), Exec.seq hex₁ (Exec.seq hex₂ hex₃),
    by omega, hlists, hlen, ?_, ?_, ?_⟩
  · exact (hreg₃ 4 (by decide)).trans (by simp [s₂])
  · intro k hk
    exact (harr₃ k (by omega)).trans (harr₁ k (by omega))
  · intro q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆
    have hnot : q ∉ (matToAdjListRegProg 4 28 30 31 32 5 6 7 8).writtenRegs := by
      simp only [matToAdjListRegProg, forUp, listAppend, Cmd.writtenRegs,
        Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, false_or, or_false]
      omega
    exact (hex₃.regs_eq_of_not_mem_writtenRegs hnot).trans
      ((show s₂.regs q = s₁.regs q by simp [s₂, show q ≠ 4 by omega]).trans
        (hreg₁ q hq₁ hq₂ hq₃ hq₄ hq₅ hq₆))

end GraphMinor.Compute
