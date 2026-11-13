module

public import GraphMinor.Compute.GM06Alg34VertexMatrixProg
public import GraphMinor.Compute.Algorithm81

/-!
# Computing vertex-graph adjacency lists

Build the endpoint adjacency matrix, read the supplied vertex count
into the list-builder register, and run the verified matrix-to-list
scan. The resulting lists support component searches while preserving
the original drawing array and its header counts.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Build vertex-component CSR lists in arrays 30, 31, and 32. -/
def gm06VertexAdjListProg : Cmd :=
  .seq gm06VertexMatrixProg
    (.seq (.assign 4 (.reg 100)) (matToAdjListRegProg 4 28 30 31 32 5 6 7 8))

/-- From the supplied drawing array alone, compute the exact adjacency
lists for vertex component searches, with a quadratic time bound. -/
theorem gm06VertexAdjListProg_exec (x : GM06DrawingData) {c : ℕ} (hc : 2 ≤ c)
    {s : State} (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06VertexAdjListProg s s' t ∧
      t ≤ 27 * (x.n * x.n) + 24 * x.n + 38 * x.ends.length + 54 ∧
      IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s' ∧
      (s'.arrs 32).length = x.n * x.n ∧ s'.regs 4 = x.n ∧
      s'.regs 100 = x.n ∧ s'.regs 101 = x.ends.length ∧ s'.regs 102 = x.regions.length ∧
      (∀ a : ℕ, a < 28 → s'.arrs a = s.arrs a) := by
  have hsize : x.size < 2 ^ wordSize c x.size :=
    lt_two_pow_wordSize_of_le (by omega) (Nat.le_succ _)
  have hn := x.counts_le_size.1.trans_lt hsize
  have hw : 1 < 2 ^ wordSize c x.size := by
    have h := x.five_le_words_length
    have hh := x.words_length_le_size
    omega
  have hsquare := (Nat.mul_le_mul (x.counts_le_size.1.trans (by omega))
    (x.counts_le_size.1.trans (by omega))).trans_lt (sq_lt_two_pow_wordSize (n := x.size) hc)
  obtain ⟨s₁, t₁, hex₁, ht₁, _, hmat₁, hn₁, hm₁, hr₁, _, ha₁⟩ :=
    gm06VertexMatrixProg_exec x hc hinput
  let s₂ := s₁.setReg 4 x.n
  have hex₂ : Exec (wordSize c x.size) (.assign 4 (.reg 100)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hn₁, hn])
  obtain ⟨s₃, t₃, hex₃, ht₃, hlists, hlen, hg₃, ha₃⟩ :=
    matToAdjListRegProg_exec x.vertexGraph (s₀ := s₂) hw hsquare hmat₁ (by simp [s₂])
  have hkeep : ∀ q : ℕ, 100 ≤ q → s₃.regs q = s₂.regs q := by
    intro q hq
    apply hex₃.regs_eq_of_not_mem_writtenRegs
    have hwr : (matToAdjListRegProg 4 28 30 31 32 5 6 7 8).writtenRegs = {5, 6, 7, 8} := by decide
    rw [hwr]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact not_or.mpr ⟨(Nat.ne_of_lt ((by decide : 5 < 100).trans_le hq)).symm,
      not_or.mpr ⟨(Nat.ne_of_lt ((by decide : 6 < 100).trans_le hq)).symm,
        not_or.mpr ⟨(Nat.ne_of_lt ((by decide : 7 < 100).trans_le hq)).symm,
          (Nat.ne_of_lt ((by decide : 8 < 100).trans_le hq)).symm⟩⟩⟩

  refine ⟨s₃, t₁ + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hlists, hlen,
    (hg₃ 4 (by decide)).trans (by simp [s₂]),
    (hkeep 100 (by decide)).trans hn₁, (hkeep 101 (by decide)).trans hm₁,
    (hkeep 102 (by decide)).trans hr₁, ?_⟩
  intro a ha
  exact (ha₃ a (by omega)).trans (ha₁ a (by omega))

end GraphMinor.Compute
