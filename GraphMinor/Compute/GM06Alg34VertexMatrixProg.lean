module

public import GraphMinor.Compute.GM06Alg34VertexEdgesLoop
public import GraphMinor.Compute.GM06Alg34Header
public import GraphMinor.Compute.GM06Alg34Layout

/-!
# Computing the vertex adjacency matrix from the drawing array

Read the supplied counts, allocate a zero square matrix, and scan the
endpoint pairs from their fixed offset. Each non-loop edge marks two
entries. The result is exactly the finite vertex graph's adjacency
matrix, with quadratic initialization and a linear endpoint scan.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read the header and build the vertex graph matrix in array 28. -/
def gm06VertexMatrixProg : Cmd :=
  .seq gm06ReadHeaderProg (.seq (.alloc 28 (.op .mul (.reg 100) (.reg 100)))
    (.seq (.assign 103 (.const 3)) (.seq (.assign 260 (.reg 101)) gm06VertexEdgesLoopProg)))

/-- The matrix program uses only the supplied drawing array and computes
its exact vertex adjacency matrix with arbitrary scratch contents. -/
theorem gm06VertexMatrixProg_exec (x : GM06DrawingData) {c : ℕ} (hc : 2 ≤ c)
    {s : State} (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06VertexMatrixProg s s' t ∧
      t ≤ x.n * x.n + 38 * x.ends.length + 40 ∧
      s'.arrs 28 = gm06VertexMatrixData x ∧ IsAdjMatrix x.vertexGraph 28 s' ∧
      s'.regs 100 = x.n ∧ s'.regs 101 = x.ends.length ∧ s'.regs 102 = x.regions.length ∧
      s'.regs 103 = 3 + 2 * x.ends.length ∧
      (∀ a : ℕ, a ≠ 28 → s'.arrs a = s.arrs a) := by
  have hc1 : 1 ≤ c := by omega
  have hsize : x.size < 2 ^ wordSize c x.size := lt_two_pow_wordSize_of_le hc1 (Nat.le_succ _)
  have hlen := x.words_length_lt_wordSize hc1
  have hn := x.counts_le_size.1.trans_lt hsize
  have hm := x.counts_le_size.2.1.trans_lt hsize
  have hr := x.counts_le_size.2.2.trans_lt hsize
  have hw3 : 3 < 2 ^ wordSize c x.size := by have h := x.five_le_words_length; omega
  have hsquare := (Nat.mul_le_mul (x.counts_le_size.1.trans (by omega))
    (x.counts_le_size.1.trans (by omega))).trans_lt (sq_lt_two_pow_wordSize (n := x.size) hc)
  have hend := x.regionOffset_lt_length.trans hlen
  let tail := x.regionWords ++ (x.cuffWords ++ x.divisionWords)
  obtain ⟨s₁, t₁, hex₁, ht₁, hn₁, hm₁, hr₁, _, _, ha₁, _⟩ :=
    gm06ReadHeaderProg_exec x.endpointWords tail x.endpointWords_length hw3 hn hm hr
      (by rw [x.endpointWords_length]; exact hend)
      (by rw [hinput, x.words_layout]; simp only [tail, List.append_assoc])
  let s₂ := s₁.setArr 28 (List.replicate (x.n * x.n) 0)
  let s₃ := s₂.setReg 103 3
  let s₄ := s₃.setReg 260 x.ends.length
  have hex₂ : Exec (wordSize c x.size) (.alloc 28 (.op .mul (.reg 100) (.reg 100))) s₁ s₂
      (3 + x.n * x.n) := .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hn₁, hn, hsquare])
  have hex₃ : Exec (wordSize c x.size) (.assign 103 (.const 3)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw3])
  have hex₄ : Exec (wordSize c x.size) (.assign 260 (.reg 101)) s₃ s₄ 2 :=
    .assign (by simp [s₃, s₂, Expr.eval, checkWord, hm₁, hm])
  have hs₄ : AtStream 0 3 (x.endpointWords ++ tail) s₄ := by
    refine ⟨[x.n, x.ends.length, x.regions.length], rfl, ?_⟩
    change s₁.arrs 0 = _
    rw [ha₁ 0, hinput, x.words_layout]
    simp only [tail, List.append_assoc]
  obtain ⟨s₅, t₅, hex₅, ht₅, hmat, hpos, _, _, ha₅, hg₅⟩ :=
    gm06VertexEdgesLoopProg_exec x.ends tail (by omega) hn hsquare hend
      hs₄ (by simp [s₄, s₃, s₂, State.setReg])
      (by simpa [s₄, s₃, s₂] using hn₁) (by simp [s₄])
      (by simp [s₄, s₃, s₂])
  have hmat' : s₅.arrs 28 = gm06VertexMatrixData x := hmat
  refine ⟨s₅, t₁ + ((3 + x.n * x.n) + (2 + (2 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), by omega,
    hmat', ?_, ?_, ?_, ?_, hpos, ?_⟩
  · simpa only [IsAdjMatrix, hmat'] using gm06VertexMatrixData_isAdjMatrixList x
  · exact (hg₅ 100 (by decide) (by decide) (by decide) (by decide)).trans hn₁
  · exact (hg₅ 101 (by decide) (by decide) (by decide) (by decide)).trans hm₁
  · exact (hg₅ 102 (by decide) (by decide) (by decide) (by decide)).trans hr₁
  · intro a ha
    exact (ha₅ a ha).trans ((State.setArr_arrs_ne s₁ _ ha).trans (ha₁ a))

end GraphMinor.Compute
