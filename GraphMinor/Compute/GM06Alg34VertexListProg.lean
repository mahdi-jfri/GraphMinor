module

public import GraphMinor.Compute.GM06Alg34VertexFilterProg

/-!
# Exact output arrays for relabelled vertex lists

The filter reserves the old list's capacity and returns its live length.
Copy just that live prefix into an exact array. This supplies the
length-prefixed output writer with precisely the words to append,
without treating unused buffer entries as part of the new list.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Filter a supplied vertex list and copy its live words into exact array 11. -/
def gm06VertexListProg : Cmd :=
  .seq gm06VertexFilterProg (readSliceProg 9 (.const 0) 11 (.reg 142) 150)

/-- The exact-array list pass returns precisely the induced payload's
relabelled list, with a linear time bound and preserved input tables. -/
theorem gm06VertexListProg_exec {w off : ℕ} (x : GM06DrawingData)
    (vs L : List (Fin x.n)) (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hoff : off + 1 + L.length < 2 ^ w) {s : State}
    (hstream : AtStream 0 off (GM06DrawingData.listWords (L.map Fin.val) ++ tail) s)
    (hpos : s.regs 103 = off) (hmask : s.arrs 4 = gm06VertexMask vs)
    (hrank : s.arrs 5 = gm06VertexRanks vs) :
    ∃ s' t, Exec w gm06VertexListProg s s' t ∧ t ≤ 42 * L.length + 21 ∧
      s'.arrs 11 = (x.relabelVertexList vs L).map Fin.val ∧
      s'.regs 142 = (x.relabelVertexList vs L).length ∧
      s'.regs 103 = off + 1 + L.length ∧
      AtStream 0 (off + 1 + L.length) tail s' ∧
      (∀ a : ℕ, a ≠ 9 → a ≠ 11 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < 150 → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 142 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hpre₁, hc₁, _, hp₁, _, hs₁, ha₁, hr₁⟩ :=
    gm06VertexFilterProg_exec x vs L tail hw hn hoff hstream hpos hmask hrank
  let chunk := gm06RelabelVertexWords x vs L
  have hchunk : chunk = (x.relabelVertexList vs L).map Fin.val := gm06RelabelVertexWords_eq x vs L
  have hc : s₁.regs 142 = chunk.length := by simpa only [hchunk, List.length_map] using hc₁
  have hpre : (s₁.arrs 9).take chunk.length = chunk := by
    rw [hc] at hpre₁
    exact hpre₁.trans hchunk.symm
  have hsplit : s₁.arrs 9 = [] ++ chunk ++ (s₁.arrs 9).drop chunk.length := by
    simpa only [List.nil_append, hpre] using (List.take_append_drop chunk.length (s₁.arrs 9)).symm
  have hlen : chunk.length ≤ L.length := gm06RelabelVertexWords_length_le x vs L
  have hactive : (x.activeVertices vs).length ≤ x.n := by
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  have hwords : ∀ a ∈ chunk, a < 2 ^ w := by
    intro a ha
    exact ((gm06RelabelVertexWords_lt x vs L a ha).trans_le hactive).trans hn
  obtain ⟨s₂, t₂, he₂, ht₂, harr₂, ha₂, hr₂⟩ := readSliceProg_exec
    (n := chunk.length) (off := 0) 9 11 (.const 0) 142 150 (by decide) (by decide)
    [] chunk ((s₁.arrs 9).drop chunk.length) rfl rfl hwords hw (by omega)
    (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw]) hsplit hc
  have hex : Exec w gm06VertexListProg s s₂ (t₁ + t₂) := .seq he₁ he₂
  refine ⟨s₂, _, hex, ?_, harr₂.trans hchunk, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost_const] at ht₂
    omega
  · exact (hr₂ 142 (by decide)).trans hc₁
  · exact (hr₂ 103 (by decide)).trans hp₁
  · exact hs₁.of_arr_eq (ha₂ 0 (by decide))
  · intro a ha9 ha11
    exact (ha₂ a ha11).trans (ha₁ a ha9)
  · intro q hq hqp hqi hqv hqo
    exact (hr₂ q hq).trans (hr₁ q hqp hqi hqv hqo)

end GraphMinor.Compute
