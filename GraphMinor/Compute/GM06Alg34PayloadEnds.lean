module

public import GraphMinor.Compute.GM06Alg34PayloadHeader

/-!
# Copying the induced endpoint section

The preparation pass already writes the relabeled endpoints to array 8.
This pass reads that array's length and appends it after the header,
without a length prefix because the header gives the edge count.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Copy the prepared endpoint array to the payload buffer. -/
def gm06PayloadEndsProg : Cmd :=
  .seq (.assign 142 (.len 8)) (appendBufSliceProg 8 10 142 143 240)

/-- Every endpoint word is a vertex label of the encoded drawing. -/
theorem gm06EndpointWords_lt (x : GM06DrawingData) :
    ∀ v ∈ x.endpointWords, v < x.n := by
  intro v hv
  obtain ⟨e, _, he⟩ := List.mem_flatMap.mp hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact e.1.isLt
  · exact e.2.isLt

/-- Endpoint copying appends the exact prepared words in linear time,
preserving every array except the output and all registers below 240
except the length and output cursors. -/
theorem gm06PayloadEndsProg_exec (x : GM06DrawingData) {w cap : ℕ} {pfx : List ℕ}
    {s : State} (hw : 1 < 2 ^ w) (hn : x.n ≤ 2 ^ w)
    (hpfx : pfx.length + x.endpointWords.length < 2 ^ w)
    (hsrc : s.arrs 8 = x.endpointWords)
    (hbuf : IsPrefixBuffer 10 pfx (x.endpointWords.length + cap) s)
    (hpos : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06PayloadEndsProg s s' t ∧
      t ≤ 17 * x.endpointWords.length + 7 ∧
      IsPrefixBuffer 10 (pfx ++ x.endpointWords) cap s' ∧
      s'.regs 143 = (pfx ++ x.endpointWords).length ∧
      (∀ a : ℕ, a ≠ 10 → s'.arrs a = s.arrs a) ∧
      (∀ q < 240, q ≠ 142 → q ≠ 143 → s'.regs q = s.regs q) := by
  have hlen : x.endpointWords.length < 2 ^ w := by omega
  let s₁ := s.setReg 142 x.endpointWords.length
  have hex₁ : Exec w (.assign 142 (.len 8)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hsrc, hlen])
  obtain ⟨s₂, t₂, hex₂, ht₂, hb₂, hp₂, _, ha₂, hg₂⟩ :=
    appendBufSliceProg_exec 8 10 142 143 240 (by decide) (by decide) (by decide) (by decide)
      (fun v hv => (gm06EndpointWords_lt x v hv).trans_le hn) hw hpfx
      (s := s₁) hsrc hbuf (by simp [s₁])
      (by simp [s₁, State.setReg, hpos])
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hb₂, hp₂, ha₂, ?_⟩
  intro q hq hq142 hq143
  rw [hg₂ q hq hq143]
  simp [s₁, State.setReg, hq142]

end GraphMinor.Compute
