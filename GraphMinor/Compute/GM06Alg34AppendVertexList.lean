module

public import GraphMinor.Compute.GM06Alg34VertexListProg

/-!
# Appending a relabelled list to the new payload stream

Filter the supplied length-prefixed vertex list into an exact array,
then append its new length and words to the reserved payload buffer.
The input cursor and output cursor advance by their respective list
lengths. This writes the same list format that the input decoder reads.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Append a filtered supplied list to output buffer 10, with output cursor 143. -/
def gm06AppendVertexListProg : Cmd :=
  .seq gm06VertexListProg (appendLengthPrefixedProg 11 10 142 143 160)

/-- Appending one supplied vertex list writes exactly the length-prefixed
relabelled list, with linear time and preserved input and rank tables. -/
theorem gm06AppendVertexListProg_exec {w off cap : ℕ} (x : GM06DrawingData)
    (vs L : List (Fin x.n)) (tail pfx : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hoff : off + 1 + L.length < 2 ^ w) (hout : pfx.length + 1 + L.length < 2 ^ w)
    {s : State} (hstream : AtStream 0 off (GM06DrawingData.listWords (L.map Fin.val) ++ tail) s)
    (hpos : s.regs 103 = off) (hmask : s.arrs 4 = gm06VertexMask vs)
    (hrank : s.arrs 5 = gm06VertexRanks vs)
    (hbuf : IsPrefixBuffer 10 pfx (1 + (x.relabelVertexList vs L).length + cap) s)
    (hcursor : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06AppendVertexListProg s s' t ∧ t ≤ 59 * L.length + 33 ∧
      IsPrefixBuffer 10 (pfx ++ GM06DrawingData.listWords ((x.relabelVertexList vs L).map Fin.val)) cap s' ∧
      s'.regs 143 = (pfx ++ GM06DrawingData.listWords ((x.relabelVertexList vs L).map Fin.val)).length ∧
      s'.regs 103 = off + 1 + L.length ∧ AtStream 0 (off + 1 + L.length) tail s' ∧
      (∀ a : ℕ, a ≠ 9 → a ≠ 10 → a ≠ 11 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < 150 → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 142 → q ≠ 143 →
        s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, harr₁, hc₁, hp₁, hs₁, ha₁, hr₁⟩ :=
    gm06VertexListProg_exec x vs L tail hw hn hoff hstream hpos hmask hrank
  let chunk := (x.relabelVertexList vs L).map Fin.val
  have hlen : chunk.length ≤ L.length := by
    simpa only [gm06RelabelVertexWords_eq] using gm06RelabelVertexWords_length_le x vs L
  have hwords : ∀ a ∈ chunk, a < 2 ^ w := by
    intro a ha
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
    have hactive : (x.activeVertices vs).length ≤ x.n :=
      (List.length_filter_le _ _).trans_eq List.length_finRange
    exact (v.isLt.trans_le hactive).trans hn
  have hbuf₁ : IsPrefixBuffer 10 pfx (1 + chunk.length + cap) s₁ := by
    simpa only [chunk, List.length_map] using hbuf.of_arr_eq (ha₁ 10 (by decide) (by decide))
  have hcursor₁ : s₁.regs 143 = pfx.length :=
    (hr₁ 143 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcursor
  have hcount₁ : s₁.regs 142 = chunk.length := by simpa only [chunk, List.length_map] using hc₁
  obtain ⟨s₂, t₂, he₂, ht₂, hbuf₂, hp₂, _, ha₂, hr₂⟩ :=
    appendLengthPrefixedProg_exec 11 10 142 143 160 (by decide) (by decide) (by decide)
      (by decide) hwords hw (by omega) harr₁ hbuf₁ hcount₁ hcursor₁
  have hex : Exec w gm06AppendVertexListProg s s₂ (t₁ + t₂) := .seq he₁ he₂
  refine ⟨s₂, _, hex, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hbuf₂
  · exact hp₂
  · exact (hr₂ 103 (by decide) (by decide)).trans hp₁
  · exact hs₁.of_arr_eq (ha₂ 0 (by decide))
  · intro a ha9 ha10 ha11
    exact (ha₂ a ha10).trans (ha₁ a ha9 ha11)
  · intro q hq hqp hqi hqv hqc hqo
    exact (hr₂ q (by omega) hqo).trans (hr₁ q hq hqp hqi hqv hqc)

end GraphMinor.Compute
