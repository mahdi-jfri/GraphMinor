module

public import GraphMinor.Compute.GM06Alg34VertexListProg
public import GraphMinor.Compute.GM06Alg34AppendNonemptyBlock

/-!
# Restricting and emitting one supplied division block

Filter the supplied block, renumber its surviving vertices, and append
it only if its new length is positive. The retained-block counter is
updated by the same test. Every input block is consumed in full.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read and restrict a supplied division block, appending it only when nonempty. -/
def gm06DivisionBlockProg : Cmd := .seq gm06VertexListProg gm06AppendNonemptyBlockProg

/-- One supplied division block yields exactly its nonempty restricted
word encoding and retained-count contribution, with linear work. -/
theorem gm06DivisionBlockProg_exec {w off cap c : ℕ} (x : GM06DrawingData)
    (vs B : List (Fin x.n)) (tail pfx : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hc : c + 1 < 2 ^ w)
    (hoff : off + 1 + B.length < 2 ^ w) (hout : pfx.length + 1 + B.length < 2 ^ w)
    {s : State} (hs : AtStream 0 off (GM06DrawingData.listWords (B.map Fin.val) ++ tail) s)
    (hp : s.regs 103 = off) (hmask : s.arrs 4 = gm06VertexMask vs)
    (hrank : s.arrs 5 = gm06VertexRanks vs) (hcount : s.regs 145 = c)
    (hbuf : IsPrefixBuffer 10 pfx
      ((gm06NonemptyBlockWords (gm06RelabelVertexWords x vs B)).length + cap) s)
    (hcursor : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06DivisionBlockProg s s' t ∧ t ≤ 59 * B.length + 38 ∧
      IsPrefixBuffer 10 (pfx ++ gm06NonemptyBlockWords (gm06RelabelVertexWords x vs B)) cap s' ∧
      s'.regs 143 = (pfx ++ gm06NonemptyBlockWords (gm06RelabelVertexWords x vs B)).length ∧
      s'.regs 145 = c + (if (gm06RelabelVertexWords x vs B).isEmpty then 0 else 1) ∧
      s'.regs 103 = off + 1 + B.length ∧ AtStream 0 (off + 1 + B.length) tail s' ∧
      (∀ a : ℕ, a ≠ 9 → a ≠ 10 → a ≠ 11 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < 150 → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 142 → q ≠ 143 →
        q ≠ 145 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, harr₁, hlen₁, hp₁, hs₁, ha₁, hr₁⟩ :=
    gm06VertexListProg_exec x vs B tail hw hn hoff hs hp hmask hrank
  let chunk := gm06RelabelVertexWords x vs B
  have hchunk : chunk = (x.relabelVertexList vs B).map Fin.val := gm06RelabelVertexWords_eq x vs B
  have hlen : chunk.length ≤ B.length := gm06RelabelVertexWords_length_le x vs B
  have hwords : ∀ a ∈ chunk, a < 2 ^ w := by
    intro a ha
    have hactive : (x.activeVertices vs).length ≤ x.n :=
      (List.length_filter_le _ _).trans_eq List.length_finRange
    exact ((gm06RelabelVertexWords_lt x vs B a ha).trans_le hactive).trans hn
  have hsrc₁ : s₁.arrs 11 = chunk := harr₁.trans hchunk.symm
  have hlength₁ : s₁.regs 142 = chunk.length := by simpa only [hchunk, List.length_map] using hlen₁
  have hcount₁ : s₁.regs 145 = c :=
    (hr₁ 145 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcount
  have hcursor₁ : s₁.regs 143 = pfx.length :=
    (hr₁ 143 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcursor
  obtain ⟨s₂, t₂, he₂, ht₂, hbuf₂, ho₂, hc₂, ha₂, hr₂⟩ :=
    gm06AppendNonemptyBlockProg_exec chunk pfx hw hc (by omega) hwords hsrc₁ hlength₁
      hcount₁ hcursor₁ (hbuf.of_arr_eq (ha₁ 10 (by decide) (by decide)))
  have hex : Exec w gm06DivisionBlockProg s s₂ (t₁ + t₂) := .seq he₁ he₂
  refine ⟨s₂, _, hex, by omega, hbuf₂, ho₂, hc₂, ?_, ?_, ?_, ?_⟩
  · exact (hr₂ 103 (by decide) (by decide) (by decide)).trans hp₁
  · exact hs₁.of_arr_eq (ha₂ 0 (by decide))
  · intro a ha9 ha10 ha11
    exact (ha₂ a ha10).trans (ha₁ a ha9 ha11)
  · intro q hq hqp hqi hqv hcl hqo hqc
    exact (hr₂ q (by omega) hqo hqc).trans (hr₁ q hq hqp hqi hqv hcl)

end GraphMinor.Compute
