module

public import GraphMinor.Compute.GM06Alg34ListSectionLoop

/-!
# Writing a complete relabelled list section

Read the supplied number of lists, write that count to the output,
and relabel every length-prefixed list. Empty lists remain present,
so the count and cuff numbering are retained. The entire section has
a linear RAM time bound.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Relabel a section including its outer count, appending to buffer 10. -/
def gm06ListSectionProg : Cmd :=
  .seq (readStreamWordProg 0 103 144)
    (.seq (appendWordProg 10 143 (.reg 144)) gm06ListSectionLoopProg)

/-- The complete supplied list section produces its exact relabelled
section, including the unchanged outer count, in linear time. -/
theorem gm06ListSectionProg_exec {w off cap : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (Ls : List (List (Fin x.n))) (tail pfx : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hoff : off + 1 + (gm06VertexSectionWords Ls).length < 2 ^ w)
    (hout : pfx.length + 1 + (gm06VertexSectionWords Ls).length < 2 ^ w)
    {s : State} (hs : AtStream 0 off (Ls.length :: (gm06VertexSectionWords Ls ++ tail)) s)
    (hp : s.regs 103 = off) (hmask : s.arrs 4 = gm06VertexMask vs)
    (hrank : s.arrs 5 = gm06VertexRanks vs)
    (hbuf : IsPrefixBuffer 10 pfx (1 + (gm06RelabelSectionWords x vs Ls).length + cap) s)
    (hcursor : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06ListSectionProg s s' t ∧
      t ≤ 60 * (gm06VertexSectionWords Ls).length + 16 ∧
      IsPrefixBuffer 10 (pfx ++ (Ls.length :: gm06RelabelSectionWords x vs Ls)) cap s' ∧
      s'.regs 143 = (pfx ++ (Ls.length :: gm06RelabelSectionWords x vs Ls)).length ∧
      s'.regs 103 = off + 1 + (gm06VertexSectionWords Ls).length ∧
      AtStream 0 (off + 1 + (gm06VertexSectionWords Ls).length) tail s' ∧
      (∀ a : ℕ, a ≠ 9 → a ≠ 10 → a ≠ 11 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < 150 → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 142 → q ≠ 143 →
        q ≠ 144 → s'.regs q = s.regs q) := by
  have hcnt := gm06VertexSectionWords_count_le Ls
  have hcntw : Ls.length < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hc₁, hp₁, hs₁, ha₁, hr₁⟩ :=
    readStreamWordProg_exec 103 144 (by decide) hw (by omega) hcntw hs hp
  have hbuf₁ : IsPrefixBuffer 10 pfx (((gm06RelabelSectionWords x vs Ls).length + cap) + 1) s₁ := by
    have hh := hbuf.of_arr_eq (ha₁ 10)
    convert hh using 1 <;> omega
  have hcursor₁ : s₁.regs 143 = pfx.length :=
    (hr₁ 143 (by decide) (by decide)).trans hcursor
  obtain ⟨s₂, t₂, he₂, ht₂, hbuf₂, hcursor₂, ha₂, hr₂⟩ :=
    appendWordProg_exec (val := Ls.length) 10 143 (.reg 144) hw (by omega) hbuf₁ hcursor₁
      (by simp [Expr.eval, checkWord, hc₁, hcntw])
  have hs₂ : AtStream 0 (off + 1) (gm06VertexSectionWords Ls ++ tail) s₂ :=
    hs₁.of_arr_eq (ha₂ 0 (by decide))
  obtain ⟨s₃, t₃, he₃, ht₃, hbuf₃, hcursor₃, hp₃, _, hs₃, ha₃, hr₃⟩ :=
    gm06ListSectionLoopProg_exec x vs Ls tail (pfx ++ [Ls.length]) hw hn hoff
      (by simpa only [List.length_append, List.length_cons, List.length_nil] using hout)
      hs₂ ((hr₂ 103 (by decide)).trans hp₁) ((hr₂ 144 (by decide)).trans hc₁)
      ((ha₂ 4 (by decide)).trans ((ha₁ 4).trans hmask))
      ((ha₂ 5 (by decide)).trans ((ha₁ 5).trans hrank)) hbuf₂ hcursor₂
  have hex : Exec w gm06ListSectionProg s s₃ (t₁ + (t₂ + t₃)) :=
    .seq he₁ (.seq he₂ he₃)
  refine ⟨s₃, _, hex, ?_, ?_, ?_, hp₃, hs₃, ?_, ?_⟩
  · simp only [Expr.cost_reg] at ht₂
    omega
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hbuf₃
  · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hcursor₃
  · intro a ha9 ha10 ha11
    exact (ha₃ a ha9 ha10 ha11).trans ((ha₂ a ha10).trans (ha₁ a))
  · intro q hq hqp hqi hqv hqc hqo hqn
    exact (hr₃ q hq hqp hqi hqv hqc hqo hqn).trans
      ((hr₂ q hqo).trans (hr₁ q hqp hqn))

end GraphMinor.Compute
