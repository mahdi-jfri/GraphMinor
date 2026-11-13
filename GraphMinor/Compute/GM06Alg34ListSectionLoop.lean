module

public import GraphMinor.Compute.GM06Alg34AppendVertexList
public import GraphMinor.Compute.GM06Alg34ListSection

/-!
# Relabelling a counted section of vertex lists

Apply the verified length-prefixed list writer to every list in a
supplied section. The section keeps one list per old list, including
empty lists, as needed for the cuff section. The proof tracks both
stream cursors and bounds work by the original encoded section size.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Relabel the supplied lists counted in register 144 into output buffer 10. -/
def gm06ListSectionLoopProg : Cmd :=
  .while (.reg 144) (.seq gm06AppendVertexListProg
    (.assign 144 (.op .sub (.reg 144) (.const 1))))

/-- A counted section produces exactly its relabelled length-prefixed
lists in linear time in the supplied section size. -/
theorem gm06ListSectionLoopProg_exec {w off cap : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (Ls : List (List (Fin x.n))) (tail pfx : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hoff : off + (gm06VertexSectionWords Ls).length < 2 ^ w)
    (hout : pfx.length + (gm06VertexSectionWords Ls).length < 2 ^ w)
    {s : State} (hs : AtStream 0 off (gm06VertexSectionWords Ls ++ tail) s)
    (hp : s.regs 103 = off) (hc : s.regs 144 = Ls.length)
    (hmask : s.arrs 4 = gm06VertexMask vs) (hrank : s.arrs 5 = gm06VertexRanks vs)
    (hbuf : IsPrefixBuffer 10 pfx ((gm06RelabelSectionWords x vs Ls).length + cap) s)
    (hcursor : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06ListSectionLoopProg s s' t ∧
      t ≤ 60 * (gm06VertexSectionWords Ls).length + 1 ∧
      IsPrefixBuffer 10 (pfx ++ gm06RelabelSectionWords x vs Ls) cap s' ∧
      s'.regs 143 = (pfx ++ gm06RelabelSectionWords x vs Ls).length ∧
      s'.regs 103 = off + (gm06VertexSectionWords Ls).length ∧ s'.regs 144 = 0 ∧
      AtStream 0 (off + (gm06VertexSectionWords Ls).length) tail s' ∧
      (∀ a : ℕ, a ≠ 9 → a ≠ 10 → a ≠ 11 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < 150 → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 142 → q ≠ 143 →
        q ≠ 144 → s'.regs q = s.regs q) := by
  induction Ls generalizing off pfx s with
  | nil =>
    have he : (Expr.reg 144).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hc, Nat.zero_lt_of_lt hw]
    refine ⟨s, 1, .while_false he, by simp [gm06VertexSectionWords], ?_, ?_, ?_, hc, ?_,
      fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩
    · simpa [gm06RelabelSectionWords] using hbuf
    · simpa [gm06RelabelSectionWords] using hcursor
    · simpa [gm06VertexSectionWords] using hp
    · simpa [gm06VertexSectionWords] using hs
  | cons L Ls ih =>
    let head := GM06DrawingData.listWords (gm06RelabelVertexWords x vs L)
    let rest := gm06RelabelSectionWords x vs Ls
    have hnew : gm06RelabelSectionWords x vs (L :: Ls) = head ++ rest := rfl
    have hhead : head.length = 1 + (x.relabelVertexList vs L).length := by
      simp [head, GM06DrawingData.listWords, gm06RelabelVertexWords_eq, Nat.add_comm]
    have hheadle : head.length ≤ 1 + L.length := by
      have hh := gm06RelabelVertexWords_length_le x vs L
      simp only [head, GM06DrawingData.listWords, List.length_cons]
      omega
    have hold := gm06VertexSectionWords_cons L Ls
    have hcnt := gm06VertexSectionWords_count_le Ls
    have hLw : Ls.length < 2 ^ w := by omega
    have hL1w : Ls.length + 1 < 2 ^ w := by omega
    have hbufhead : IsPrefixBuffer 10 pfx
        (1 + (x.relabelVertexList vs L).length + (rest.length + cap)) s := by
      convert hbuf using 1
      rw [hnew, List.length_append, hhead]
      omega
    have hshead : AtStream 0 off
        (GM06DrawingData.listWords (L.map Fin.val) ++ (gm06VertexSectionWords Ls ++ tail)) s := by
      simpa only [gm06VertexSectionWords, List.flatMap_cons, List.append_assoc] using hs
    obtain ⟨s₁, t₁, he₁, ht₁, hbuf₁, hpout₁, hp₁, hs₁, ha₁, hr₁⟩ :=
      gm06AppendVertexListProg_exec x vs L (gm06VertexSectionWords Ls ++ tail) pfx hw hn
        (by omega) (by omega) hshead hp hmask hrank hbufhead hcursor
    have hc₁ : s₁.regs 144 = Ls.length + 1 := by
      simpa only [List.length_cons] using
        (hr₁ 144 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc
    let s₂ := s₁.setReg 144 Ls.length
    have he₂ : Exec w (.assign 144 (.op .sub (.reg 144) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₁, hL1w, hLw, hw])
    have hbuf₂ : IsPrefixBuffer 10 (pfx ++ head) (rest.length + cap) s₂ := by
      simpa only [← gm06RelabelVertexWords_eq] using hbuf₁.of_arr_eq (s' := s₂) rfl
    have hout₂ : s₂.regs 143 = (pfx ++ head).length := by
      rw [State.setReg_regs_ne _ _ (by decide : 143 ≠ 144)]
      simpa only [← gm06RelabelVertexWords_eq] using hpout₁
    have hp₂ : s₂.regs 103 = off + 1 + L.length := by simp [s₂, hp₁]
    obtain ⟨s₃, t₃, he₃, ht₃, hbuf₃, hout₃, hp₃, hc₃, hs₃, ha₃, hr₃⟩ :=
      ih (off := off + 1 + L.length) (pfx := pfx ++ head) (s := s₂)
        (by omega) (by simp only [List.length_append]; omega)
        (hs₁.of_arr_eq rfl) hp₂ (by simp [s₂])
        ((ha₁ 4 (by decide) (by decide) (by decide)).trans hmask)
        ((ha₁ 5 (by decide) (by decide) (by decide)).trans hrank) hbuf₂ hout₂
    have hecond : (Expr.reg 144).eval w s = some (Ls.length + 1) := by
      simp [Expr.eval, checkWord, hc, hL1w]
    have hex : Exec w gm06ListSectionLoopProg s s₃ (1 + (t₁ + 4) + t₃) :=
      .while_true hecond (by omega) (.seq he₁ he₂) he₃
    refine ⟨s₃, _, hex, by omega, ?_, ?_, ?_, hc₃, ?_, ?_, ?_⟩
    · simpa only [hnew, List.append_assoc] using hbuf₃
    · simpa only [hnew, List.append_assoc] using hout₃
    · omega
    · convert hs₃ using 1 <;> omega
    · intro a ha9 ha10 ha11
      exact (ha₃ a ha9 ha10 ha11).trans (ha₁ a ha9 ha10 ha11)
    · intro q hq hqp hqi hqv hqc hqo hqn
      rw [hr₃ q hq hqp hqi hqv hqc hqo hqn]
      change (s₁.setReg 144 Ls.length).regs q = _
      rw [State.setReg_regs_ne _ _ hqn]
      exact hr₁ q hq hqp hqi hqv hqc hqo

end GraphMinor.Compute
