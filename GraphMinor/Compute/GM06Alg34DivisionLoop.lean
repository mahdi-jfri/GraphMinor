module

public import GraphMinor.Compute.GM06Alg34DivisionBlockProg
public import GraphMinor.Compute.GM06Alg34DivisionSectionFacts

/-!
# The RAM scan of restricted division blocks

Read every old block and append its restriction only when nonempty.
Register 144 counts old blocks still to read, while register 145 counts
retained blocks. The proof follows the supplied section and identifies
both the output stream and the final retained count.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Restrict the old division blocks counted in register 144. -/
def gm06DivisionLoopProg : Cmd :=
  .while (.reg 144) (.seq gm06DivisionBlockProg
    (.assign 144 (.op .sub (.reg 144) (.const 1))))

/-- The division scan emits exactly the nonempty restricted blocks and
counts them, in linear time in the supplied encoded section length. -/
theorem gm06DivisionLoopProg_exec {w off cap c : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (D : List (List (Fin x.n))) (tail pfx : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hoff : off + (gm06VertexSectionWords D).length < 2 ^ w)
    (hout : pfx.length + (gm06VertexSectionWords D).length < 2 ^ w)
    (hcountw : c + D.length < 2 ^ w)
    {s : State} (hs : AtStream 0 off (gm06VertexSectionWords D ++ tail) s)
    (hp : s.regs 103 = off) (hc : s.regs 144 = D.length) (hret : s.regs 145 = c)
    (hmask : s.arrs 4 = gm06VertexMask vs) (hrank : s.arrs 5 = gm06VertexRanks vs)
    (hbuf : IsPrefixBuffer 10 pfx ((gm06DivisionSectionWords x vs D).length + cap) s)
    (hcursor : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06DivisionLoopProg s s' t ∧
      t ≤ 60 * (gm06VertexSectionWords D).length + 1 ∧
      IsPrefixBuffer 10 (pfx ++ gm06DivisionSectionWords x vs D) cap s' ∧
      s'.regs 143 = (pfx ++ gm06DivisionSectionWords x vs D).length ∧
      s'.regs 145 = c + (gm06DivisionWordLists x vs D).length ∧
      s'.regs 103 = off + (gm06VertexSectionWords D).length ∧ s'.regs 144 = 0 ∧
      AtStream 0 (off + (gm06VertexSectionWords D).length) tail s' ∧
      (∀ a : ℕ, a ≠ 9 → a ≠ 10 → a ≠ 11 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < 150 → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 142 → q ≠ 143 →
        q ≠ 144 → q ≠ 145 → s'.regs q = s.regs q) := by
  induction D generalizing off pfx c s with
  | nil =>
    have he : (Expr.reg 144).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hc, Nat.zero_lt_of_lt hw]
    refine ⟨s, 1, .while_false he, by simp [gm06VertexSectionWords], ?_, ?_, ?_, ?_, hc, ?_,
      fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩
    · simpa [gm06DivisionSectionWords, gm06DivisionWordLists] using hbuf
    · simpa [gm06DivisionSectionWords, gm06DivisionWordLists] using hcursor
    · simpa [gm06DivisionWordLists] using hret
    · simpa [gm06VertexSectionWords] using hp
    · simpa [gm06VertexSectionWords] using hs
  | cons B D ih =>
    let head := gm06NonemptyBlockWords (gm06RelabelVertexWords x vs B)
    let rest := gm06DivisionSectionWords x vs D
    let c' := c + (if (gm06RelabelVertexWords x vs B).isEmpty then 0 else 1)
    have hnew : gm06DivisionSectionWords x vs (B :: D) = head ++ rest :=
      gm06DivisionSectionWords_cons_append x vs B D
    have hheadle : head.length ≤ 1 + B.length := gm06NonemptyBlockWords_relabel_length_le x vs B
    have hold := gm06VertexSectionWords_cons B D
    have hcnt := gm06VertexSectionWords_count_le D
    have hDw : D.length < 2 ^ w := by omega
    have hD1w : D.length + 1 < 2 ^ w := by omega
    have hc1w : c + 1 < 2 ^ w := by simp only [List.length_cons] at hcountw; omega
    have hbufhead : IsPrefixBuffer 10 pfx (head.length + (rest.length + cap)) s := by
      convert hbuf using 1
      rw [hnew, List.length_append]
      omega
    have hshead : AtStream 0 off
        (GM06DrawingData.listWords (B.map Fin.val) ++ (gm06VertexSectionWords D ++ tail)) s := by
      simpa only [gm06VertexSectionWords, List.flatMap_cons, List.append_assoc] using hs
    obtain ⟨s₁, t₁, he₁, ht₁, hbuf₁, hpout₁, hret₁, hp₁, hs₁, ha₁, hr₁⟩ :=
      gm06DivisionBlockProg_exec x vs B (gm06VertexSectionWords D ++ tail) pfx hw hn hc1w
        (by omega) (by omega) hshead hp hmask hrank hret hbufhead hcursor
    have hc₁ : s₁.regs 144 = D.length + 1 := by
      simpa only [List.length_cons] using
        (hr₁ 144 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc
    let s₂ := s₁.setReg 144 D.length
    have he₂ : Exec w (.assign 144 (.op .sub (.reg 144) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₁, hD1w, hDw, hw])
    have hbuf₂ : IsPrefixBuffer 10 (pfx ++ head) (rest.length + cap) s₂ :=
      hbuf₁.of_arr_eq rfl
    have hout₂ : s₂.regs 143 = (pfx ++ head).length := by
      exact (State.setReg_regs_ne _ _ (by decide : 143 ≠ 144)).trans hpout₁
    have hret₂ : s₂.regs 145 = c' := by
      exact (State.setReg_regs_ne _ _ (by decide : 145 ≠ 144)).trans hret₁
    have hp₂ : s₂.regs 103 = off + 1 + B.length := by simp [s₂, hp₁]
    have hc'w : c' + D.length < 2 ^ w := by
      simp only [List.length_cons] at hcountw
      dsimp only [c']
      split <;> omega
    obtain ⟨s₃, t₃, he₃, ht₃, hbuf₃, hout₃, hret₃, hp₃, hc₃, hs₃, ha₃, hr₃⟩ :=
      ih (off := off + 1 + B.length) (pfx := pfx ++ head) (c := c') (s := s₂)
        (by omega) (by simp only [List.length_append]; omega) hc'w
        (hs₁.of_arr_eq rfl) hp₂ (by simp [s₂]) hret₂
        ((ha₁ 4 (by decide) (by decide) (by decide)).trans hmask)
        ((ha₁ 5 (by decide) (by decide) (by decide)).trans hrank) hbuf₂ hout₂
    have hecond : (Expr.reg 144).eval w s = some (D.length + 1) := by
      simp [Expr.eval, checkWord, hc, hD1w]
    have hex : Exec w gm06DivisionLoopProg s s₃ (1 + (t₁ + 4) + t₃) :=
      .while_true hecond (by omega) (.seq he₁ he₂) he₃
    refine ⟨s₃, _, hex, by omega, ?_, ?_, ?_, ?_, hc₃, ?_, ?_, ?_⟩
    · simpa only [hnew, List.append_assoc] using hbuf₃
    · simpa only [hnew, List.append_assoc] using hout₃
    · rw [gm06DivisionWordLists_length_cons]
      dsimp only [c'] at hret₃
      omega
    · omega
    · convert hs₃ using 1 <;> omega
    · intro a ha9 ha10 ha11
      exact (ha₃ a ha9 ha10 ha11).trans (ha₁ a ha9 ha10 ha11)
    · intro q hq hqp hqi hqv hqc hqo hqn hqr
      rw [hr₃ q hq hqp hqi hqv hqc hqo hqn hqr]
      change (s₁.setReg 144 D.length).regs q = _
      rw [State.setReg_regs_ne _ _ hqn]
      exact hr₁ q hq hqp hqi hqv hqc hqo hqr

end GraphMinor.Compute
