module

public import GraphMinor.Compute.GM06Alg34VertexFilterLoop

/-!
# Filtering and renumbering one length-prefixed vertex list

Read the supplied list length, reserve that much output space, and run
the counted filter. Buffer 9's live prefix is exactly the induced
payload's relabelled list, and register 142 gives its length. This pass
is shared by cuff, division, and boundary-list construction.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read a length-prefixed vertex list and build its relabelled live buffer. -/
def gm06VertexFilterProg : Cmd :=
  .seq (readStreamWordProg 0 103 108)
    (.seq (.alloc 9 (.reg 108))
      (.seq (.assign 142 (.const 0)) gm06VertexFilterLoopProg))

/-- One supplied list yields exactly the relabelled payload list in the
live output prefix, with linear work and no conditions on old scratch. -/
theorem gm06VertexFilterProg_exec {w off : ℕ} (x : GM06DrawingData)
    (vs L : List (Fin x.n)) (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hoff : off + 1 + L.length < 2 ^ w) {s : State}
    (hstream : AtStream 0 off (GM06DrawingData.listWords (L.map Fin.val) ++ tail) s)
    (hpos : s.regs 103 = off) (hmask : s.arrs 4 = gm06VertexMask vs)
    (hrank : s.arrs 5 = gm06VertexRanks vs) :
    ∃ s' t, Exec w gm06VertexFilterProg s s' t ∧ t ≤ 26 * L.length + 12 ∧
      (s'.arrs 9).take (s'.regs 142) = (x.relabelVertexList vs L).map Fin.val ∧
      s'.regs 142 = (x.relabelVertexList vs L).length ∧ (s'.arrs 9).length = L.length ∧
      s'.regs 103 = off + 1 + L.length ∧ s'.regs 108 = 0 ∧
      AtStream 0 (off + 1 + L.length) tail s' ∧
      (∀ a : ℕ, a ≠ 9 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 142 → s'.regs q = s.regs q) := by
  have hLw : L.length < 2 ^ w := by omega
  have hs : AtStream 0 off (L.length :: (L.map Fin.val ++ tail)) s := by
    simpa only [GM06DrawingData.listWords, List.length_map, List.cons_append] using hstream
  obtain ⟨s₁, t₁, he₁, ht₁, hlen₁, hp₁, hs₁, ha₁, hr₁⟩ :=
    readStreamWordProg_exec 103 108 (by decide) hw (by omega) hLw hs hpos
  let s₂ := s₁.setArr 9 (List.replicate L.length 0)
  have he₂ : Exec w (.alloc 9 (.reg 108)) s₁ s₂ (1 + L.length) :=
    .alloc (by simp [Expr.eval, checkWord, hlen₁, hLw])
  let s₃ := s₂.setReg 142 0
  have he₃ : Exec w (.assign 142 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hs₃ : AtStream 0 (off + 1) (L.map Fin.val ++ tail) s₃ :=
    hs₁.of_arr_eq (by simp [s₃, s₂])
  have hp₃ : s₃.regs 103 = off + 1 := by simp [s₃, s₂, hp₁]
  obtain ⟨s₄, t₄, he₄, ht₄, hbuf₄, hc₄, hp₄, hin₄, hs₄, _, _⟩ :=
    gm06VertexFilterLoopProg_exec (off := off + 1) (k := 0) (s := s₃) x vs L tail hw hn
      (by omega) (by omega) hs₃ hp₃ (by simp [s₃, s₂, hlen₁]) (by simp [s₃])
      (by simpa [s₃, s₂] using (ha₁ 4).trans hmask)
      (by simpa [s₃, s₂] using (ha₁ 5).trans hrank) (by simp [s₃, s₂])
  have hex : Exec w gm06VertexFilterProg s s₄ (t₁ + ((1 + L.length) + (2 + t₄))) :=
    .seq he₁ (.seq he₂ (.seq he₃ he₄))
  have hcount : s₄.regs 142 = (gm06RelabelVertexWords x vs L).length := by simpa using hc₄
  refine ⟨s₄, _, hex, by omega, ?_, ?_, ?_, hp₄, hin₄, hs₄, ?_, ?_⟩
  · rw [hcount, hbuf₄, gm06VertexWordWrites_take x vs L _ (by simp [s₃, s₂]),
      gm06RelabelVertexWords_eq]
  · simpa only [gm06RelabelVertexWords_eq, List.length_map] using hcount
  · rw [hbuf₄, gm06VertexWordWrites_length]
    simp [s₃, s₂]
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [gm06VertexFilterProg, gm06VertexFilterLoopProg, gm06EmitVertexProg,
        readStreamWordProg, Cmd.writtenArrs, ha])
  · intro q hq hqi hqv hqo
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [gm06VertexFilterProg, gm06VertexFilterLoopProg, gm06EmitVertexProg,
        readStreamWordProg, Cmd.writtenRegs, hq, hqi, hqv, hqo])

end GraphMinor.Compute
