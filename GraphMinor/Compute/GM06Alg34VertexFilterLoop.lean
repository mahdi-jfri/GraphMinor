module

public import GraphMinor.Compute.GM06Alg34EmitVertex
public import GraphMinor.Compute.GM06Alg34VertexWordWrites
public import GraphMinor.Compute.GM06Alg34Stream

/-!
# Filtering a supplied vertex list on the RAM

Read the counted list from the input stream and emit each surviving
label. The proof follows the list, records its exact buffer updates,
and shows that the final output count is the old count plus the number
of retained labels. Input and rank tables are preserved.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Filter the vertex words counted in register 108 into buffer 9. -/
def gm06VertexFilterLoopProg : Cmd :=
  .while (.reg 108) (.seq (readStreamWordProg 0 103 109)
    (.seq gm06EmitVertexProg (.assign 108 (.op .sub (.reg 108) (.const 1)))))

/-- The counted vertex-list scan implements the exact finite filtering
updates and count in linear time, with arbitrary old buffer entries. -/
theorem gm06VertexFilterLoopProg_exec {w off k : ℕ} (x : GM06DrawingData)
    (vs L : List (Fin x.n)) (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hoff : off + L.length < 2 ^ w) (hk : k + L.length < 2 ^ w)
    {s : State} (hstream : AtStream 0 off (L.map Fin.val ++ tail) s)
    (hpos : s.regs 103 = off) (hin : s.regs 108 = L.length) (hout : s.regs 142 = k)
    (hmask : s.arrs 4 = gm06VertexMask vs) (hrank : s.arrs 5 = gm06VertexRanks vs)
    (hcap : k + L.length ≤ (s.arrs 9).length) :
    ∃ s' t, Exec w gm06VertexFilterLoopProg s s' t ∧ t ≤ 25 * L.length + 1 ∧
      s'.arrs 9 = gm06VertexWordWrites x vs L k (s.arrs 9) ∧
      s'.regs 142 = k + (gm06RelabelVertexWords x vs L).length ∧
      s'.regs 103 = off + L.length ∧ s'.regs 108 = 0 ∧
      AtStream 0 (off + L.length) tail s' ∧
      (∀ a : ℕ, a ≠ 9 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 142 → s'.regs q = s.regs q) := by
  induction L generalizing off k s with
  | nil =>
    have hc : (Expr.reg 108).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hin, Nat.zero_lt_of_lt hw]
    refine ⟨s, 1, .while_false hc, by simp, rfl, ?_, by simpa using hpos,
      hin, by simpa using hstream, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
    simpa [gm06RelabelVertexWords] using hout
  | cons v L ih =>
    have hL1w : L.length + 1 < 2 ^ w := by simp only [List.length_cons] at hk; omega
    have hLw : L.length < 2 ^ w := by omega
    have hk1w : k + 1 < 2 ^ w := by simp only [List.length_cons] at hk; omega
    obtain ⟨s₁, t₁, he₁, ht₁, hv₁, hp₁, hs₁, ha₁, hr₁⟩ :=
      readStreamWordProg_exec 103 109 (by decide) hw
        (by simp only [List.length_cons] at hoff; omega) (v.isLt.trans hn) hstream hpos
    have hout₁ : s₁.regs 142 = k := (hr₁ 142 (by decide) (by decide)).trans hout
    obtain ⟨s₂, t₂, he₂, ht₂, hbuf₂, hout₂, ha₂, hr₂⟩ :=
      gm06EmitVertexProg_exec x vs v hw hn hk1w hv₁ hout₁
        ((ha₁ 4).trans hmask) ((ha₁ 5).trans hrank)
        (by rw [ha₁ 9]; simp only [List.length_cons] at hcap; omega)
    let k' := k + (if v ∈ vs then 1 else 0)
    have hc₂ : s₂.regs 108 = L.length + 1 := by
      simpa only [List.length_cons] using
        (hr₂ 108 (by decide)).trans ((hr₁ 108 (by decide) (by decide)).trans hin)
    let s₃ := s₂.setReg 108 L.length
    have he₃ : Exec w (.assign 108 (.op .sub (.reg 108) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₂, hL1w, hLw, hw])
    have hp₃ : s₃.regs 103 = off + 1 := by
      rw [State.setReg_regs_ne _ _ (by decide : 103 ≠ 108), hr₂ 103 (by decide), hp₁]
    have hout₃ : s₃.regs 142 = k' := by
      exact (State.setReg_regs_ne _ _ (by decide : 142 ≠ 108)).trans hout₂
    have hs₃ : AtStream 0 (off + 1) (L.map Fin.val ++ tail) s₃ :=
      hs₁.of_arr_eq (ha₂ 0 (by decide))
    have hlen₂ : (s₂.arrs 9).length = (s.arrs 9).length := by
      rw [hbuf₂, ha₁ 9]
      split <;> simp only [List.length_set]
    have hcap₃ : k' + L.length ≤ (s₃.arrs 9).length := by
      change k' + L.length ≤ (s₂.arrs 9).length
      rw [hlen₂]
      simp only [List.length_cons] at hcap
      dsimp only [k']
      split <;> omega
    have hk' : k' + L.length < 2 ^ w := by
      simp only [List.length_cons] at hk
      dsimp only [k']
      split <;> omega
    obtain ⟨s₄, t₄, he₄, ht₄, hbuf₄, hout₄, hp₄, hin₄, hs₄, _, _⟩ :=
      ih (off := off + 1) (k := k') (s := s₃)
        (by simp only [List.length_cons] at hoff; omega) hk' hs₃ hp₃ (by simp [s₃]) hout₃
        ((ha₂ 4 (by decide)).trans ((ha₁ 4).trans hmask))
        ((ha₂ 5 (by decide)).trans ((ha₁ 5).trans hrank)) hcap₃
    have hc : (Expr.reg 108).eval w s = some (L.length + 1) := by
      simp [Expr.eval, checkWord, hin, hL1w]
    have hex : Exec w gm06VertexFilterLoopProg s s₄ (1 + (t₁ + (t₂ + 4)) + t₄) :=
      .while_true hc (by omega) (.seq he₁ (.seq he₂ he₃)) he₄
    refine ⟨s₄, _, hex, by simp only [List.length_cons]; omega, ?_, ?_, ?_, hin₄, ?_, ?_, ?_⟩
    · rw [hbuf₄]
      change gm06VertexWordWrites x vs L k' (s₂.arrs 9) = _
      rw [hbuf₂, ha₁ 9]
      rfl
    · rw [gm06RelabelVertexWords_cons]
      dsimp only [k'] at hout₄
      split <;> simp_all only [↓reduceIte, List.length_cons, Nat.add_zero] <;> omega
    · simp only [List.length_cons]
      omega
    · convert hs₄ using 1 <;> simp only [List.length_cons] <;> omega
    · intro a ha
      exact hex.arrs_eq_of_not_mem_writtenArrs (by
        simp [gm06VertexFilterLoopProg, gm06EmitVertexProg, readStreamWordProg, Cmd.writtenArrs, ha])
    · intro q hq hqi hqv hqo
      exact hex.regs_eq_of_not_mem_writtenRegs (by
        simp [gm06VertexFilterLoopProg, gm06EmitVertexProg, readStreamWordProg, Cmd.writtenRegs,
          hq, hqi, hqv, hqo])

end GraphMinor.Compute
