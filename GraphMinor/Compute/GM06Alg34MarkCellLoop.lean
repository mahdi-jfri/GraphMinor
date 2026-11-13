module

public import GraphMinor.Compute.GM06Alg34MarkCell
public import GraphMinor.Compute.GM06Alg34Stream

/-!
# Marking a supplied closure-incidence list

Read each counted vertex or edge label from the input stream and mark
its incidence in the current matrix row. The fixed kind offset lets
the same loop process either sort of boundary list. The proof records
the exact matrix writes and bounds work linearly in the supplied list.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Exact successive marks of the supplied labels at a fixed row and kind offset. -/
def gm06MarkCells (row shift : ℕ) : List ℕ → List ℕ → List ℕ
  | [], dst => dst
  | v :: L, dst => gm06MarkCells row shift L (dst.set (row + shift + v) 1)

/-- Mark the incidence labels counted in register 172 from the input cursor. -/
def gm06MarkCellLoopProg : Cmd :=
  .while (.reg 172) (.seq (readStreamWordProg 0 103 109)
    (.seq gm06MarkCellProg (.assign 172 (.op .sub (.reg 172) (.const 1)))))

/-- The incidence scan marks exactly the supplied labels in the fixed
row, with linear time and no changes to other arrays or row registers. -/
theorem gm06MarkCellLoopProg_exec {w off row shift : ℕ} (L tail : List ℕ)
    (hw : 1 < 2 ^ w) (hoff : off + L.length < 2 ^ w) {s : State}
    (hs : AtStream 0 off (L ++ tail) s) (hp : s.regs 103 = off)
    (hc : s.regs 172 = L.length) (hr : s.regs 173 = row) (hshift : s.regs 174 = shift)
    (hlen : (s.arrs 12).length < 2 ^ w)
    (hvalid : ∀ v ∈ L, row + shift + v < (s.arrs 12).length) :
    ∃ s' t, Exec w gm06MarkCellLoopProg s s' t ∧ t ≤ 20 * L.length + 1 ∧
      s'.arrs 12 = gm06MarkCells row shift L (s.arrs 12) ∧
      s'.regs 103 = off + L.length ∧ s'.regs 172 = 0 ∧
      AtStream 0 (off + L.length) tail s' ∧
      (∀ a : ℕ, a ≠ 12 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 109 → q ≠ 172 → s'.regs q = s.regs q) := by
  induction L generalizing off s with
  | nil =>
    have he : (Expr.reg 172).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hc, Nat.zero_lt_of_lt hw]
    exact ⟨s, 1, .while_false he, by simp, rfl, by simpa using hp,
      hc, by simpa using hs, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | cons v L ih =>
    have hvlen := hvalid v List.mem_cons_self
    have hvword : row + shift + v < 2 ^ w := hvlen.trans hlen
    have hvw : v < 2 ^ w := by omega
    have hLw : L.length < 2 ^ w := by simp only [List.length_cons] at hoff; omega
    have hL1w : L.length + 1 < 2 ^ w := by simp only [List.length_cons] at hoff; omega
    obtain ⟨s₁, t₁, he₁, ht₁, hv₁, hp₁, hs₁, ha₁, hr₁⟩ :=
      readStreamWordProg_exec 103 109 (by decide) hw
        (by simp only [List.length_cons] at hoff; omega) hvw hs hp
    obtain ⟨s₂, he₂, hbuf₂, ha₂, hr₂⟩ := gm06MarkCellProg_exec hw hvword
      ((hr₁ 173 (by decide) (by decide)).trans hr)
      ((hr₁ 174 (by decide) (by decide)).trans hshift) hv₁
      (by rw [ha₁ 12]; exact hvlen)
    have hc₂ : s₂.regs 172 = L.length + 1 := by
      simpa only [List.length_cons] using
        (hr₂ 172).trans ((hr₁ 172 (by decide) (by decide)).trans hc)
    let s₃ := s₂.setReg 172 L.length
    have he₃ : Exec w (.assign 172 (.op .sub (.reg 172) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₂, hL1w, hLw, hw])
    have hp₃ : s₃.regs 103 = off + 1 := by
      rw [State.setReg_regs_ne _ _ (by decide : 103 ≠ 172), hr₂ 103, hp₁]
    have hs₃ : AtStream 0 (off + 1) (L ++ tail) s₃ := hs₁.of_arr_eq (ha₂ 0 (by decide))
    have hrow₃ : s₃.regs 173 = row := by
      rw [State.setReg_regs_ne _ _ (by decide : 173 ≠ 172), hr₂ 173,
        hr₁ 173 (by decide) (by decide), hr]
    have hshift₃ : s₃.regs 174 = shift := by
      rw [State.setReg_regs_ne _ _ (by decide : 174 ≠ 172), hr₂ 174,
        hr₁ 174 (by decide) (by decide), hshift]
    have hlen₃ : (s₃.arrs 12).length = (s.arrs 12).length := by
      change (s₂.arrs 12).length = _
      rw [hbuf₂, List.length_set, ha₁ 12]
    obtain ⟨s₄, t₄, he₄, ht₄, hbuf₄, hp₄, hc₄, hs₄, _, _⟩ :=
      ih (off := off + 1) (s := s₃) (by simp only [List.length_cons] at hoff; omega)
        hs₃ hp₃ (by simp [s₃]) hrow₃ hshift₃ (hlen₃ ▸ hlen)
        (fun a ha => by rw [hlen₃]; exact hvalid a (List.mem_cons_of_mem _ ha))
    have hecond : (Expr.reg 172).eval w s = some (L.length + 1) := by
      simp [Expr.eval, checkWord, hc, hL1w]
    have hex : Exec w gm06MarkCellLoopProg s s₄ (1 + (t₁ + (7 + 4)) + t₄) :=
      .while_true hecond (by omega) (.seq he₁ (.seq he₂ he₃)) he₄
    refine ⟨s₄, _, hex, by simp only [List.length_cons]; omega, ?_, ?_, hc₄, ?_, ?_, ?_⟩
    · rw [hbuf₄]
      change gm06MarkCells row shift L (s₂.arrs 12) = _
      rw [hbuf₂, ha₁ 12]
      rfl
    · simp only [List.length_cons]
      omega
    · convert hs₄ using 1 <;> simp only [List.length_cons] <;> omega
    · intro a ha
      exact hex.arrs_eq_of_not_mem_writtenArrs (by
        simp [gm06MarkCellLoopProg, gm06MarkCellProg, readStreamWordProg, Cmd.writtenArrs, ha])
    · intro q hqp hqv hqc
      exact hex.regs_eq_of_not_mem_writtenRegs (by
        simp [gm06MarkCellLoopProg, gm06MarkCellProg, readStreamWordProg, Cmd.writtenRegs, hqp, hqv, hqc])

end GraphMinor.Compute
