module

public import GraphMinor.Compute.GM06Alg34SplitStream

/-!
# Scanning every division block for a component split

Read each block, search from its first label, and conjoin the resulting
one-component flags. The induction follows the supplied record stream.
A weighted word count bounds the total search and scan work and includes
empty records. Every source graph and adjacency array is preserved.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test the blocks counted in 107, conjoining their answers into 263. -/
def gm06SplitLoopProg : Cmd :=
  .while (.reg 107) (.seq gm06ReadBlockTestProg
    (.seq (.assign 263 (exprAnd (.reg 263) (.reg 112)))
      (.assign 107 (.op .sub (.reg 107) (.const 1)))))

/-- The counted division scan computes exactly that no supplied block
meets two components, combined with the incoming conjunction flag. -/
theorem gm06SplitLoopProg_exec {w off : ℕ} (x : GM06DrawingData)
    (D : List (List (Fin x.n))) (tail : List ℕ) (flag : Bool)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hsquare : x.n * x.n < 2 ^ w)
    (hend : off + (gm06BlockStream D).length < 2 ^ w)
    {s : State} (hsize : s.regs 4 = x.n)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n)
    (hs : AtStream 0 off (gm06BlockStream D ++ tail) s)
    (hp : s.regs 103 = off) (hcount : s.regs 107 = D.length)
    (hflag : s.regs 263 = if flag then 1 else 0) :
    ∃ s' t, Exec w gm06SplitLoopProg s s' t ∧
      t ≤ (26 * (x.n * x.n) + 23 * x.n + 70) * (gm06BlockStream D).length + 1 ∧
      s'.regs 263 = (if flag && D.all (fun L => !x.isSplitBlock L) then 1 else 0) ∧
      s'.regs 103 = off + (gm06BlockStream D).length ∧ s'.regs 107 = 0 ∧
      AtStream 0 (off + (gm06BlockStream D).length) tail s' ∧
      (∀ A : ℕ, A ≠ 33 → A ≠ 34 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 190 ∨ 197 ≤ q) → q ≠ 103 → q ≠ 107 → q ≠ 108 → q ≠ 109 →
        q ≠ 112 → q ≠ 187 → q ≠ 263 → s'.regs q = s.regs q) := by
  induction D generalizing off s flag with
  | nil =>
    have hc : (Expr.reg 107).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hcount, Nat.zero_lt_of_lt hw]
    refine ⟨s, 1, .while_false hc, by simp [gm06BlockStream],
      by simpa using hflag, by simpa [gm06BlockStream] using hp, hcount,
      by simpa [gm06BlockStream] using hs, fun _ _ _ => rfl,
      fun _ _ _ _ _ _ _ _ _ => rfl⟩
  | cons L D ih =>
    have hrec := gm06BlockStream_cons_length L D
    have hcnt := gm06BlockStream_count_le D
    have hcw : D.length + 1 < 2 ^ w := by omega
    have hrw : D.length < 2 ^ w := by omega
    obtain ⟨s₁, t₁, hex₁, ht₁, hans₁, hp₁, hs₁, ha₁, hg₁⟩ :=
      gm06ReadBlockTestProg_exec x L (gm06BlockStream D ++ tail) hw hn hsquare
        (by omega) hsize hlists hlen
        (by simpa only [gm06BlockStream_cons, List.append_assoc] using hs) hp
    have hflag₁ : s₁.regs 263 = if flag then 1 else 0 :=
      (hg₁ 263 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hflag
    have hfw : (if flag then 1 else 0) < 2 ^ w := by cases flag <;> simp_all only [Bool.false_eq_true, ↓reduceIte]; omega
    have hbw : (if !x.isSplitBlock L then 1 else 0) < 2 ^ w := by
      cases x.isSplitBlock L <;> simp_all only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; omega
    have hef : (Expr.reg 263).eval w s₁ = some (if flag then 1 else 0) := by
      simp [Expr.eval, checkWord, hflag₁, hfw]
    have heb : (Expr.reg 112).eval w s₁ = some (if !x.isSplitBlock L then 1 else 0) := by
      change checkWord w (s₁.regs 112) = _
      rw [hans₁]
      simp only [checkWord, if_pos hbw]
    let flag' := flag && !x.isSplitBlock L
    have heval : (exprAnd (.reg 263) (.reg 112)).eval w s₁ = some (if flag' then 1 else 0) := by
      simpa only [flag', Bool.and_eq_true] using eval_exprAnd hw hef heb
    let s₂ := s₁.setReg 263 (if flag' then 1 else 0)
    have hex₂ : Exec w (.assign 263 (exprAnd (.reg 263) (.reg 112))) s₁ s₂ 4 := .assign heval
    have hc₂ : s₂.regs 107 = D.length + 1 := by
      rw [State.setReg_regs_ne _ _ (by decide : 107 ≠ 263),
        hg₁ 107 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hcount, List.length_cons]
    let s₃ := s₂.setReg 107 D.length
    have hex₃ : Exec w (.assign 107 (.op .sub (.reg 107) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₂, hcw, hrw, hw])
    have hsize₃ : s₃.regs 4 = x.n := by
      simp only [s₃, s₂, State.setReg_regs_ne _ _ (by decide : 4 ≠ 107),
        State.setReg_regs_ne _ _ (by decide : 4 ≠ 263),
        hg₁ 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsize]
    have hadj₃ : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s₃ :=
      hlists.of_arrs_eq (ha₁ 30 (by decide) (by decide))
        (ha₁ 31 (by decide) (by decide)) (ha₁ 32 (by decide) (by decide))
    obtain ⟨s₄, t₄, hex₄, ht₄, hans₄, hp₄, hz₄, hs₄, ha₄, hg₄⟩ :=
      ih flag' (by omega) hsize₃ hadj₃
        (by simpa only [s₃, s₂, State.setReg_arrs, ha₁ 32 (by decide) (by decide)] using hlen)
        (hs₁.of_arr_eq rfl) (by simpa [s₃, s₂] using hp₁)
        (by simp [s₃]) (by simp [s₃, s₂])
    have hc : (Expr.reg 107).eval w s = some (D.length + 1) := by
      simp [Expr.eval, checkWord, hcount, hcw]
    have hex : Exec w gm06SplitLoopProg s s₄ (1 + (t₁ + (4 + 4)) + t₄) :=
      .while_true hc (Nat.succ_ne_zero _) (.seq hex₁ (.seq hex₂ hex₃)) hex₄
    have hbudget : 26 * (x.n * x.n) + 23 * x.n + 22 * L.length + 63 ≤
        (26 * (x.n * x.n) + 23 * x.n + 70) * (1 + L.length) := by
      rw [Nat.mul_add, Nat.mul_one]
      have hm := Nat.mul_le_mul_right L.length (show 22 ≤ 26 * (x.n * x.n) + 23 * x.n + 70 by omega)
      omega
    have hoff : off + (gm06BlockStream (L :: D)).length =
        off + 1 + L.length + (gm06BlockStream D).length := by rw [hrec]; omega
    refine ⟨s₄, _, hex, ?_, ?_, hp₄.trans hoff.symm, hz₄, hoff.symm ▸ hs₄, ?_, ?_⟩
    · rw [hrec, ← Nat.add_assoc, Nat.mul_add]
      omega
    · rw [hans₄]
      simp only [flag', List.all_cons, Bool.and_assoc]
      rfl
    · intro A h33 h34
      exact (ha₄ A h33 h34).trans (ha₁ A h33 h34)
    · intro q hq h103 h107 h108 h109 h112 h187 h263
      rw [hg₄ q hq h103 h107 h108 h109 h112 h187 h263]
      change (s₂.setReg 107 D.length).regs q = s.regs q
      rw [State.setReg_regs_ne _ _ h107, State.setReg_regs_ne _ _ h263]
      exact hg₁ q hq h103 h108 h109 h112 h187

end GraphMinor.Compute
