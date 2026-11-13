module

public import GraphMinor.Compute.GM06Alg34VertexReachRead
public import GraphMinor.Compute.GM06Alg34Stream

/-!
# Testing that a block stays in one component

Read the counted labels and conjoin their computed reachability marks.
Starting from a block label, this scan tests whether all its other
labels belong to the same component, as needed in VI (3.3)(iii).
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Consume the labels counted in 108, conjoining their reachability in 112. -/
def gm06ReachedListProg : Cmd :=
  .while (.reg 108) (.seq (readStreamWordProg 0 103 109)
    (.seq (.assign 112 (exprAnd (.reg 112) (Expr.read 33 (.reg 109))))
      (.assign 108 (.op .sub (.reg 108) (.const 1)))))

/-- The counted stream scan tests exactly that all supplied labels are
inside the searched component, in linear time and without array changes. -/
theorem gm06ReachedListProg_exec {w off : ℕ} (x : GM06DrawingData) (a : Fin x.n)
    (L : List (Fin x.n)) (tail : List ℕ) (flag : Bool)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hend : off + L.length < 2 ^ w)
    {s : State} (hmarks : s.arrs 33 = gm06VertexReachData x a)
    (hs : AtStream 0 off (L.map Fin.val ++ tail) s)
    (hp : s.regs 103 = off) (hcount : s.regs 108 = L.length)
    (hflag : s.regs 112 = if flag then 1 else 0) :
    ∃ s' t, Exec w gm06ReachedListProg s s' t ∧ t ≤ 22 * L.length + 1 ∧
      s'.regs 112 = (if flag && L.all (fun b => decide (x.vertexGraph.Reachable a b)) then 1 else 0) ∧
      s'.regs 103 = off + L.length ∧ s'.regs 108 = 0 ∧
      AtStream 0 (off + L.length) tail s' ∧
      (∀ A : ℕ, s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 112 → s'.regs q = s.regs q) := by
  induction L generalizing off s flag with
  | nil =>
    have hc : (Expr.reg 108).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hcount, Nat.zero_lt_of_lt hw]
    refine ⟨s, 1, .while_false hc, by simp, ?_, by simpa using hp, hcount,
      by simpa using hs, fun _ => rfl, fun _ _ _ _ _ => rfl⟩
    simpa using hflag
  | cons b L ih =>
    have hcountw : L.length + 1 < 2 ^ w := by simp only [List.length_cons] at hend; omega
    have hrestw : L.length < 2 ^ w := by omega
    obtain ⟨s₁, t₁, hex₁, ht₁, hb₁, hp₁, hs₁, ha₁, hg₁⟩ :=
      readStreamWordProg_exec 103 109 (by decide) hw (by simp only [List.length_cons] at hend; omega)
        (b.isLt.trans hn) (by simpa only [List.map_cons, List.cons_append] using hs) hp
    have hflag₁ : s₁.regs 112 = if flag then 1 else 0 :=
      (hg₁ 112 (by decide) (by decide)).trans hflag
    have hmark₁ : s₁.arrs 33 = gm06VertexReachData x a := (ha₁ 33).trans hmarks
    have hfw : (if flag then 1 else 0) < 2 ^ w := by
      cases flag
      · exact Nat.zero_lt_of_lt hw
      · exact hw
    have hef : (Expr.reg 112).eval w s₁ = some (if flag then 1 else 0) := by
      simp [Expr.eval, checkWord, hflag₁, hfw]
    have heu := gm06VertexReachRead_eval x a b hw hn hmark₁ hb₁
    let flag' := flag && decide (x.vertexGraph.Reachable a b)
    have heval : (exprAnd (.reg 112) (Expr.read 33 (.reg 109))).eval w s₁ =
        some (if flag' then 1 else 0) := by
      simpa only [flag', Bool.and_eq_true, decide_eq_true_eq] using eval_exprAnd hw hef heu
    let s₂ := s₁.setReg 112 (if flag' then 1 else 0)
    have hex₂ : Exec w (.assign 112 (exprAnd (.reg 112) (Expr.read 33 (.reg 109)))) s₁ s₂ 5 := .assign heval
    have hc₂ : s₂.regs 108 = L.length + 1 := by
      simp only [s₂, State.setReg_regs_ne _ _ (by decide : 108 ≠ 112),
        hg₁ 108 (by decide) (by decide), hcount, List.length_cons]
    let s₃ := s₂.setReg 108 L.length
    have hex₃ : Exec w (.assign 108 (.op .sub (.reg 108) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₂, hcountw, hrestw, hw])
    obtain ⟨s₄, t₄, hex₄, ht₄, hans, hp₄, hz₄, hs₄, ha₄, hg₄⟩ :=
      ih (s := s₃) flag' (by simp only [List.length_cons] at hend; omega)
        hmark₁ (hs₁.of_arr_eq rfl) (by simpa [s₃, s₂] using hp₁) (by simp [s₃])
        (by simp [s₃, s₂])
    have hcond : (Expr.reg 108).eval w s = some (L.length + 1) := by
      simp [Expr.eval, checkWord, hcount, hcountw]
    have hoff : off + (b :: L).length = off + 1 + L.length := by simp; omega
    refine ⟨s₄, 1 + (t₁ + (5 + 4)) + t₄,
      .while_true hcond (Nat.succ_ne_zero _) (.seq hex₁ (.seq hex₂ hex₃)) hex₄,
      by simp only [List.length_cons]; omega, ?_, hp₄.trans hoff.symm, hz₄,
      hoff.symm ▸ hs₄, ?_, ?_⟩
    · rw [hans]
      simp only [flag', List.all_cons, Bool.and_assoc]
      rfl
    · intro A
      exact (ha₄ A).trans (ha₁ A)
    · intro q h103 h108 h109 h112
      rw [hg₄ q h103 h108 h109 h112]
      change (s₂.setReg 108 L.length).regs q = s.regs q
      rw [State.setReg_regs_ne _ _ h108, State.setReg_regs_ne _ _ h112]
      exact hg₁ q h103 h109

end GraphMinor.Compute
