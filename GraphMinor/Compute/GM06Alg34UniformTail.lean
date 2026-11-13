module

public import GraphMinor.Compute.GM06Alg34Stream
public import GraphMinor.Compute.Algorithm77Prog

/-!
# RAM test that a block's remaining labels equal its first label

The singleton search reads a block's first label into register 111.
This counted stream loop compares each remaining label with that first
label, accumulating the conjunction in register 112. It preserves all
arrays and costs linear time in the supplied number of remaining labels.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Consume the counted labels, keeping flag 112 true only when they
all equal the first label in register 111. -/
def gm06UniformTailProg : Cmd :=
  .while (.reg 108)
    (.seq (readStreamWordProg 0 103 109)
      (.seq (.assign 112 (exprAnd (.reg 112) (exprEq (.reg 109) (.reg 111))))
        (.assign 108 (.op .sub (.reg 108) (.const 1)))))

/-- The singleton tail loop compares exactly the supplied labels, with
at most `20 * length + 1` RAM steps and no array changes. -/
theorem gm06UniformTailProg_exec {w off : ℕ} (target : ℕ) (vs tail : List ℕ) (flag : Bool)
    (hw : 1 < 2 ^ w) (htarget : target < 2 ^ w)
    (hvalid : ∀ v ∈ vs, v < 2 ^ w) (hend : off + vs.length < 2 ^ w)
    {s : State} (hstream : AtStream 0 off (vs ++ tail) s)
    (hpos : s.regs 103 = off) (hcount : s.regs 108 = vs.length)
    (hfirst : s.regs 111 = target) (hflag : s.regs 112 = (if flag then 1 else 0)) :
    ∃ s' t, Exec w gm06UniformTailProg s s' t ∧ t ≤ 20 * vs.length + 1 ∧
      s'.regs 112 = (if flag && vs.all (fun v => v == target) then 1 else 0) ∧
      s'.regs 103 = off + vs.length ∧ s'.regs 108 = 0 ∧
      AtStream 0 (off + vs.length) tail s' ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 112 → s'.regs q = s.regs q) := by
  induction vs generalizing off s flag with
  | nil =>
    have h0 : 0 < 2 ^ w := by omega
    have hc : (Expr.reg 108).eval w s = some 0 := by
      simp [Expr.eval, hcount, checkWord, h0]
    refine ⟨s, 1, .while_false hc, by simp, ?_, ?_, hcount, ?_, fun _ => rfl,
      fun _ _ _ _ _ => rfl⟩
    · simpa using hflag
    · simpa using hpos
    · simpa using hstream
  | cons v vs ih =>
    have hvw := hvalid v List.mem_cons_self
    have hcountw : vs.length + 1 < 2 ^ w := by simp only [List.length_cons] at hend; omega
    have hrestw : vs.length < 2 ^ w := by omega
    obtain ⟨s₁, t₁, hex₁, ht₁, hv₁, hpos₁, hstream₁, harr₁, hreg₁⟩ :=
      readStreamWordProg_exec 103 109 (by decide) hw
        (by simp only [List.length_cons] at hend; omega) hvw hstream hpos
    have htarget₁ : s₁.regs 111 = target := (hreg₁ 111 (by decide) (by decide)).trans hfirst
    have hflag₁ : s₁.regs 112 = (if flag then 1 else 0) :=
      (hreg₁ 112 (by decide) (by decide)).trans hflag
    have hfw : (if flag then 1 else 0) < 2 ^ w := by cases flag <;> simp_all
    have heflag : (Expr.reg 112).eval w s₁ = some (if flag then 1 else 0) := by
      simp [Expr.eval, checkWord, hflag₁, hfw]
    have hev : (Expr.reg 109).eval w s₁ = some v := by simp [Expr.eval, checkWord, hv₁, hvw]
    have hefirst : (Expr.reg 111).eval w s₁ = some target := by
      simp [Expr.eval, checkWord, htarget₁, htarget]
    let flag' := flag && (v == target)
    have heval : (exprAnd (.reg 112) (exprEq (.reg 109) (.reg 111))).eval w s₁ =
        some (if flag' then 1 else 0) := by
      simpa only [flag', Bool.and_eq_true, beq_iff_eq] using
        eval_exprAnd hw heflag (eval_exprEq hw hev hefirst)
    let s₂ := s₁.setReg 112 (if flag' then 1 else 0)
    have hex₂ : Exec w (.assign 112 (exprAnd (.reg 112) (exprEq (.reg 109) (.reg 111)))) s₁ s₂ 6 :=
      .assign heval
    have hcount₂ : s₂.regs 108 = vs.length + 1 := by
      simp only [s₂, State.setReg_regs_ne _ _ (by decide : 108 ≠ 112),
        hreg₁ 108 (by decide) (by decide), hcount, List.length_cons]
    have hedec : (Expr.op .sub (.reg 108) (.const 1)).eval w s₂ = some vs.length := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcount₂, hcountw, hrestw, hw]
    let s₃ := s₂.setReg 108 vs.length
    have hex₃ : Exec w (.assign 108 (.op .sub (.reg 108) (.const 1))) s₂ s₃ 4 := .assign hedec
    have hpos₃ : s₃.regs 103 = off + 1 := by simpa [s₃, s₂] using hpos₁
    have hfirst₃ : s₃.regs 111 = target := by simpa [s₃, s₂] using htarget₁
    have hflag₃ : s₃.regs 112 = (if flag' then 1 else 0) := by simp [s₃, s₂]
    obtain ⟨s₄, t₄, hex₄, ht₄, hans, hpos₄, hzero₄, hstream₄, harr₄, hreg₄⟩ :=
      ih (s := s₃) flag' (fun a ha => hvalid a (List.mem_cons_of_mem v ha))
        (by simp only [List.length_cons] at hend; omega) (hstream₁.of_arr_eq rfl)
        hpos₃ (State.setReg_regs_self _ _ _) hfirst₃ hflag₃
    have hcond : (Expr.reg 108).eval w s = some (vs.length + 1) := by
      simp [Expr.eval, hcount, checkWord, hcountw]
    have hex : Exec w gm06UniformTailProg s s₄ (1 + (t₁ + (6 + 4)) + t₄) :=
      .while_true hcond (Nat.succ_ne_zero _) (.seq hex₁ (.seq hex₂ hex₃)) hex₄
    have hoff : off + (v :: vs).length = off + 1 + vs.length := by simp; omega
    refine ⟨s₄, _, hex, by simp only [List.length_cons]; omega, ?_,
      hpos₄.trans hoff.symm, hzero₄, hoff.symm ▸ hstream₄, ?_, ?_⟩
    · rw [hans]
      have heq : (flag' && vs.all (fun a => a == target)) =
          (flag && (v :: vs).all (fun a => a == target)) := by
        simp only [flag', List.all_cons, Bool.and_assoc]
      exact congrArg (fun b : Bool => if b then (1 : ℕ) else 0) heq
    · intro a
      exact (harr₄ a).trans (harr₁ a)
    · intro q hq103 hq108 hq109 hq112
      rw [hreg₄ q hq103 hq108 hq109 hq112]
      change (s₂.setReg 108 vs.length).regs q = s.regs q
      rw [State.setReg_regs_ne _ _ hq108, State.setReg_regs_ne _ _ hq112]
      exact hreg₁ q hq103 hq109

end GraphMinor.Compute
