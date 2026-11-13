module

public import GraphMinor.Compute.GM06Alg34UniformTail

/-!
# RAM singleton test for one counted block

An empty list is not a singleton. For a nonempty block, read its first
label and compare the rest with it using the verified stream loop.
The program consumes exactly the block, returns its first label when
present, and computes the singleton flag in linear time.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Whether a natural-number list is nonempty and has just one distinct label. -/
def gm06SingletonBlockFlag : List ℕ → Bool
  | [] => false
  | v :: vs => vs.all (fun a => a == v)

/-- Test a block whose length is in register 108 and labels start at
cursor 103. Return its singleton flag in 112 and its first label in 111. -/
def gm06SingletonBlockProg : Cmd :=
  .ite (.reg 108)
    (.seq (readStreamWordProg 0 103 111)
      (.seq (.assign 108 (.op .sub (.reg 108) (.const 1)))
        (.seq (.assign 112 (.const 1)) gm06UniformTailProg)))
    (.assign 112 (.const 0))

/-- The counted block test consumes precisely the supplied list, stores
its exact singleton flag, and uses at most `20 * length + 20` steps. -/
theorem gm06SingletonBlockProg_exec {w off : ℕ} (vs tail : List ℕ)
    (hw : 1 < 2 ^ w) (hvalid : ∀ v ∈ vs, v < 2 ^ w)
    (hend : off + vs.length < 2 ^ w) {s : State}
    (hstream : AtStream 0 off (vs ++ tail) s)
    (hpos : s.regs 103 = off) (hcount : s.regs 108 = vs.length) :
    ∃ s' t, Exec w gm06SingletonBlockProg s s' t ∧ t ≤ 20 * vs.length + 20 ∧
      s'.regs 112 = (if gm06SingletonBlockFlag vs then 1 else 0) ∧
      (∀ v rest, vs = v :: rest → s'.regs 111 = v) ∧
      s'.regs 103 = off + vs.length ∧ s'.regs 108 = 0 ∧
      AtStream 0 (off + vs.length) tail s' ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 111 → q ≠ 112 →
        s'.regs q = s.regs q) := by
  cases vs with
  | nil =>
    have h0 : 0 < 2 ^ w := by omega
    have hcond : (Expr.reg 108).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hcount, h0]
    let s' := s.setReg 112 0
    have hex : Exec w gm06SingletonBlockProg s s' 3 :=
      .ite_false hcond (.assign (by simp [Expr.eval, checkWord, h0]))
    refine ⟨s', 3, hex, by simp, by simp [s', gm06SingletonBlockFlag], ?_,
      ?_, ?_, ?_, fun _ => rfl, ?_⟩
    · intro v rest heq; cases heq
    · simpa [s'] using hpos
    · simpa [s'] using hcount
    · simpa using hstream.of_arr_eq (s' := s') rfl
    · intro q _ _ _ _ hq112
      exact State.setReg_regs_ne _ _ hq112
  | cons v vs =>
    have hv := hvalid v List.mem_cons_self
    have hcountw : vs.length + 1 < 2 ^ w := by simp only [List.length_cons] at hend; omega
    have hrestw : vs.length < 2 ^ w := by omega
    obtain ⟨s₁, t₁, hex₁, ht₁, hv₁, hpos₁, hstream₁, harr₁, hreg₁⟩ :=
      readStreamWordProg_exec 103 111 (by decide) hw
        (by simp only [List.length_cons] at hend; omega) hv hstream hpos
    have hcount₁ : s₁.regs 108 = vs.length + 1 := by
      simpa only [hreg₁ 108 (by decide) (by decide), List.length_cons] using hcount
    have hedec : (Expr.op .sub (.reg 108) (.const 1)).eval w s₁ = some vs.length := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcount₁, hcountw, hrestw, hw]
    let s₂ := s₁.setReg 108 vs.length
    have hex₂ : Exec w (.assign 108 (.op .sub (.reg 108) (.const 1))) s₁ s₂ 4 := .assign hedec
    let s₃ := s₂.setReg 112 1
    have hex₃ : Exec w (.assign 112 (.const 1)) s₂ s₃ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw])
    have hpos₃ : s₃.regs 103 = off + 1 := by simpa [s₃, s₂] using hpos₁
    have hfirst₃ : s₃.regs 111 = v := by simpa [s₃, s₂] using hv₁
    obtain ⟨s₄, t₄, hex₄, ht₄, hans, hpos₄, hzero₄, hstream₄, harr₄, hreg₄⟩ :=
      gm06UniformTailProg_exec v vs tail true (s := s₃) hw hv
        (fun a ha => hvalid a (List.mem_cons_of_mem v ha))
        (by simp only [List.length_cons] at hend; omega) (hstream₁.of_arr_eq rfl)
        hpos₃ (by simp [s₃, s₂]) hfirst₃ (by simp [s₃])
    have hcond : (Expr.reg 108).eval w s = some (vs.length + 1) := by
      simp [Expr.eval, checkWord, hcount, hcountw]
    have hex : Exec w gm06SingletonBlockProg s s₄ (1 + (t₁ + (4 + (2 + t₄)))) :=
      .ite_true hcond (Nat.succ_ne_zero _) (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)))
    have hoff : off + (v :: vs).length = off + 1 + vs.length := by simp; omega
    refine ⟨s₄, _, hex, by simp only [List.length_cons]; omega, ?_, ?_,
      hpos₄.trans hoff.symm, hzero₄, hoff.symm ▸ hstream₄, ?_, ?_⟩
    · change s₄.regs 112 = (if vs.all (fun a => a == v) then 1 else 0)
      rw [hans]
      exact congrArg (fun b : Bool => if b then (1 : ℕ) else 0) (Bool.true_and _)
    · intro a rest heq
      have ha : v = a := (List.cons.inj heq).1
      rw [hreg₄ 111 (by decide) (by decide) (by decide) (by decide), hfirst₃, ha]
    · intro a; exact (harr₄ a).trans (harr₁ a)
    · intro q hq103 hq108 hq109 hq111 hq112
      rw [hreg₄ q hq103 hq108 hq109 hq112]
      change (s₂.setReg 112 1).regs q = s.regs q
      rw [State.setReg_regs_ne _ _ hq112, State.setReg_regs_ne _ _ hq108]
      exact hreg₁ q hq103 hq111

end GraphMinor.Compute
