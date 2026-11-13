module

public import GraphMinor.Compute.GM06Alg34Stream

/-!
# Initializing the division output section

Read the old number of blocks, save the output count-word position,
append a zero placeholder, and initialize the retained count to zero.
The following scan uses separate old and retained counters.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read the old block count and initialize the reserved output count word. -/
def gm06DivisionInitProg : Cmd :=
  .seq (readStreamWordProg 0 103 144)
    (.seq (.assign 146 (.reg 143))
      (.seq (appendWordProg 10 143 (.const 0)) (.assign 145 (.const 0))))

/-- Division-section initialization reserves its count word, records its
position, and initializes the retained count in at most nineteen steps. -/
theorem gm06DivisionInitProg_exec {w off cap oldCount : ℕ} (tail pfx : List ℕ)
    (hw : 1 < 2 ^ w) (hoff : off + 1 < 2 ^ w)
    (hout : pfx.length + 1 < 2 ^ w) (hcount : oldCount < 2 ^ w) {s : State}
    (hs : AtStream 0 off (oldCount :: tail) s) (hp : s.regs 103 = off)
    (hb : IsPrefixBuffer 10 pfx (cap + 1) s) (hcursor : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06DivisionInitProg s s' t ∧ t ≤ 19 ∧
      IsPrefixBuffer 10 (pfx ++ [0]) cap s' ∧ s'.regs 143 = (pfx ++ [0]).length ∧
      s'.regs 103 = off + 1 ∧ s'.regs 144 = oldCount ∧ s'.regs 145 = 0 ∧
      s'.regs 146 = pfx.length ∧ AtStream 0 (off + 1) tail s' ∧
      (∀ a : ℕ, a ≠ 10 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 143 → q ≠ 144 → q ≠ 145 → q ≠ 146 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hc₁, hp₁, hs₁, ha₁, hr₁⟩ :=
    readStreamWordProg_exec 103 144 (by decide) hw hoff hcount hs hp
  have hcursor₁ : s₁.regs 143 = pfx.length :=
    (hr₁ 143 (by decide) (by decide)).trans hcursor
  let s₂ := s₁.setReg 146 pfx.length
  have he₂ : Exec w (.assign 146 (.reg 143)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hcursor₁, show pfx.length < 2 ^ w by omega])
  obtain ⟨s₃, t₃, he₃, ht₃, hb₃, hcursor₃, ha₃, hr₃⟩ :=
    appendWordProg_exec (val := 0) 10 143 (.const 0) hw hout
      (hb.of_arr_eq (s' := s₂) (ha₁ 10)) (by simp [s₂, hcursor₁])
      (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  let s₄ := s₃.setReg 145 0
  have he₄ : Exec w (.assign 145 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hex : Exec w gm06DivisionInitProg s s₄ (t₁ + (2 + (t₃ + 2))) :=
    .seq he₁ (.seq he₂ (.seq he₃ he₄))
  refine ⟨s₄, _, hex, ?_, hb₃.of_arr_eq rfl, ?_, ?_, ?_, by simp [s₄], ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost_const] at ht₃
    omega
  · exact (State.setReg_regs_ne _ _ (by decide : 143 ≠ 145)).trans hcursor₃
  · simp only [s₄, State.setReg_regs_ne _ _ (by decide : 103 ≠ 145)]
    rw [hr₃ 103 (by decide)]
    simpa [s₂] using hp₁
  · simp only [s₄, State.setReg_regs_ne _ _ (by decide : 144 ≠ 145)]
    rw [hr₃ 144 (by decide)]
    simpa [s₂] using hc₁
  · simp only [s₄, State.setReg_regs_ne _ _ (by decide : 146 ≠ 145)]
    rw [hr₃ 146 (by decide)]
    simp [s₂]
  · exact hs₁.of_arr_eq (ha₃ 0 (by decide))
  · intro a ha
    exact (ha₃ a ha).trans (ha₁ a)
  · intro q hqp hqo hqc hqr hqs
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [gm06DivisionInitProg, readStreamWordProg, appendWordProg, Cmd.writtenRegs,
        hqp, hqo, hqc, hqr, hqs])

end GraphMinor.Compute
