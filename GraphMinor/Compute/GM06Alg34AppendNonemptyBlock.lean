module

public import GraphMinor.Compute.GM06Alg34Stream

/-!
# Appending and counting a nonempty division block

The restricted block is already stored as an exact word array. Its
length decides whether to append the length-prefixed block and increase
the retained-block counter. Empty blocks leave both outputs unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The words emitted by one restricted division block. -/
def gm06NonemptyBlockWords (chunk : List ℕ) : List ℕ :=
  if chunk.isEmpty then [] else GM06DrawingData.listWords chunk

/-- Append a positive-length block and increment the retained count in register 145. -/
def gm06AppendNonemptyBlockProg : Cmd :=
  .ite (.reg 142)
    (.seq (appendLengthPrefixedProg 11 10 142 143 160)
      (.assign 145 (.op .add (.reg 145) (.const 1)))) .skip

/-- The nonempty-block branch appends exactly the required words and
updates the retained count, with linear work in the block length. -/
theorem gm06AppendNonemptyBlockProg_exec {w cap c : ℕ} (chunk pfx : List ℕ)
    (hw : 1 < 2 ^ w) (hc : c + 1 < 2 ^ w)
    (hout : pfx.length + 1 + chunk.length < 2 ^ w)
    (hwords : ∀ a ∈ chunk, a < 2 ^ w) {s : State}
    (hsrc : s.arrs 11 = chunk) (hlen : s.regs 142 = chunk.length)
    (hcount : s.regs 145 = c) (hcursor : s.regs 143 = pfx.length)
    (hbuf : IsPrefixBuffer 10 pfx ((gm06NonemptyBlockWords chunk).length + cap) s) :
    ∃ s' t, Exec w gm06AppendNonemptyBlockProg s s' t ∧ t ≤ 17 * chunk.length + 17 ∧
      IsPrefixBuffer 10 (pfx ++ gm06NonemptyBlockWords chunk) cap s' ∧
      s'.regs 143 = (pfx ++ gm06NonemptyBlockWords chunk).length ∧
      s'.regs 145 = c + (if chunk.isEmpty then 0 else 1) ∧
      (∀ a : ℕ, a ≠ 10 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < 160 → q ≠ 143 → q ≠ 145 → s'.regs q = s.regs q) := by
  cases chunk with
  | nil =>
    have hcond : (Expr.reg 142).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hlen, Nat.zero_lt_of_lt hw]
    refine ⟨s, 2, .ite_false hcond (.skip s), by decide, ?_, ?_, ?_,
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    · simpa [gm06NonemptyBlockWords] using hbuf
    · simpa [gm06NonemptyBlockWords] using hcursor
    · simpa using hcount
  | cons a chunk =>
    have hlenw : chunk.length + 1 < 2 ^ w := by simp only [List.length_cons] at hout; omega
    have hcw : c < 2 ^ w := by omega
    have hcond : (Expr.reg 142).eval w s = some (a :: chunk).length := by
      simp [Expr.eval, checkWord, hlen, hlenw]
    have hbuf' : IsPrefixBuffer 10 pfx (1 + (a :: chunk).length + cap) s := by
      simpa [gm06NonemptyBlockWords, GM06DrawingData.listWords, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hbuf
    obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hp₁, _, ha₁, hr₁⟩ :=
      appendLengthPrefixedProg_exec 11 10 142 143 160 (by decide) (by decide) (by decide)
        (by decide) hwords hw hout hsrc hbuf' hlen hcursor
    have hc₁ : s₁.regs 145 = c := (hr₁ 145 (by decide) (by decide)).trans hcount
    let s₂ := s₁.setReg 145 (c + 1)
    have he₂ : Exec w (.assign 145 (.op .add (.reg 145) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₁, hcw, hc, hw])
    have hex : Exec w gm06AppendNonemptyBlockProg s s₂ (1 + (t₁ + 4)) :=
      .ite_true hcond (by simp) (.seq he₁ he₂)
    refine ⟨s₂, _, hex, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [gm06NonemptyBlockWords, GM06DrawingData.listWords] using hb₁.of_arr_eq (s' := s₂) rfl
    · rw [State.setReg_regs_ne _ _ (by decide : 143 ≠ 145)]
      simpa [gm06NonemptyBlockWords, GM06DrawingData.listWords] using hp₁
    · simp [s₂]
    · exact ha₁
    · intro q hq hqp hqc
      rw [State.setReg_regs_ne _ _ hqc]
      exact hr₁ q hq hqp

end GraphMinor.Compute
