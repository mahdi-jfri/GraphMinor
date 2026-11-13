module

public import GraphMinor.Compute.GM06Alg34PayloadAlloc

/-!
# Writing the induced payload header

The three computed counts are copied to the reserved output buffer.
Only the output array and its cursor change, so every boundary and
label table remains available to the later serialization passes.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Append the new vertex, edge, and region counts in encoding order. -/
def gm06PayloadHeaderProg : Cmd :=
  .seq (appendWordProg 10 143 (.reg 131))
    (.seq (appendWordProg 10 143 (.reg 137)) (appendWordProg 10 143 (.reg 203)))

/-- The header writer copies the three supplied count registers exactly. -/
theorem gm06PayloadHeaderProg_exec {w cap n m r : ℕ} {s : State}
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (hm : m < 2 ^ w) (hr : r < 2 ^ w)
    (hbuf : IsPrefixBuffer 10 [] (3 + cap) s) (hpos : s.regs 143 = 0)
    (hvn : s.regs 131 = n) (hem : s.regs 137 = m) (hrr : s.regs 203 = r) :
    ∃ s' t, Exec w gm06PayloadHeaderProg s s' t ∧ t ≤ 21 ∧
      IsPrefixBuffer 10 [n, m, r] cap s' ∧ s'.regs 143 = 3 ∧
      (∀ a : ℕ, a ≠ 10 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 143 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hb₁, hp₁, ha₁, hg₁⟩ :=
    appendWordProg_exec (w := w) (pfx := []) (val := n) (cap := 2 + cap) 10 143 (.reg 131) (by omega) (by change 1 < 2 ^ w; omega)
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbuf)
      hpos (by simp [Expr.eval, checkWord, hvn, hn])
  obtain ⟨s₂, t₂, hex₂, ht₂, hb₂, hp₂, ha₂, hg₂⟩ :=
    appendWordProg_exec (w := w) (pfx := [n]) (val := m) (cap := 1 + cap) 10 143 (.reg 137) (by omega) (by change 2 < 2 ^ w; omega)
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb₁)
      hp₁ (by simp [Expr.eval, checkWord, hg₁ 137 (by decide), hem, hm])
  obtain ⟨s₃, t₃, hex₃, ht₃, hb₃, hp₃, ha₃, hg₃⟩ :=
    appendWordProg_exec (w := w) (pfx := [n, m]) (val := r) (cap := cap) 10 143 (.reg 203) (by omega) (by change 3 < 2 ^ w; omega)
      (by simpa [Nat.add_comm] using hb₂)
      hp₂ (by simp [Expr.eval, checkWord, hg₂ 203 (by decide), hg₁ 203 (by decide), hrr, hr])
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost] at ht₁ ht₂ ht₃
    omega
  · simpa using hb₃
  · simpa using hp₃
  · intro a ha
    exact (ha₃ a ha).trans ((ha₂ a ha).trans (ha₁ a ha))
  · intro q hq
    exact (hg₃ q hq).trans ((hg₂ q hq).trans (hg₁ q hq))

end GraphMinor.Compute
