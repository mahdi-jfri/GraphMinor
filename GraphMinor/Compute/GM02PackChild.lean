module

public import GraphMinor.Compute.GM02PackTerminatedArrays

/-!
# Packing a recursive child from its computed arrays

The rank scan supplies the child vertex count and the edge filter
supplies its edge count. Read the terminal-pair array length and divide
by two to obtain its index, then pack the three headers and both
endpoint arrays. No count is supplied as additional input data.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Derive the child headers from scan results and the pair array, then pack. -/
def gm02PackChildProg (edges pairs dst : Arr) : Cmd :=
  .seq (.assign 260 (.reg 312))
    (.seq (.assign 261 (.reg 22))
      (.seq (.assign 262 (.op .div (.len pairs) (.const 2)))
        (gm02PackTerminatedArraysProg edges pairs dst)))

/-- The packer writes the exact plain child input using only computed counts. -/
theorem gm02PackChildProg_exec {w n m k : ℕ} (edges pairs dst : Arr)
    (hed : edges ≠ dst) (hpd : pairs ≠ dst) (E P : List ℕ) (s : State)
    (he : s.arrs edges = E) (hp : s.arrs pairs = P) (hplen : P.length = 2 * k)
    (hn : s.regs 312 = n) (hm : s.regs 22 = m)
    (hlen : 3 + E.length + P.length < 2 ^ w)
    (hnw : n < 2 ^ w) (hmw : m < 2 ^ w)
    (hew : ∀ v ∈ E, v < 2 ^ w) (hpw : ∀ v ∈ P, v < 2 ^ w) :
    ∃ s' t, Exec w (gm02PackChildProg edges pairs dst) s s' t ∧
      t ≤ 58 + 16 * (E.length + P.length) ∧
      s'.arrs dst = [n, m] ++ E ++ [k] ++ P ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r < 260, s'.regs r = s.regs r) := by
  have hkw : k < 2 ^ w := by omega
  let s₁ := s.setReg 260 n
  have he₁ : Exec w (.assign 260 (.reg 312)) s s₁ 2 :=
    Exec.assign (by simp [Expr.eval, hn, checkWord_of_lt hnw])
  let s₂ := s₁.setReg 261 m
  have he₂ : Exec w (.assign 261 (.reg 22)) s₁ s₂ 2 := by
    apply Exec.assign
    simp [Expr.eval, s₁, hm, checkWord_of_lt hmw]
  let s₃ := s₂.setReg 262 k
  have he₃ : Exec w (.assign 262 (.op .div (.len pairs) (.const 2))) s₂ s₃ 4 := by
    apply Exec.assign
    simp [Expr.eval, BinOp.eval, BinOp.raw, s₂, s₁, hp, hplen,
      checkWord_of_lt (by omega : 2 < 2 ^ w),
      checkWord_of_lt (by omega : 2 * k < 2 ^ w), checkWord_of_lt hkw]
  obtain ⟨s', t, he₄, ht, hout, ha, hr⟩ := gm02PackTerminatedArraysProg_exec edges pairs dst
    hed hpd E P s₃ he hp (by simp [s₃, s₂, s₁]) (by simp [s₃, s₂])
    (by simp [s₃]) hlen hnw hmw hkw hew hpw
  refine ⟨s', 2 + (2 + (4 + t)), Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)),
    by omega, hout, ?_, ?_⟩
  · intro a had
    exact ha a had
  · intro r hrl
    dsimp only [Reg] at hrl
    rw [hr r hrl]
    simp only [s₃, s₂, s₁, State.setReg_regs_ne (r := 262) (r' := r) _ _ (by dsimp only [Reg]; omega),
      State.setReg_regs_ne (r := 261) (r' := r) _ _ (by dsimp only [Reg]; omega),
      State.setReg_regs_ne (r := 260) (r' := r) _ _ (by dsimp only [Reg]; omega)]

end GraphMinor.Compute
