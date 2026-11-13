module

public import GraphMinor.Compute.GM02PackTerminated

/-!
# Computing packing lengths from the source arrays

The recursive input builder reads both endpoint-array lengths itself.
It adds the three header words to determine the allocation length and
then packs the input. The input relation therefore supplies no derived
buffer lengths or packing certificate.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute the two suffix lengths and allocation length before packing. -/
def gm02PackTerminatedArraysProg (edges pairs dst : Arr) : Cmd :=
  .seq (.assign 263 (.len edges))
    (.seq (.assign 264 (.len pairs))
      (.seq (.assign 265 (.op .add (.op .add (.const 3) (.reg 263)) (.reg 264)))
        (gm02PackTerminatedProg edges pairs dst)))

/-- Packing from arrays computes all allocation lengths and writes the
complete input in linear time. -/
theorem gm02PackTerminatedArraysProg_exec {w n m k : ℕ} (edges pairs dst : Arr)
    (hed : edges ≠ dst) (hpd : pairs ≠ dst) (E P : List ℕ) (s : State)
    (he : s.arrs edges = E) (hp : s.arrs pairs = P)
    (hn : s.regs 260 = n) (hm : s.regs 261 = m) (hk : s.regs 262 = k)
    (hlen : 3 + E.length + P.length < 2 ^ w)
    (hnw : n < 2 ^ w) (hmw : m < 2 ^ w) (hkw : k < 2 ^ w)
    (hew : ∀ v ∈ E, v < 2 ^ w) (hpw : ∀ v ∈ P, v < 2 ^ w) :
    ∃ s' t, Exec w (gm02PackTerminatedArraysProg edges pairs dst) s s' t ∧
      t ≤ 50 + 16 * (E.length + P.length) ∧
      s'.arrs dst = [n, m] ++ E ++ [k] ++ P ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r < 260, s'.regs r = s.regs r) := by
  let s₁ := s.setReg 263 E.length
  have hex₁ : Exec w (.assign 263 (.len edges)) s s₁ 2 := by
    apply Exec.assign
    simp [Expr.eval, he, checkWord_of_lt (by omega : E.length < 2 ^ w)]
  let s₂ := s₁.setReg 264 P.length
  have hex₂ : Exec w (.assign 264 (.len pairs)) s₁ s₂ 2 := by
    apply Exec.assign
    simp [Expr.eval, s₁, hp, checkWord_of_lt (by omega : P.length < 2 ^ w)]
  let s₃ := s₂.setReg 265 (3 + E.length + P.length)
  have hex₃ : Exec w (.assign 265 (.op .add (.op .add (.const 3) (.reg 263)) (.reg 264))) s₂ s₃ 6 := by
    apply Exec.assign
    simp [Expr.eval, BinOp.eval, BinOp.raw, s₂, s₁,
      checkWord_of_lt (by omega : 3 < 2 ^ w),
      checkWord_of_lt (by omega : E.length < 2 ^ w),
      checkWord_of_lt (by omega : P.length < 2 ^ w),
      checkWord_of_lt (by omega : 3 + E.length < 2 ^ w), checkWord_of_lt hlen]
  have hreg (r : Reg) (hr : r < 260) : s₃.regs r = s.regs r := by
    dsimp only [Reg] at hr
    simp [s₃, s₂, s₁, State.setReg_regs_ne (r := 265) (r' := r) _ _ (by dsimp only [Reg]; omega),
      State.setReg_regs_ne (r := 264) (r' := r) _ _ (by dsimp only [Reg]; omega),
      State.setReg_regs_ne (r := 263) (r' := r) _ _ (by dsimp only [Reg]; omega)]
  obtain ⟨s', t, hex, ht, hout, ha, hr⟩ := gm02PackTerminatedProg_exec edges pairs dst hed hpd E P s₃
    (by simpa [s₃, s₂, s₁] using he) (by simpa [s₃, s₂, s₁] using hp)
    (by simp [s₃, s₂, s₁, hn]) (by simp [s₃, s₂, s₁, hm]) (by simp [s₃, s₂, s₁, hk])
    (by simp [s₃, s₂, s₁]) (by simp [s₃, s₂]) (by simp [s₃]) hlen hnw hmw hkw hew hpw
  refine ⟨s', _, Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ hex)), by omega, hout, ?_, ?_⟩
  · intro a ha'
    exact ha a ha'
  · intro r hr'
    exact (hr r hr').trans (hreg r hr')

end GraphMinor.Compute
