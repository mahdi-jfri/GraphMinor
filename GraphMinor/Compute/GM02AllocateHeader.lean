module

public import GraphMinor.Compute.Basic

/-!
# Allocating an encoded child graph header

The recursive input builder first allocates the complete output and
writes its vertex and graph-edge counts. The remaining words stay zero
until the edge and terminal-pair suffixes are copied. This small routine
records the allocation cost and preserves every register.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Allocate the output length and write the two graph header words. -/
def gm02AllocateHeaderProg (dst : Arr) (r_len r_n r_m : Reg) : Cmd :=
  .seq (.alloc dst (.reg r_len))
    (.seq (.write dst (.const 0) (.reg r_n)) (.write dst (.const 1) (.reg r_m)))

/-- Header allocation writes exactly the two supplied counts followed by
zero words, changing no register or other array. -/
theorem gm02AllocateHeaderProg_exec {w extra n m : ℕ} (dst : Arr) (r_len r_n r_m : Reg)
    (s : State) (hl : s.regs r_len = 2 + extra) (hn : s.regs r_n = n)
    (hm : s.regs r_m = m) (hlen : 2 + extra < 2 ^ w) (hnw : n < 2 ^ w) (hmw : m < 2 ^ w) :
    ∃ s', Exec w (gm02AllocateHeaderProg dst r_len r_n r_m) s s' (extra + 9) ∧
      s'.arrs dst = [n, m] ++ List.replicate extra 0 ∧ s'.regs = s.regs ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) := by
  let s₁ := s.setArr dst (List.replicate (2 + extra) 0)
  have he₁ : Exec w (.alloc dst (.reg r_len)) s s₁ (1 + (2 + extra)) := by
    apply Exec.alloc
    simp [Expr.eval, hl, checkWord_of_lt hlen]
  let s₂ := s₁.writeArr dst 0 n
  have he₂ : Exec w (.write dst (.const 0) (.reg r_n)) s₁ s₂ 3 := by
    apply Exec.write
    · simp [Expr.eval, checkWord_of_lt (by omega : 0 < 2 ^ w)]
    · simp [Expr.eval, s₁, hn, checkWord_of_lt hnw]
    · simp only [s₁, State.setArr_arrs_self, List.length_replicate]
      omega
  let s₃ := s₂.writeArr dst 1 m
  have hr : List.replicate (2 + extra) 0 = 0 :: 0 :: List.replicate extra 0 := by
    rw [show 2 + extra = extra + 2 by omega]
    simp only [List.replicate_succ]
  have h₂ : s₂.arrs dst = n :: 0 :: List.replicate extra 0 := by
    simp [s₂, s₁, hr]
  have he₃ : Exec w (.write dst (.const 1) (.reg r_m)) s₂ s₃ 3 := by
    apply Exec.write
    · simp [Expr.eval, checkWord_of_lt (by omega : 1 < 2 ^ w)]
    · simp [Expr.eval, s₂, s₁, hm, checkWord_of_lt hmw]
    · simp [h₂]
  refine ⟨s₃, ?_, ?_, rfl, ?_⟩
  · have htime : 1 + (2 + extra) + (3 + 3) = extra + 9 := by omega
    simpa only [gm02AllocateHeaderProg, htime] using Exec.seq he₁ (Exec.seq he₂ he₃)
  · simp [s₃, h₂]
  · intro a ha
    simp [s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha, State.setArr_arrs_ne _ _ ha]

end GraphMinor.Compute
