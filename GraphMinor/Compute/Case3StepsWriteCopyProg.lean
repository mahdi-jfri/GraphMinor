module

public import GraphMinor.Compute.Case3StepsParallelCopies
public import GraphMinor.Compute.Logic

/-!
# Writing one expanded parallel copy

The directed endpoints have already been mapped to original labels. One
iteration writes those two labels and the copy number in three consecutive
record slots. The surrounding records and all other arrays are retained.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Write the copy in register 110 after the edge prefix counted by 109. -/
def case3WriteCopyProg : Cmd :=
  .seq (.assign 116 (.op .mul (.const 3) (.op .add (.reg 109) (.reg 110))))
    (.seq (.write 50 (.reg 116) (.reg 106))
      (.seq (.write 50 (.op .add (.reg 116) (.const 1)) (.reg 107))
        (.write 50 (.op .add (.reg 116) (.const 2)) (.reg 110))))

/-- One expanded edge copy occupies exactly the next three slots and takes
nineteen steps. Only the record array and the position register change. -/
theorem case3WriteCopyProg_exec {w : ℕ} (pre suf : List ℕ) (u v q k : ℕ)
    (hpre : pre.length = 3 * (q + k)) (hw : 3 < 2 ^ w)
    (hlen : pre.length + 3 < 2 ^ w) (hu : u < 2 ^ w) (hv : v < 2 ^ w)
    {s : State} (hdst : s.arrs 50 = pre ++ [0, 0, 0] ++ suf)
    (hru : s.regs 106 = u) (hrv : s.regs 107 = v)
    (hrq : s.regs 109 = q) (hrk : s.regs 110 = k) :
    ∃ s', Exec w case3WriteCopyProg s s' 19 ∧
      s'.arrs 50 = pre ++ [u, v, k] ++ suf ∧
      (∀ a, a ≠ 50 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 116 → s'.regs r = s.regs r) := by
  have hq : q < 2 ^ w := by omega
  have hk : k < 2 ^ w := by omega
  have hqk : q + k < 2 ^ w := by omega
  have hp : pre.length < 2 ^ w := by omega
  have hp1 : pre.length + 1 < 2 ^ w := by omega
  have hp2 : pre.length + 2 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  let s₀ := s.setReg 116 pre.length
  let s₁ := s₀.writeArr 50 pre.length u
  let s₂ := s₁.writeArr 50 (pre.length + 1) v
  let s₃ := s₂.writeArr 50 (pre.length + 2) k
  have hex₀ : Exec w (.assign 116 (.op .mul (.const 3) (.op .add (.reg 109) (.reg 110)))) s s₀ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrq, hrk, hw, hq, hk, hqk, ← hpre, hp])
  have hrl (r : ℕ) (hr : r ≠ 116) : s₀.regs r = s.regs r := State.setReg_regs_ne _ _ hr
  have hex₁ : Exec w (.write 50 (.reg 116) (.reg 106)) s₀ s₁ 3 :=
    .write (by simp only [Expr.eval, checkWord, s₀, State.setReg_regs_self, hp, ↓reduceIte])
      (by simp only [Expr.eval, checkWord, hrl 106 (by decide), hru, hu, ↓reduceIte])
      (by simp only [s₀, State.setReg_arrs, hdst, List.length_append, List.length_cons, List.length_nil]; omega)
  have hex₂ : Exec w (.write 50 (.op .add (.reg 116) (.const 1)) (.reg 107)) s₁ s₂ 5 :=
    .write (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, s₀, hp, h1, hp1])
      (by simp only [Expr.eval, checkWord, s₁, State.writeArr_regs,
        hrl 107 (by decide), hrv, hv, ↓reduceIte])
      (by simp only [s₁, s₀, State.writeArr_arrs_self, State.setReg_arrs, List.length_set,
        hdst, List.length_append, List.length_cons, List.length_nil]; omega)
  have hex₃ : Exec w (.write 50 (.op .add (.reg 116) (.const 2)) (.reg 110)) s₂ s₃ 5 :=
    .write (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, s₀, hp, h2, hp2])
      (by simp only [Expr.eval, checkWord, s₂, s₁, State.writeArr_regs,
        hrl 110 (by decide), hrk, hk, ↓reduceIte])
      (by simp only [s₂, s₁, s₀, State.writeArr_arrs_self, State.setReg_arrs, List.length_set,
        hdst, List.length_append, List.length_cons, List.length_nil]; omega)
  have hex : Exec w case3WriteCopyProg s s₃ 19 := .seq hex₀ (.seq hex₁ (.seq hex₂ hex₃))
  refine ⟨s₃, hex, ?_, ?_, ?_⟩
  · simp only [s₃, s₂, s₁, s₀, State.writeArr_arrs_self, State.setReg_arrs, hdst]
    exact case3TripleBuffer_set pre suf u v k
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [case3WriteCopyProg, Cmd.writtenArrs, ha])
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by simp [case3WriteCopyProg, Cmd.writtenRegs, hr])

end GraphMinor.Compute
