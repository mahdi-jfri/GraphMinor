module

public import GraphMinor.Compute.GM02TerminalPrefix
public import GraphMinor.Compute.MultiDigraph
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Writing the fixed terminal names for an active pattern edge

Compute the two names from the supplied pattern position and the saved
terminal offset. Append them to the terminal buffer and increment the
pair count. The original position and offset registers are preserved.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Append the terminal pair at pattern position 74, using the saved offset 73. -/
@[expose] def gm02AppendTerminalPairProg : Cmd :=
  .seq (.assign 60 (.op .add (.reg 73) (.op .mul (.const 2) (.reg 74))))
    (.seq (.assign 61 (.op .add (.reg 60) (.const 1)))
      (.seq (bufPush2 26 75 60 61) (.assign 76 (.op .add (.reg 76) (.const 1)))))

/-- Appending an active position writes exactly its two numeric terminal names in at most 28 steps. -/
theorem gm02AppendTerminalPairProg_exec {w K rem m : ℕ} (x : GM02TopologicalInput)
    (hK : x.edges.length ≤ K) (f : Fin x.edges.length) (pre : List ℕ) (s : State)
    (hbase : s.regs 73 = x.G.n + x.G.edges.length) (hf : s.regs 74 = f.val)
    (hbuf : s.arrs 26 = pre ++ List.replicate (rem + 2) 0)
    (hpos : s.regs 75 = pre.length) (hcount : s.regs 76 = m)
    (hw : 2 < 2 ^ w) (hN : gm02FullPortSize x K < 2 ^ w)
    (hposw : pre.length + 2 < 2 ^ w) (hcountw : m + 1 < 2 ^ w) :
    ∃ s' t, Exec w gm02AppendTerminalPairProg s s' t ∧ t ≤ 28 ∧
      s'.arrs 26 = (pre ++ [(gm02PatternTerminalPair x K hK f).1.val,
        (gm02PatternTerminalPair x K hK f).2.val]) ++ List.replicate rem 0 ∧
      s'.regs 75 = (pre ++ [(gm02PatternTerminalPair x K hK f).1.val,
        (gm02PatternTerminalPair x K hK f).2.val]).length ∧ s'.regs 76 = m + 1 ∧
      (∀ a, a ≠ 26 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 60 → r ≠ 61 → r ≠ 75 → r ≠ 76 → s'.regs r = s.regs r) := by
  let left := (gm02PatternTerminalPair x K hK f).1.val
  let right := (gm02PatternTerminalPair x K hK f).2.val
  have hlw : left < 2 ^ w := (gm02PatternTerminalPair x K hK f).1.isLt.trans hN
  have hrw : right < 2 ^ w := (gm02PatternTerminalPair x K hK f).2.isLt.trans hN
  have hleft : left = x.G.n + x.G.edges.length + 2 * f.val := gm02PatternTerminalPair_fst_val x K hK f
  have hright : right = left + 1 := by rw [hleft]; exact gm02PatternTerminalPair_snd_val x K hK f
  have hbword : x.G.n + x.G.edges.length < 2 ^ w := by omega
  have hfword : f.val < 2 ^ w := by omega
  have hmulword : 2 * f.val < 2 ^ w := by omega
  let s₀ := s.setReg 60 left
  have he₀ : Exec w (.assign 60 (.op .add (.reg 73) (.op .mul (.const 2) (.reg 74)))) s s₀ 6 := by
    dsimp only [s₀]
    rw [hleft]
    exact Exec.assign (eval_add (eval_reg hbase hbword)
      (eval_mul (eval_const hw) (eval_reg hf hfword) hmulword) (hleft ▸ hlw))
  let s₁ := s₀.setReg 61 right
  have he₁ : Exec w (.assign 61 (.op .add (.reg 60) (.const 1))) s₀ s₁ 4 := by
    have hv := eval_add (eval_reg (State.setReg_regs_self s 60 left) hlw) (eval_const (by omega : 1 < 2 ^ w)) (hright ▸ hrw)
    simpa only [← hright, s₁, s₀, Expr.cost] using (Exec.assign (r := 61) hv)
  obtain ⟨s₂, t₂, he₂, ht₂, hbuf₂, hpos₂, ha₂, hr₂⟩ := bufPush2_exec (s := s₁) 26 75 60 61 pre rem left right
    hw hposw hlw hrw hbuf (by simpa [s₁, s₀] using hpos)
    (by simp [s₁, s₀]) (State.setReg_regs_self ..)
  let s₃ := s₂.setReg 76 (m + 1)
  have he₃ : Exec w (.assign 76 (.op .add (.reg 76) (.const 1))) s₂ s₃ 4 :=
    .assign (eval_add (eval_reg ((hr₂ 76 (by decide)).trans (by simpa [s₁, s₀] using hcount)) (by omega))
      (eval_const (by omega)) hcountw)
  refine ⟨s₃, 6 + (4 + (t₂ + 4)), .seq he₀ (.seq he₁ (.seq he₂ he₃)), by omega,
    hbuf₂, ?_, State.setReg_regs_self .., ha₂, ?_⟩
  · exact (State.setReg_regs_ne s₂ (m + 1) (by decide : (75 : Reg) ≠ 76)).trans hpos₂
  · intro r hr60 hr61 hr75 hr76
    exact (State.setReg_regs_ne s₂ (m + 1) hr76).trans
      ((hr₂ r hr75).trans ((State.setReg_regs_ne s₀ right hr61).trans (State.setReg_regs_ne s left hr60)))

end GraphMinor.Compute
