module

public import GraphMinor.Compute.GM02EdgePortAdjExpr
import GraphMinor.Compute.CrossingOpsBasic
import GraphMinor.Compute.CrossingOpsReplLists

/-!
# Executing the edge-to-terminal adjacency test

Recover the host-edge position and terminal slot from their numeric
offsets. Divide the slot by two to obtain its original pattern position.
Check that position before reading its flag. An unused fixed slot is
rejected without an out-of-range read, while a supplied slot uses the
proved flag-and-digit adjacency expression.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Test a host-edge vertex in register 60 against a terminal in register 61. -/
@[expose] def gm02EdgePortAdjProg : Cmd :=
  .seq (.assign 32 (.op .sub (.reg 60) (.reg 10)))
    (.seq (.assign 62 (.op .sub (.reg 61) (.op .add (.reg 10) (.reg 11))))
      (.seq (.assign 43 (.op .div (.reg 62) (.const 2)))
        (.ite (.op .lt (.reg 43) (.reg 15))
          (.assign 63 gm02EdgePortAdjExpr) (.assign 63 (.const 0)))))

/-- The checked edge-to-terminal command returns exact numeric adjacency in at most 32 steps. -/
theorem gm02EdgePortAdjProg_exec {w K code : ℕ} (x : GM02TopologicalInput) (s : State)
    (gflags hflags : List ℕ) (e : Fin x.G.edges.length) (p : Fin (2 * K))
    (hG : s.arrs 20 = gflags) (hGlen : gflags.length = x.G.edges.length)
    (hGbits : ∀ b ∈ gflags, b ≤ 1) (hH : s.arrs 21 = hflags)
    (hHlen : hflags.length = x.edges.length) (hHbits : ∀ b ∈ hflags, b ≤ 1)
    (hslots : s.arrs 23 = List.ofFn (fun i : Fin (2 * K) => gm02SeparatorDigit x.G.edges.length code i.val))
    (he : s.regs 60 = x.G.n + e.val) (hp : s.regs 61 = x.G.n + x.G.edges.length + p.val)
    (hn : s.regs 10 = x.G.n) (hm : s.regs 11 = x.G.edges.length) (hf : s.regs 15 = x.edges.length)
    (hw : 2 < 2 ^ w) (hnw : x.G.n < 2 ^ w) (hmw : x.G.edges.length < 2 ^ w)
    (hfw : x.edges.length < 2 ^ w) (hKw : 2 * K < 2 ^ w)
    (hew : x.G.n + e.val < 2 ^ w) (hpw : x.G.n + x.G.edges.length + p.val < 2 ^ w) :
    ∃ s' t, Exec w gm02EdgePortAdjProg s s' t ∧ t ≤ 32 ∧
      s'.regs 63 = (if (gm02FullPortGraph x gflags hflags code K).Adj
        (gm02FullPortEdge x K e) (gm02FullPortTerminal x K p) then 1 else 0) ∧
      s'.arrs = s.arrs ∧
      (∀ r, r ≠ 32 → r ≠ 43 → r ≠ 62 → r ≠ 63 → s'.regs r = s.regs r) := by
  have heword : e.val < 2 ^ w := e.isLt.trans hmw
  have hpword : p.val < 2 ^ w := p.isLt.trans hKw
  have hsum : x.G.n + x.G.edges.length < 2 ^ w := by omega
  let s₀ := s.setReg 32 e.val
  have he₀ : Exec w (.assign 32 (.op .sub (.reg 60) (.reg 10))) s s₀ 4 := by
    simpa only [s₀, Expr.cost, Nat.add_sub_cancel_left] using
      (Exec.assign (r := 32) (eval_sub (eval_reg he hew) (eval_reg hn hnw)))
  let s₁ := s₀.setReg 62 p.val
  have he₁ : Exec w (.assign 62 (.op .sub (.reg 61) (.op .add (.reg 10) (.reg 11)))) s₀ s₁ 6 := by
    have hval := eval_sub
      (eval_reg ((State.setReg_regs_ne s e.val (by decide : (61 : Reg) ≠ 32)).trans hp) hpw)
      (eval_add (eval_reg ((State.setReg_regs_ne s e.val (by decide : (10 : Reg) ≠ 32)).trans hn) hnw)
        (eval_reg ((State.setReg_regs_ne s e.val (by decide : (11 : Reg) ≠ 32)).trans hm) hmw) hsum)
    simpa only [s₁, Expr.cost, Nat.add_sub_cancel_left] using (Exec.assign (r := 62) hval)
  let s₂ := s₁.setReg 43 (p.val / 2)
  have he₂ : Exec w (.assign 43 (.op .div (.reg 62) (.const 2))) s₁ s₂ 4 :=
    .assign (eval_div (eval_reg (State.setReg_regs_self ..) hpword) (eval_const hw)
      (by decide) ((Nat.div_le_self _ _).trans_lt hpword))
  have hframe (r : Reg) (hr32 : r ≠ 32) (hr43 : r ≠ 43) (hr62 : r ≠ 62) :
      s₂.regs r = s.regs r :=
    (State.setReg_regs_ne s₁ (p.val / 2) hr43).trans
      ((State.setReg_regs_ne s₀ p.val hr62).trans (State.setReg_regs_ne s e.val hr32))
  have hguard := eval_lt (eval_reg (State.setReg_regs_self s₁ 43 (p.val / 2))
    ((Nat.div_le_self _ _).trans_lt hpword))
    (eval_reg ((hframe 15 (by decide) (by decide) (by decide)).trans hf) hfw) (by omega)
  by_cases hbound : p.val / 2 < x.edges.length
  · have hval := gm02EdgePortAdjExpr_eval x s₂ gflags hflags e p hbound hG hGlen hGbits hH hHlen hHbits
      hslots (by simp [s₂, s₁, s₀]) (State.setReg_regs_self ..)
      (by simp [s₂, s₁]) (by omega) hmw hfw hKw
    let bit := if (gm02FullPortGraph x gflags hflags code K).Adj
      (gm02FullPortEdge x K e) (gm02FullPortTerminal x K p) then 1 else 0
    let s₃ := s₂.setReg 63 bit
    have he₃ : Exec w (.assign 63 gm02EdgePortAdjExpr) s₂ s₃ 15 := .assign hval
    have hg : (Expr.op .lt (.reg 43) (.reg 15)).eval w s₂ = some 1 := by
      simpa only [hbound, ↓reduceIte] using hguard
    refine ⟨s₃, 32, .seq he₀ (.seq he₁ (.seq he₂ (.ite_true hg (by decide) he₃))), le_rfl,
      State.setReg_regs_self .., rfl, ?_⟩
    intro r hr32 hr43 hr62 hr63
    exact (State.setReg_regs_ne s₂ bit hr63).trans (hframe r hr32 hr43 hr62)
  · let s₃ := s₂.setReg 63 0
    have he₃ : Exec w (.assign 63 (.const 0)) s₂ s₃ 2 := .assign (eval_const (by omega))
    have hg : (Expr.op .lt (.reg 43) (.reg 15)).eval w s₂ = some 0 := by
      simpa only [hbound, ↓reduceIte] using hguard
    refine ⟨s₃, 19, .seq he₀ (.seq he₁ (.seq he₂ (.ite_false hg he₃))), by decide, ?_, rfl, ?_⟩
    · simp only [s₃, State.setReg_regs_self, gm02FullPortGraph_edge_terminal, hbound, false_and, ite_false]
    · intro r hr32 hr43 hr62 hr63
      exact (State.setReg_regs_ne s₂ 0 hr63).trans (hframe r hr32 hr43 hr62)

end GraphMinor.Compute
