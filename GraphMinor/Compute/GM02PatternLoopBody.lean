module

public import GraphMinor.Compute.GM02PatternLoopExpr
import GraphMinor.Compute.CrossingOpsBasic

/-!
# One iteration of the descending loop search

Compute the next edge position from the fixed edge count and the
ascending loop counter. Read its active-loop bit and replace the saved
answer when it matches. The body leaves all arrays unchanged and writes
only the answer and temporary edge-position registers.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Process edge `m - 1 - j`, retaining the least matching position seen so far. -/
def gm02PatternLoopBody (src : Arr) : Cmd :=
  .seq (.assign 43 (.op .sub (.op .sub (.reg 15) (.const 1)) (.reg 40)))
    (.ite (gm02PatternLoopExpr src) (.assign 41 (.reg 43)) .skip)

/-- One actual scan iteration takes at most thirty-four steps and performs exactly its conditional answer update. -/
theorem gm02PatternLoopBody_exec {w : ℕ} (x : GM02TopologicalInput) (s : State) (src : Arr)
    (flags : List ℕ) (v j : ℕ) (hj : j < x.edges.length)
    (hsrc : s.arrs src = x.enc) (hflags : s.arrs 21 = flags)
    (hFlen : flags.length = x.edges.length) (hbits : ∀ b ∈ flags, b ≤ 1)
    (hM : s.regs 15 = x.edges.length)
    (hoff : s.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card)
    (hjreg : s.regs 40 = j) (hv : s.regs 42 = v)
    (hw : 2 < 2 ^ w) (hn : x.G.n < 2 ^ w) (hvw : v < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02PatternLoopBody src) s s' t ∧ t ≤ 34 ∧
      s'.regs 41 = (if gm02PatternLoopTest x flags v ⟨x.edges.length - (j + 1), by omega⟩ then
        x.edges.length - (j + 1) else s.regs 41) ∧
      s'.arrs = s.arrs ∧ (∀ r, r ≠ 41 → r ≠ 43 → s'.regs r = s.regs r) := by
  let f : Fin x.edges.length := ⟨x.edges.length - (j + 1), by omega⟩
  have hLen := x.enc_length
  have hMw : x.edges.length < 2 ^ w := by omega
  have hjw : j < 2 ^ w := hj.trans hMw
  have hfw : f.val < 2 ^ w := f.isLt.trans hMw
  have hw₁ : 1 < 2 ^ w := by omega
  let s₁ := s.setReg 43 f.val
  have hidx : (Expr.op .sub (.op .sub (.reg 15) (.const 1)) (.reg 40)).eval w s = some f.val := by
    have he := eval_sub (eval_sub (eval_reg hM hMw) (eval_const hw₁)) (eval_reg hjreg hjw)
    exact he.trans (congrArg some (by dsimp only [f]; omega))
  have he₁ : Exec w (.assign 43 (.op .sub (.op .sub (.reg 15) (.const 1)) (.reg 40))) s s₁ 6 := .assign hidx
  have htest := gm02PatternLoopExpr_eval x s₁ src flags f v
    (by simpa only [s₁, State.setReg_arrs] using hsrc)
    (by simpa only [s₁, State.setReg_arrs] using hflags) hFlen hbits
    (by simpa [s₁, State.setReg] using hoff) (by simp [s₁])
    (by simpa [s₁, State.setReg] using hv) hw hn hvw hlen
  cases ht : gm02PatternLoopTest x flags v f with
  | false =>
    have htest₀ : (gm02PatternLoopExpr src).eval w s₁ = some 0 := by simpa only [ht, Bool.false_eq_true, ↓reduceIte] using htest
    have he₂ : Exec w (.ite (gm02PatternLoopExpr src) (.assign 41 (.reg 43)) .skip) s₁ s₁ 27 := by
      simpa only [gm02PatternLoopExpr_cost] using Exec.ite_false htest₀ (Exec.skip s₁)
    refine ⟨s₁, 33, .seq he₁ he₂, by decide, ?_, rfl, ?_⟩
    · simpa only [ht, Bool.false_eq_true, ↓reduceIte] using (State.setReg_regs_ne s f.val (by decide : 41 ≠ 43))
    · intro r _ hr43
      exact State.setReg_regs_ne _ _ hr43
  | true =>
    have htest₁ : (gm02PatternLoopExpr src).eval w s₁ = some 1 := by simpa only [ht, ↓reduceIte] using htest
    let s₂ := s₁.setReg 41 f.val
    have he₂ : Exec w (.ite (gm02PatternLoopExpr src) (.assign 41 (.reg 43)) .skip) s₁ s₂ 28 := by
      simpa only [gm02PatternLoopExpr_cost, Expr.cost] using
        Exec.ite_true htest₁ (by decide : 1 ≠ 0) (Exec.assign (eval_reg (by simp [s₁]) hfw))
    refine ⟨s₂, 34, .seq he₁ he₂, le_rfl, ?_, rfl, ?_⟩
    · simpa only [ht, ↓reduceIte] using (State.setReg_regs_self s₁ 41 f.val)
    · intro r hr41 hr43
      simp only [s₂, s₁, State.setReg_regs_ne _ _ hr41, State.setReg_regs_ne _ _ hr43]

end GraphMinor.Compute
