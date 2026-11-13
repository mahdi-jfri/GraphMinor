module

public import GraphMinor.Compute.GM02ChoiceIncidenceExpr
import GraphMinor.Compute.CrossingOpsBasic

/-!
# A bounds-checked incident-edge choice command

Candidate digits include a sentinel equal to the host edge count.
Reject that sentinel before reading any host endpoints. For a genuine
position, read its two endpoints and run the active incidence test. The
command therefore also handles a host with no edges.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Save the incidence bit in register 46, guarding all chosen-edge reads. -/
@[expose] def gm02CheckChoiceProg (src : Arr) : Cmd :=
  .ite (.op .lt (.reg 32) (.reg 11))
    (.seq (gm02ReadHostEndsProg src) (.assign 46 gm02ChoiceIncidenceExpr))
    (.assign 46 (.const 0))

/-- A checked choice returns actual active incidence in constant time, including the sentinel case. -/
theorem gm02CheckChoiceProg_exec {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (src : Arr) (flags : List ℕ) (e v : ℕ)
    (hsrc : s.arrs src = x.enc) (hflags : s.arrs 20 = flags)
    (hlen : flags.length = x.G.edges.length) (hbits : ∀ b ∈ flags, b ≤ 1)
    (he : s.regs 32 = e) (hm : s.regs 11 = x.G.edges.length) (hv : s.regs 45 = v)
    (hw : 2 < 2 ^ w) (hn : x.G.n < 2 ^ w) (hmw : x.G.edges.length < 2 ^ w)
    (hew : e < 2 ^ w) (hvw : v < 2 ^ w) (henc : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02CheckChoiceProg src) s s' t ∧ t ≤ 36 ∧
      s'.regs 46 = (if (gm02ActiveGraph x.G.graph flags).Inc e v then 1 else 0) ∧
      s'.arrs = s.arrs ∧
      (∀ r, r ≠ 42 → r ≠ 44 → r ≠ 46 → s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hguard := eval_lt (eval_reg he hew) (eval_reg hm hmw) hw1
  by_cases hem : e < x.G.edges.length
  · let i : Fin x.G.edges.length := ⟨e, hem⟩
    obtain ⟨s₁, he₁, ha, hb, harr, hr⟩ :=
      gm02ReadHostEndsProg_exec x s src i hsrc he hw hn henc
    have heval := gm02ChoiceIncidenceExpr_eval x s₁ flags i v
      ((congrFun harr 20).trans hflags) hlen hbits
      ((hr 32 (by decide) (by decide)).trans he) ha hb
      ((hr 45 (by decide) (by decide)).trans hv) hw1 hn hvw hew
    let bit := if (gm02ActiveGraph x.G.graph flags).Inc e v then 1 else 0
    let s₂ := s₁.setReg 46 bit
    have he₂ : Exec w (.assign 46 gm02ChoiceIncidenceExpr) s₁ s₂ 19 := by
      exact Exec.assign heval
    have hg : (Expr.op .lt (.reg 32) (.reg 11)).eval w s = some 1 := by
      simpa only [hem, ↓reduceIte] using hguard
    refine ⟨s₂, 36, .ite_true hg (by decide) (.seq he₁ he₂), le_rfl, ?_, harr, ?_⟩
    · exact State.setReg_regs_self ..
    · intro r hr42 hr44 hr46
      exact (State.setReg_regs_ne s₁ bit hr46).trans (hr r hr42 hr44)
  · have hnot := gm02ActiveGraph_not_inc_of_length_le x.G flags (v := v) (Nat.le_of_not_gt hem)
    let s₁ := s.setReg 46 0
    have he₁ : Exec w (.assign 46 (.const 0)) s s₁ 2 :=
      .assign (eval_const (by omega))
    have hg : (Expr.op .lt (.reg 32) (.reg 11)).eval w s = some 0 := by
      simpa only [hem, ↓reduceIte] using hguard
    refine ⟨s₁, 5, .ite_false hg he₁, by decide, ?_, rfl, ?_⟩
    · simp only [s₁, State.setReg_regs_self, hnot, ite_false]
    · intro r _ _ hr46
      exact State.setReg_regs_ne s 0 hr46

end GraphMinor.Compute
