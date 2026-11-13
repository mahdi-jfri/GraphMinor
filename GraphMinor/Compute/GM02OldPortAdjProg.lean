module

public import GraphMinor.Compute.GM02OldPortAdjExpr
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Executing the old-to-edge split adjacency test

For an old vertex and an edge vertex, subtract the host vertex offset
to recover the supplied edge position. Run its bounds-checked incidence
test and combine the result with the branch mask. The output bit in
register 63 is exactly the numeric graph's adjacency at this pair.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Test an old vertex in register 60 against a host-edge vertex in register 61. -/
@[expose] def gm02OldPortAdjProg (src : Arr) : Cmd :=
  .seq (.assign 32 (.op .sub (.reg 61) (.reg 10)))
    (.seq (.assign 45 (.reg 60))
      (.seq (gm02CheckChoiceProg src) (.assign 63 gm02OldPortAdjExpr)))

/-- The old-to-edge adjacency command computes the correct bit in at most 49 steps. -/
theorem gm02OldPortAdjProg_exec {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (src : Arr) (gflags hflags : List ℕ) (code K : ℕ)
    (a : Fin x.G.n) (e : Fin x.G.edges.length)
    (hsrc : s.arrs src = x.enc) (hGarr : s.arrs 20 = gflags)
    (hlen : gflags.length = x.G.edges.length) (hbits : ∀ b ∈ gflags, b ≤ 1)
    (hmask : s.arrs 22 = bitSetList x.vertices)
    (ha : s.regs 60 = a.val) (he : s.regs 61 = x.G.n + e.val)
    (hn : s.regs 10 = x.G.n) (hm : s.regs 11 = x.G.edges.length)
    (hw : 2 < 2 ^ w) (hnw : x.G.n < 2 ^ w) (hmw : x.G.edges.length < 2 ^ w)
    (hvew : x.G.n + e.val < 2 ^ w) (henc : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02OldPortAdjProg src) s s' t ∧ t ≤ 49 ∧
      s'.regs 63 = (if (gm02FullPortGraph x gflags hflags code K).Adj
        (gm02FullPortOld x K a) (gm02FullPortEdge x K e) then 1 else 0) ∧
      s'.arrs = s.arrs ∧
      (∀ r, r ≠ 32 → r ≠ 42 → r ≠ 44 → r ≠ 45 → r ≠ 46 → r ≠ 63 → s'.regs r = s.regs r) := by
  have hew : e.val < 2 ^ w := e.isLt.trans hmw
  have haw : a.val < 2 ^ w := a.isLt.trans hnw
  let s₀ := s.setReg 32 e.val
  have he₀ : Exec w (.assign 32 (.op .sub (.reg 61) (.reg 10))) s s₀ 4 := by
    have hval := eval_sub (eval_reg he hvew) (eval_reg hn hnw)
    simpa only [s₀, Expr.cost, Nat.add_sub_cancel_left] using (Exec.assign (r := 32) hval)
  let s₁ := s₀.setReg 45 a.val
  have he₁ : Exec w (.assign 45 (.reg 60)) s₀ s₁ 2 :=
    .assign (eval_reg ((State.setReg_regs_ne s e.val (by decide : (60 : Reg) ≠ 32)).trans ha) haw)
  obtain ⟨s₂, t₂, he₂, ht₂, hinc, ha₂, hr₂⟩ :=
    gm02CheckChoiceProg_exec x s₁ src gflags e.val a.val hsrc hGarr hlen hbits
      (by simp [s₁, s₀]) (by simpa [s₁, s₀] using hm) (State.setReg_regs_self ..)
      hw hnw hmw hew haw henc
  have ha60 : s₂.regs 60 = a.val :=
    (hr₂ 60 (by decide) (by decide) (by decide)).trans (by simpa [s₁, s₀] using ha)
  have heval := gm02OldPortAdjExpr_eval x s₂ gflags hflags code K a e
    ((congrFun ha₂ 22).trans hmask) ha60 hinc (by omega) hnw
  let bit := if (gm02FullPortGraph x gflags hflags code K).Adj
    (gm02FullPortOld x K a) (gm02FullPortEdge x K e) then 1 else 0
  let s₃ := s₂.setReg 63 bit
  have he₃ : Exec w (.assign 63 gm02OldPortAdjExpr) s₂ s₃ 7 := .assign heval
  refine ⟨s₃, 4 + (2 + (t₂ + 7)), .seq he₀ (.seq he₁ (.seq he₂ he₃)), by omega,
    State.setReg_regs_self .., ha₂, ?_⟩
  intro r hr32 hr42 hr44 hr45 hr46 hr63
  exact (State.setReg_regs_ne s₂ bit hr63).trans
    ((hr₂ r hr42 hr44 hr46).trans
      ((State.setReg_regs_ne s₀ a.val hr45).trans (State.setReg_regs_ne s e.val hr32)))

end GraphMinor.Compute
