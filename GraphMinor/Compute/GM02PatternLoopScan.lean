module

public import GraphMinor.Compute.GM02PatternLoopBody
public import GraphMinor.Compute.GM02PatternLoopScanResult
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The complete matching-loop scan

Initialize the answer to the pattern edge count, then scan the supplied
positions from last to first. The body implements the suffix-search
recurrence. A counting-loop invariant proves that the saved answer is
the first matching loop, or the edge-count sentinel when none exists.
The running time is linear in the number of supplied pattern edges.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Scan all actual pattern edges for a loop at the branch vertex in register 42. -/
def gm02PatternLoopScanProg (src : Arr) : Cmd :=
  .seq (.assign 40 (.const 0)) (.seq (.assign 41 (.reg 15))
    (forUp 40 (.reg 15) (gm02PatternLoopBody src)))

/-- The actual matching-loop scan computes the finite search result in at most `41m + 7` steps. -/
theorem gm02PatternLoopScanProg_exec {w : ℕ} (x : GM02TopologicalInput) (s : State) (src : Arr)
    (flags : List ℕ) (v : ℕ)
    (hsrc : s.arrs src = x.enc) (hflags : s.arrs 21 = flags)
    (hFlen : flags.length = x.edges.length) (hbits : ∀ b ∈ flags, b ≤ 1)
    (hM : s.regs 15 = x.edges.length)
    (hoff : s.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card) (hv : s.regs 42 = v)
    (hw : 2 < 2 ^ w) (hn : x.G.n < 2 ^ w) (hvw : v < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02PatternLoopScanProg src) s s' t ∧ t ≤ 41 * x.edges.length + 7 ∧
      s'.regs 40 = x.edges.length ∧
      s'.regs 41 = ((gm02FindPatternLoop x flags v).map Fin.val).getD x.edges.length ∧
      s'.arrs = s.arrs ∧
      (∀ r, r ≠ 40 → r ≠ 41 → r ≠ 43 → s'.regs r = s.regs r) := by
  have hLen := x.enc_length
  have hMw : x.edges.length < 2 ^ w := by omega
  have hw₁ : 1 < 2 ^ w := by omega
  let s₁ := s.setReg 40 0
  have he₁ : Exec w (.assign 40 (.const 0)) s s₁ 2 := .assign (eval_const (Nat.two_pow_pos w))
  let s₂ := s₁.setReg 41 x.edges.length
  have he₂ : Exec w (.assign 41 (.reg 15)) s₁ s₂ 2 :=
    .assign (eval_reg (by simpa [s₁, State.setReg] using hM) hMw)
  let I : ℕ → State → Prop := fun j st =>
    st.regs 40 = j ∧ st.regs 41 = gm02PatternLoopScanResult x flags v j ∧
    st.arrs = s.arrs ∧ (∀ r, r ≠ 40 → r ≠ 41 → r ≠ 43 → st.regs r = s.regs r)
  have hI₀ : I 0 s₂ := by
    refine ⟨by simp [s₂, s₁], ?_, rfl, ?_⟩
    · rw [gm02PatternLoopScanResult_zero]
      exact State.setReg_regs_self _ _ _
    · intro r hr40 hr41 _
      simp only [s₂, s₁, State.setReg_regs_ne _ _ hr40, State.setReg_regs_ne _ _ hr41]
  obtain ⟨s₃, t₃, he₃, ht₃, hI₃⟩ := forUp_exec' I x.edges.length 34 (r_i := 40) (hi := .reg 15) (body := gm02PatternLoopBody src) hw₁ hMw
    (fun j hj st hI => by
      refine ⟨hI.1, ?_⟩
      apply eval_reg _ hMw
      rw [hI.2.2.2 15 (by decide) (by decide) (by decide)]
      exact hM)
    (fun j hj st hI => by
      obtain ⟨st', t, he, ht, hres, ha, hr⟩ := gm02PatternLoopBody_exec x st src flags v j hj
        (by rw [hI.2.2.1]; exact hsrc) (by rw [hI.2.2.1]; exact hflags) hFlen hbits
        (by rw [hI.2.2.2 15 (by decide) (by decide) (by decide)]; exact hM)
        (by rw [hI.2.2.2 16 (by decide) (by decide) (by decide)]; exact hoff) hI.1
        (by rw [hI.2.2.2 42 (by decide) (by decide) (by decide)]; exact hv) hw hn hvw hlen
      refine ⟨st', t, he, ht, ?_, ?_⟩
      · refine ⟨State.setReg_regs_self _ _ _, ?_, ?_, ?_⟩
        · have hc := congrArg (fun r : ℕ =>
            if gm02PatternLoopTest x flags v ⟨x.edges.length - (j + 1), by omega⟩ then
              x.edges.length - (j + 1) else r) hI.2.1
          exact (State.setReg_regs_ne st' (j + 1) (by decide : 41 ≠ 40)).trans
            (hres.trans (hc.trans (gm02PatternLoopScanResult_succ x flags v j hj).symm))
        · exact ha.trans hI.2.2.1
        · intro r hr40 hr41 hr43
          rw [State.setReg_regs_ne _ _ hr40, hr r hr41 hr43]
          exact hI.2.2.2 r hr40 hr41 hr43
      · rw [hr 40 (by decide) (by decide)]
        exact hI.1)
    s₂ hI₀
  refine ⟨s₃, 2 + (2 + t₃), .seq he₁ (.seq he₂ he₃), ?_, hI₃.1, ?_, hI₃.2.2.1, hI₃.2.2.2⟩
  · change t₃ ≤ 3 + x.edges.length * 41 at ht₃
    omega
  · exact hI₃.2.1.trans (gm02PatternLoopScanResult_full x flags v)

end GraphMinor.Compute
