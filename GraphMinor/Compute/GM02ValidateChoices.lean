module

public import GraphMinor.Compute.GM02ChoiceScanBody
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The complete candidate choice validator

Start with a true accumulated bit and scan the supplied pattern edge
positions. Each step adds just the next active edge's conditions.
Induction through the counting loop identifies the final bit with the
whole assignment validity predicate. The scan is linear in the supplied
pattern edge count and retains every array.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Validate the decoded candidate array against all active pattern edges. -/
@[expose] def gm02ValidateChoicesProg (src : Arr) : Cmd :=
  .seq (.assign 43 (.const 0))
    (.seq (.assign 51 (.const 1)) (forUp 43 (.reg 15) (gm02ChoiceScanBody src)))

/-- The full scan returns the exact split-choice validity bit with a linear step bound. -/
theorem gm02ValidateChoicesProg_exec {w K code : ℕ} (x : GM02TopologicalInput)
    (s : State) (src : Arr) (gflags hflags : List ℕ)
    (hK : x.edges.length ≤ K) (hsrc : s.arrs src = x.enc)
    (harr : s.arrs 23 = List.ofFn (fun i : Fin (2 * K) => gm02SeparatorDigit x.G.edges.length code i.val))
    (hG : s.arrs 20 = gflags) (hGlen : gflags.length = x.G.edges.length)
    (hGbits : ∀ b ∈ gflags, b ≤ 1) (hH : s.arrs 21 = hflags)
    (hHlen : hflags.length = x.edges.length) (hHbits : ∀ b ∈ hflags, b ≤ 1)
    (hoff : s.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card)
    (hm : s.regs 11 = x.G.edges.length) (hk : s.regs 15 = x.edges.length)
    (hw : 2 < 2 ^ w) (hn : x.G.n < 2 ^ w) (hKw : 2 * K < 2 ^ w)
    (hmw : x.G.edges.length + 1 < 2 ^ w) (henc : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02ValidateChoicesProg src) s s' t ∧
      t ≤ 139 * x.edges.length + 7 ∧
      s'.regs 51 = (if gm02PortAssignmentValid x gflags hflags
        (gm02PortAssignmentOfCode x code) then 1 else 0) ∧
      s'.regs 43 = x.edges.length ∧ s'.arrs = s.arrs ∧
      (∀ r, r ≠ 32 → (r < 42 ∨ 51 < r) → s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hmw' : x.edges.length < 2 ^ w := by omega
  let s₀ := s.setReg 43 0
  let s₁ := s₀.setReg 51 1
  have he₀ : Exec w (.assign 43 (.const 0)) s s₀ 2 := .assign (eval_const (by omega))
  have he₁ : Exec w (.assign 51 (.const 1)) s₀ s₁ 2 := .assign (eval_const hw1)
  let I : ℕ → State → Prop := fun j st => st.regs 43 = j ∧
    st.regs 51 = (if gm02PortAssignmentPrefixValid x gflags hflags
      (gm02PortAssignmentOfCode x code) j then 1 else 0) ∧
    st.arrs = s.arrs ∧
    (∀ r, r ≠ 32 → (r < 42 ∨ 51 < r) → st.regs r = s.regs r)
  have hI : I 0 s₁ := by
    refine ⟨by simp [s₁, s₀], ?_, rfl, ?_⟩
    · rw [ite_eq_left (gm02PortAssignmentPrefixValid_zero x gflags hflags (gm02PortAssignmentOfCode x code))]
      exact State.setReg_regs_self ..
    · intro r hr32 hrange
      have hr43 : r ≠ 43 := by dsimp only [Reg] at *; omega
      have hr51 : r ≠ 51 := by dsimp only [Reg] at *; omega
      exact (State.setReg_regs_ne s₀ 1 hr51).trans (State.setReg_regs_ne s 0 hr43)
  obtain ⟨s₂, t₂, he₂, ht₂, hI₂⟩ := forUp_exec' I x.edges.length 132
    (r_i := 43) (hi := .reg 15) (body := gm02ChoiceScanBody src) hw1 hmw'
    (fun j hj st hst => ⟨hst.1, eval_reg
      ((hst.2.2.2 15 (by decide) (Or.inl (by decide))).trans hk) hmw'⟩)
    (fun j hj st hst => by
      obtain ⟨st', t, he, ht, hvalid, hcounter, ha, hr⟩ :=
        gm02ChoiceScanBody_exec x st src gflags hflags ⟨j, hj⟩ hK
          ((congrFun hst.2.2.1 src).trans hsrc)
          ((congrFun hst.2.2.1 23).trans harr)
          ((congrFun hst.2.2.1 20).trans hG) hGlen hGbits
          ((congrFun hst.2.2.1 21).trans hH) hHlen hHbits hst.1 hst.2.1
          ((hst.2.2.2 16 (by decide) (Or.inl (by decide))).trans hoff)
          ((hst.2.2.2 11 (by decide) (Or.inl (by decide))).trans hm)
          hw hn hKw hmw henc
      refine ⟨st', t, he, ht, ?_, hcounter.trans hst.1⟩
      refine ⟨State.setReg_regs_self .., ?_, ha.trans hst.2.2.1, ?_⟩
      · exact (State.setReg_regs_ne st' (j + 1) (by decide : (51 : Reg) ≠ 43)).trans hvalid
      · intro r hr32 hrange
        have hr43 : r ≠ 43 := by dsimp only [Reg] at *; omega
        exact (State.setReg_regs_ne st' (j + 1) hr43).trans
          ((hr r hr32 hrange).trans (hst.2.2.2 r hr32 hrange))) s₁ hI
  refine ⟨s₂, 2 + (2 + t₂), .seq he₀ (.seq he₁ he₂), ?_, ?_, hI₂.1, hI₂.2.2.1, hI₂.2.2.2⟩
  · change t₂ ≤ 3 + x.edges.length * 139 at ht₂
    omega
  · simpa only [gm02PortAssignmentPrefixValid_full] using hI₂.2.1

end GraphMinor.Compute
